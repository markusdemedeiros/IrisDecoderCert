import Kraken.SepCells
import Kraken.SeparationTactics

/-!
# Stepping memory accesses through a tree of cells, without `grind`

`grind_cells` finds the cell of every access by E-matching (`FindAt` demands
walking the tree, `Split` facts climbing back), one round per tree node. On a
frame of a few dozen cells that is hundreds of thousands of heartbeats per
block. The accesses of straight-line code are at addresses that are, after
the block's address normalization, *syntactically* the base of a cell, so the
search needs no theory reasoning at all. This file does it by a direct walk:

* `sep_mem h` — `h : m =⋆ H` is a memory fact. Every `Mem.storeInt m a n v`
  of the goal over `m` (innermost first) is replaced in `h` by the fact about
  the stored memory (`Block.storeInt_val`, `Val.storeInt`: the stored cell
  moves to the front of the tree); then a goal `(loadInt m' a n).isSome =
  true` is closed (`Block.loadInt_isSome_here`, `Val.loadInt_isSome`), and a
  load of a known cell in the goal is rewritten to its value (`Val.loadInt`).
* `sep_close h` — the goal is `m =⋆ G` for `h : m =⋆ H`: the cells of `G`
  that are `n ?@ a` where `H` holds `bs =@ a` are forgotten in `h`
  (`Val.forget_len`), and the two trees are then equal up to AC
  (`solveSepEq`, as `ecancel`).

A cell is found by its base address up to syntactic equality (after
instantiating metavariables), falling back to reducible defeq; its size must
match the access width.
-/

open Std.ExtHashMap

namespace Mem

/-- A tree that is one predicate splits with the empty rest. -/
theorem Split.single {w : Nat} (P : Mem w → Prop) : Split P emp P := (sep_emp _).symm

/-- The last predicate of a two-node tree. -/
theorem Split.last {w : Nat} (Q S : Mem w → Prop) : Split S Q (Q ⋆ S) := sep_comm _ _

/-- Loading an unknown cell whole succeeds. -/
theorem Block.loadInt_isSome_here {w : Nat} {H R : Mem w → Prop} {m : Mem w}
    {a : BitVec w} {n : Nat} (h : m =⋆ H) (hs : Split (n ?@ a) R H) :
    (m.loadInt a n).isSome = true :=
  Block.loadInt_isSome_split h hs (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- Loading a known cell whole succeeds. -/
theorem Val.loadInt_isSome {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ a) R H)
    (hlen : bs.length = n) (hw : n ≤ 2 ^ w) : (m.loadInt a n).isSome = true := by
  rw [Val.loadInt h hs hlen hw]; rfl

/-- Forgetting a known cell's contents, at a given size. -/
theorem Val.forget_len {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ a) R H)
    (hlen : bs.length = n) (hw : n ≤ 2 ^ w) : m =⋆ n ?@ a ⋆ R := by
  subst hlen; exact Val.forget h hs hw

/-- An access of `n ≤ len` bytes at a block's base is inside it. -/
theorem Block.inside_base {w : Nat} (a : BitVec w) {n len : Nat} (h : n ≤ len) :
    (a - a).toNat + n ≤ len := by
  rw [BitVec.sub_self, BitVec.toNat_zero]; omega

/-- An access inside a listed block is inside the list. -/
theorem Blocks.Inside.of_mem {w : Nat} {addr b : BitVec w} {n len : Nat} :
    ∀ {bs : List (BitVec w × Nat)}, (b, len) ∈ bs → (addr - b).toNat + n ≤ len →
      Blocks.Inside addr n bs
  | [], hm, _ => by cases hm
  | (a, l) :: bs, hm, h => by
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact Or.inl h
    · exact Or.inr (Blocks.Inside.of_mem hm h)

/-- A load inside one of the blocks of an atom `Blocks bs` of the tree. -/
theorem Blocks.loadInt_isSome_split {w : Nat} {bs : List (BitVec w × Nat)} {H R : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat} (h : m =⋆ H) (hs : Split (Blocks bs) R H)
    (hin : Blocks.Inside addr n bs) : (m.loadInt addr n).isSome = true := by
  rw [hs] at h; exact Blocks.loadInt_isSome h hin

/-- A store inside one of the blocks of an atom `Blocks bs` keeps the tree. -/
theorem Blocks.storeInt_split {w : Nat} {bs : List (BitVec w × Nat)} {H R : Mem w → Prop}
    {m : Mem w} {addr : BitVec w} {n : Nat} (h : m =⋆ H) (hs : Split (Blocks bs) R H)
    (hin : Blocks.Inside addr n bs) (v : Int) : m.storeInt addr n v =⋆ H := by
  rw [hs] at h ⊢; exact Blocks.storeInt h hin v

/-- Side goals of an access off a region's base: the offset from the base. -/
theorem sub_base_add {w : Nat} (b x : BitVec w) : b + x - b = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem sub_base_add_add {w : Nat} (b c x : BitVec w) : b + c + x - b = c + x := by
  rw [BitVec.add_assoc, sub_base_add]

/-- An access inside an unknown cell, off its base. -/
theorem Block.inside_off {w : Nat} {a addr : BitVec w} {n len : Nat}
    (h : (addr - a).toNat + n ≤ len) : (addr - a).toNat + n ≤ len := h

/-- A load inside a known cell, off its base: the bytes there. -/
theorem Val.loadInt_slice_split {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a b : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ b) R H)
    (hin : (a - b).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    m.loadInt a n = some (Int.ofBytes ((bs.drop (a - b).toNat).take n)) := by
  rw [hs] at h; exact Mem.loadInt_slice h hin hw

theorem Val.loadInt_isSome_slice {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a b : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ b) R H)
    (hin : (a - b).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    (m.loadInt a n).isSome = true := by
  rw [Val.loadInt_slice_split h hs hin hw]; rfl

/-- A store inside a known cell, off its base: the cell's bytes there replaced. -/
theorem Val.storeInt_slice_split {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a b : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ b) R H)
    (hin : (a - b).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) (v : Int) :
    m.storeInt a n v =⋆
      (bs.take (a - b).toNat ++ Int.toBytes n v ++ bs.drop ((a - b).toNat + n)) =@ b ⋆ R := by
  rw [hs] at h; exact Mem.storeInt_slice h hin hw v

/-- Two adjacent known cells are one (`rw [← Val.append_eq …]` merges, for a store across
both; `rw [Val.append_eq …]` splits back). -/
theorem Val.append_eq {w : Nat} (bs1 bs2 : List UInt8) (a b : BitVec w)
    (hb : b = a + BitVec.ofNat w bs1.length) (hw : bs1.length + bs2.length ≤ 2 ^ w) :
    (bs1 ++ bs2) =@ a = bs1 =@ a ⋆ bs2 =@ b := by
  subst hb; rw [Val.eq, Val.eq, Val.eq, Mem.At_append_sep _ _ _ hw]

/-- Side goals of an access at a literal offset from a cell at another literal offset of the
same root. -/
theorem sub_add_add_lit {w : Nat} (r x y : BitVec w) : r + x - (r + y) = x - y := by
  have h : r + x = (x - y) + (r + y) := by
    rw [BitVec.add_comm r y, ← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.add_comm]
  rw [h, BitVec.add_sub_cancel]

/-- A store of `n` bytes at the base of an unknown `n + k`-byte cell: the cell splits into the
stored bytes and the unknown rest (`sep_mem.splitNarrow`). -/
theorem Block.storeInt_val_split {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {n k len : Nat} (h : m =⋆ H) (hs : Split (len ?@ a) R H) (hn : n + k = len)
    (hw : len ≤ 2 ^ w) (v : Int) :
    m.storeInt a n v =⋆ (Int.toBytes n v) =@ a ⋆ (k ?@ (a + .ofNat w n) ⋆ R) := by
  rw [hs, ← hn, Block.split a n k (by omega), Std.ExtHashMap.sep_assoc] at h
  exact Block.storeInt_val h (Split.here _ _) v

/-! ### Accesses at a symbolic offset (an indexed cell: `base + c*j + …`)

The side goal `(a - b).toNat + n ≤ len` is reduced to a `%`-free `Nat` goal `B + n ≤ len`,
`B` an upper bound of the offset built structurally (`toNat_*_le`); `omega` then only sees
the bound facts of the index atoms. -/

theorem sub_eq_of_eq_add {w : Nat} {a b x : BitVec w} (h : a = b + x) : a - b = x := by
  rw [h, BitVec.add_comm, BitVec.add_sub_cancel]

theorem toNat_add_le {w : Nat} (x y : BitVec w) : (x + y).toNat ≤ x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_le _ _

theorem toNat_mul_le {w : Nat} (x y : BitVec w) : (x * y).toNat ≤ x.toNat * y.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_le _ _

theorem toNat_ofNat_le (w j : Nat) : (BitVec.ofNat w j).toNat ≤ j := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _

theorem toNat_setWidth_le {v w : Nat} (x : BitVec w) : (BitVec.setWidth v x).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

theorem toNat_shiftLeft_le {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k).toNat ≤ x.toNat * 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; exact Nat.mod_le _ _

theorem inside_of_bound {w : Nat} {a b x : BitVec w} {n len B : Nat} (hx : a - b = x)
    (hB : x.toNat ≤ B) (h : B + n ≤ len) : (a - b).toNat + n ≤ len := by
  rw [hx]; omega


end Mem

namespace Kraken.Tactic.SepStep

open Lean Meta Elab Tactic Kraken.Tactic

register_option sep_mem.splitNarrow : Bool := {
  defValue := false
  descr := "sep_mem: a store narrower than an unknown cell, at its base, splits the cell into the stored bytes and the unknown rest (default: the cell stays whole and unknown)"
}

register_option kraken.sepFast : Bool := {
  defValue := true
  descr := "sep_*: build `Split` proofs by explicit applications, and memoise address comparisons and tree normalisation within a command (same proofs, fewer heartbeats)"
}

register_option kraken.sepFast.check : Bool := {
  defValue := false
  descr := "kraken.sepFast: also run the old search (mkAppM Split proofs, uncached sameAddr / normTree) and report every difference as `[kraken.sepFast.diff]` (trace class and stdout)"
}

register_option kraken.sepFast.key : String := {
  defValue := ""
  descr := "internal: the cache key of the current `sep_*` call (set by `withSepKey`)"
}

initialize registerTraceClass `kraken.sepFast.diff

/-- Report a difference between the `kraken.sepFast` path and the old one (stdout as well as the
trace: a trace inside a failing `try` is backtracked away). -/
def sepFastDiff (msg : MessageData) : MetaM Unit := do
  trace[kraken.sepFast.diff] msg
  IO.println s!"[kraken.sepFast.diff] {← msg.toString}"

/-- Run a `kraken.sepFast.check` comparison off the books: without a heartbeat limit, and its
heartbeats are not charged to the declaration (the check must not change what elaborates). -/
def sepUncounted {α : Type} (x : MetaM α) : MetaM α := do
  let h0 ← IO.getNumHeartbeats
  try withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) x
  finally IO.setNumHeartbeats h0

/-- A cache of `kraken.sepFast`, one table per command. The table key is the option
`kraken.sepFast.key` (`file:declaration:initHeartbeats`), set by the `sep_*` tactics for the
duration of one call (`withSepKey`); without it nothing is cached. Commands may elaborate in
parallel, so a few tables are kept (at most `sepCacheMax`). -/
abbrev SepCache (κ ν : Type) [BEq κ] [Hashable κ] := IO.Ref (Std.HashMap String (Std.HashMap κ ν))

def sepCacheMax : Nat := 16

/-- `sameAddr` answers and `normTree` results. Only terms without metavariables and without
let-bound free variables are cached: a reducible-defeq answer on such terms depends on the
environment alone, not on the local context or the metavariable context. -/
initialize sameAddrCache : SepCache (Expr × Expr) Bool ← IO.mkRef {}
initialize normTreeCache : SepCache Expr Expr ← IO.mkRef {}

/-- The current command's cache key, if a `sep_*` tactic set one. -/
def sepCacheKey? : CoreM (Option String) := do
  let k := kraken.sepFast.key.get (← getOptions)
  return if k.isEmpty then none else some k

/-- Run a `sep_*` tactic with the cache key of the current command. -/
def withSepKey {α : Type} (x : TacticM α) : TacticM α := do
  unless kraken.sepFast.get (← getOptions) do return ← x
  let decl := (← Term.getDeclName?).getD .anonymous
  let key := s!"{← getFileName}:{decl}:{(← readThe Core.Context).initHeartbeats}"
  withTheReader Core.Context (fun c => { c with options := kraken.sepFast.key.set c.options key }) x

/-- Look `k` up in the current command's table. -/
def sepCacheGet? {κ ν : Type} [BEq κ] [Hashable κ] (ref : SepCache κ ν) (k : κ) :
    CoreM (Option ν) := do
  let some key ← sepCacheKey? | return none
  return (← ref.get)[key]? >>= (·[k]?)

/-- Store `k ↦ v` in the current command's table. -/
def sepCacheSet {κ ν : Type} [BEq κ] [Hashable κ] (ref : SepCache κ ν) (k : κ) (v : ν) :
    CoreM Unit := do
  let some key ← sepCacheKey? | return
  ref.modify fun t =>
    let t := if t.contains key || t.size < sepCacheMax then t else {}
    let inner := t.getD key {}
    -- erase first, so that `inner` is unshared and updated in place
    let t := t.erase key
    t.insert key (inner.insert k v)

/-- `e` is cacheable: no metavariables, no let-bound free variables. -/
def sepCacheable (e : Expr) : MetaM Bool := do
  if e.hasMVar then return false
  if !e.hasFVar then return true
  let lctx ← getLCtx
  return (e.find? fun t => t.isFVar && (lctx.find? t.fvarId!).all (·.isLet)).isNone

private def isSep (e : Expr) : Bool := e.getAppFn.constName? == some ``Std.ExtHashMap.sep

/-- The two sides of a `⋆` node (the predicate, not applied to a memory). -/
private def sepArgs (e : Expr) : Expr × Expr :=
  let args := e.getAppArgs
  (args[args.size - 2]!, args[args.size - 1]!)

private def mkSepLike (node l r : Expr) : Expr :=
  let args := node.getAppArgs
  mkAppN node.getAppFn (args.extract 0 (args.size - 2) ++ #[l, r])

/-- `findSplit` for a tree over `Mem w`, the `Split` proofs built by explicit applications
(the terms `mkAppM` builds, without its unification at every level of the tree). -/
partial def findSplitW (w : Expr) (pred : Expr → MetaM Bool) (H : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  if isSep H then
    let (Q, S) := sepArgs H
    if isSep Q then
      if let some (P, R, h) ← findSplitW w pred Q then
        return some (P, mkSepLike H R S, mkApp6 (mkConst ``Mem.Split.left) w P R Q h S)
    else if ← pred Q then
      return some (Q, S, mkApp3 (mkConst ``Mem.Split.here) w Q S)
    if isSep S then
      if let some (P, R, h) ← findSplitW w pred S then
        return some (P, mkSepLike H Q R, mkApp6 (mkConst ``Mem.Split.right) w P R S h Q)
    else if ← pred S then
      return some (S, Q, mkApp3 (mkConst ``Mem.Split.last) w Q S)
    return none
  else if ← pred H then
    return some (H, ← mkAppOptM ``Std.ExtHashMap.emp #[], ← mkAppM ``Mem.Split.single #[H])
  return none

/-- The width `w` of a predicate `H : Mem w → Prop`. -/
def predWidth? (H : Expr) : MetaM (Option Expr) := do
  let .forallE _ d _ _ ← whnfR (← inferType H) | return none
  let d ← whnfR d
  unless d.isAppOf ``Std.ExtHashMap && d.getAppNumArgs ≥ 1 do return none
  let k ← whnfR d.getAppArgs[0]!
  unless k.isAppOfArity ``BitVec 1 do return none
  return some k.appArg!

/-- Walk the tree `H` to the first atom satisfying `pred`: returns the atom
`P`, the rest `R`, and a proof of `Split P R H`. -/
partial def findSplitOld (pred : Expr → MetaM Bool) (H : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  if isSep H then
    let (Q, S) := sepArgs H
    if isSep Q then
      if let some (P, R, h) ← findSplitOld pred Q then
        return some (P, mkSepLike H R S, ← mkAppM ``Mem.Split.left #[h, S])
    else if ← pred Q then
      return some (Q, S, ← mkAppM ``Mem.Split.here #[Q, S])
    if isSep S then
      if let some (P, R, h) ← findSplitOld pred S then
        return some (P, mkSepLike H Q R, ← mkAppM ``Mem.Split.right #[h, Q])
    else if ← pred S then
      return some (S, Q, ← mkAppM ``Mem.Split.last #[Q, S])
    return none
  else if ← pred H then
    return some (H, ← mkAppOptM ``Std.ExtHashMap.emp #[], ← mkAppM ``Mem.Split.single #[H])
  return none

/-- The first differing subterms of two terms (along the application spines). -/
partial def firstDiff (a b : Expr) : Expr × Expr :=
  if a.isApp && b.isApp && a.getAppNumArgs == b.getAppNumArgs then
    if a.getAppFn != b.getAppFn then (a.getAppFn, b.getAppFn) else
    match (a.getAppArgs.zip b.getAppArgs).find? (fun (x, y) => x != y) with
    | some (x, y) => firstDiff x y
    | none => (a, b)
  else (a, b)

@[inherit_doc findSplitOld]
def findSplit (pred : Expr → MetaM Bool) (H : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless kraken.sepFast.get (← getOptions) && isSep H do return ← findSplitOld pred H
  let some w ← predWidth? H | findSplitOld pred H
  unless kraken.sepFast.check.get (← getOptions) do return ← findSplitW w pred H
  -- check mode: the old search first, then the new one (whose result is used; `pred` may
  -- record the atom it accepted, the new run records last)
  let old ← sepUncounted (findSplitOld pred H)
  let new ← findSplitW w pred H
  match old, new with
  | none, none => pure ()
  | some (P, R, h), some (P', R', h') =>
    if P != P' || R != R' then
      sepFastDiff m!"findSplit: old{indentExpr P}\nnew{indentExpr P'}\nin{indentExpr H}"
    else
      let h ← instantiateMVars h
      let h' ← instantiateMVars h'
      -- the spellings may differ: the new proof takes the subtrees from `H`, `mkAppM` from the
      -- lemma statements (e.g. another proof term in the `⋆` instance arguments); the two must
      -- prove the same proposition up to defeq
      if h != h' then
        unless ← sepUncounted (withNewMCtxDepth (isDefEq (← inferType h) (← inferType h'))) do
          let (a, b) := firstDiff h h'
          sepFastDiff m!"findSplit proof: same atom and rest, proof types differ at{indentExpr a}\nvs{indentExpr b}"
  | _, _ =>
    sepFastDiff m!"findSplit: old found {old.isSome}, new found {new.isSome}, in{indentExpr H}"
  return new

private def sameAddr (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a == b then return true
  unless kraken.sepFast.get (← getOptions) do
    return ← withReducible (withNewMCtxDepth (isDefEq a b))
  unless (← sepCacheable a) && (← sepCacheable b) do
    return ← withReducible (withNewMCtxDepth (isDefEq a b))
  if let some r ← sepCacheGet? sameAddrCache (a, b) then
    if kraken.sepFast.check.get (← getOptions) then
      let r' ← sepUncounted (withReducible (withNewMCtxDepth (isDefEq a b)))
      if r != r' then sepFastDiff m!"sameAddr: cached {r}, fresh {r'}:{indentExpr a}\nvs{indentExpr b}"
    return r
  let r ← withReducible (withNewMCtxDepth (isDefEq a b))
  sepCacheSet sameAddrCache (a, b) r
  return r

/-- `bs.length = n`, if it is evident: `Int.toBytes n v`, or by evaluation. -/
private def lenProof? (bs n : Expr) : MetaM (Option Expr) := do
  let bs ← instantiateMVars bs
  if bs.isAppOfArity ``Int.toBytes 2 then
    if ← isDefEq bs.appFn!.appArg! n then
      return some (← mkAppM ``Int.toBytes_length #[bs.appFn!.appArg!, bs.appArg!])
  let len ← mkAppM ``List.length #[bs]
  if ← withNewMCtxDepth (isDefEq len n) then return some (← mkEqRefl n)
  return none

/-- `n ≤ 2 ^ w` for literals. -/
private def widthProof (n w : Expr) : MetaM Expr := do
  let pow ← mkAppM ``HPow.hPow #[mkNatLit 2, w]
  mkDecideProof (← mkAppM ``LE.le #[n, pow])

/-- The memory width `w` of `m : Mem w`. -/
private def memWidth (m : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType m)
  -- `ExtHashMap (BitVec w) UInt8`
  let k := ty.getAppArgs[0]!
  let k ← whnfR k
  return k.appArg!

inductive Cell where
  | val (a bs : Expr)
  | block (a n : Expr)

private def cellOf? (e : Expr) : Option Cell :=
  if e.isAppOfArity ``Mem.Val 3 then some (.val (e.getArg! 1) (e.getArg! 2))
  else if e.isAppOfArity ``Mem.Block 3 then some (.block (e.getArg! 1) (e.getArg! 2))
  else none

/-- Find the cell at `a` of size `n` in `H`: `(cell, R, split, hlen?)`. -/
private def findCell (H a n : Expr) : MetaM (Option (Cell × Expr × Expr × Option Expr)) := do
  let found : IO.Ref (Option (Cell × Option Expr)) ← IO.mkRef none
  let pred := fun (P : Expr) => do
    match cellOf? P with
    | some (.block b len) =>
      if ← sameAddr a b then
        if ← isDefEq len n then
          found.set (some (.block b len, none)); return true
        if let (some nv, some lv) := ((← instantiateMVars n).nat?, (← instantiateMVars len).nat?) then
          if nv < lv then
            let le ← mkDecideProof (← mkAppM ``LE.le #[n, len])
            found.set (some (.block b len, some (← mkAppM ``Mem.Block.inside_base #[a, le])))
            return true
      return false
    | some (.val b bs) =>
      if ← sameAddr a b then
        if let some hl ← lenProof? bs n then
          found.set (some (.val b bs, some hl)); return true
      return false
    | none => return false
  let some (_, R, h) ← findSplit pred H | return none
  let some (c, hl) ← found.get | return none
  return some (c, R, h, hl)

/-- `b` is a left prefix of the address `a`: `a` is `b`, or `x + y` with `b` a
prefix of `x` (an index or offset added to a region's base). -/
private partial def prefixDepth (b a : Expr) : MetaM (Option Nat) := do
  if ← sameAddr a b then return some 0
  if a.isAppOfArity ``HAdd.hAdd 6 then
    return (← prefixDepth b (a.getArg! 4)).map (· + 1)
  return none

/-- An access off a region's base: a `len ?@ b` cell, or an entry `(b, len)` of a
`Blocks` atom, with `b` a prefix of `a`. Returns the lemma to apply's arguments:
`(isBlocks, R, split, inside, side goal)`; the side goal is
`(a - b).toNat + n ≤ len`. -/
private def litSplit (a : Expr) : MetaM (Expr × Option Nat) := do
  let a ← instantiateMVars a
  if a.isAppOfArity ``HAdd.hAdd 6 then
    if let some ⟨_, v⟩ ← getBitVecValue? (a.getArg! 5) then
      return (a.getArg! 4, some v.toNat)
  return (a, none)

/-- `a = root + ca`, `b = root + cb` (or `b = root`), literals `ca ≥ cb`. -/
private def litMatch (b a : Expr) : MetaM Bool := do
  let (ra, ca) ← litSplit a
  let some ca := ca | return false
  let (rb, cb) ← litSplit b
  let cb := cb.getD 0
  if cb > ca then return false
  if (← litSplit b).2.isNone then return ← sameAddr ra b
  sameAddr ra rb

/-- Reject a candidate region when the access is at a literal offset from its base that
evidently overruns it (`ca - cb + n > len`, all literals). -/
private def litOk (b a n len : Expr) : MetaM Bool := do
  let (ra, ca) ← litSplit a
  let some ca := ca | return true
  let (rb, cb) ← litSplit b
  let cb ← if cb.isSome && (← sameAddr ra rb) then pure cb.get!
    else if ← sameAddr ra b then pure 0 else return true
  let some nv := (← instantiateMVars n).nat? | return true
  let some lv := (← instantiateMVars len).nat? | return true
  return ca ≥ cb && ca - cb + nv ≤ lv

/-- `a = ((b + c₁) + …) + cₖ` with literal `cᵢ`: their sum (`none` if some added term is not a
literal, or `b` is not a prefix of `a`). -/
private partial def prefixLitOff (b a : Expr) : MetaM (Option Nat) := do
  if ← sameAddr a b then return some 0
  if a.isAppOfArity ``HAdd.hAdd 6 then
    let some ⟨_, v⟩ ← getBitVecValue? (← instantiateMVars (a.getArg! 5)) | return none
    return (← prefixLitOff b (a.getArg! 4)).map (· + v.toNat)
  return none

/-- Reject a prefix region whose literal offset evidently overruns it. -/
private def prefixFits (b a n len : Expr) : MetaM Bool := do
  let some off ← prefixLitOff b a | return true
  let some nv := (← instantiateMVars n).nat? | return true
  let some lv := (← instantiateMVars len).nat? | return true
  return off + nv ≤ lv

/-! ### Symbolic offsets

An address `rsi + (0x289ac + j)` or `rsi + (48*j + (rbx + 0x3db80))` is not syntactically a
prefix extension of its region's base `rsi + 0x289a0`, whatever the association. As a last
resort a base is matched by *atoms*: the `+`-tree of the address is flattened into
non-literal atoms and a literal sum; a base matches if its (nonempty) atoms are among the
address's and its literal is at most the address's. Of the matching bases, the one with
the largest literal (the closest below) is taken; its depth is encoded as `100 + literal`. -/

/-- Flatten a `+` tree: the non-literal atoms (left to right), the literal subterms, their
sum. -/
partial def addView (e : Expr) : MetaM (Array Expr × Array Expr × Nat) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (a1, l1, s1) ← addView (e.getArg! 4)
    let (a2, l2, s2) ← addView (e.getArg! 5)
    return (a1 ++ a2, l1 ++ l2, s1 + s2)
  if let some ⟨_, v⟩ ← getBitVecValue? e then return (#[], #[e], v.toNat)
  return (#[e], #[], 0)

/-- The atoms `as` without the atoms `bs` (as multisets, up to `sameAddr`); none if one of
`bs` is missing. -/
private def atomsMinus (as bs : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut rest := as
  for b in bs do
    let mut idx : Option Nat := none
    for i in [:rest.size] do
      if ← sameAddr rest[i]! b then
        idx := some i
        break
    let some i := idx | return none
    rest := rest.eraseIdx! i
  return some rest

/-- `b` is a region base below the address `a` by atoms: its literal offset. -/
private def symBase? (b a : Expr) : MetaM (Option Nat) := do
  let (ab, _, lb) ← addView b
  if ab.isEmpty then return none
  let (aa, _, la) ← addView a
  if lb > la then return none
  let some rest ← atomsMinus aa ab | return none
  -- a purely literal offset is the literal matchers' business (no containing cell: no match)
  if rest.isEmpty then return none
  return some lb

/-- The bases of the cells / `Blocks` entries of an atom. -/
private def atomBases (P : Expr) : MetaM (Array Expr) := do
  match cellOf? P with
  | some (.block b _) => return #[b]
  | some (.val b _) => return #[b]
  | none =>
    if P.isAppOfArity ``Mem.Blocks 2 then
      let some (_, elems) := (← instantiateMVars (P.getArg! 1)).listLit? | return #[]
      return elems.toArray.filterMap fun el =>
        if el.isAppOfArity ``Prod.mk 4 then some (el.getArg! 2) else none
    return #[]

/-- The closest symbolic-offset base below `a` in the tree `H`: its literal. -/
private def bestSymBase (H a : Expr) : MetaM (Option Nat) := do
  let mut best : Option Nat := none
  for P in ← reifyClauses extHashMapOps H do
    for b in ← atomBases P do
      if let some lb ← symBase? b a then
        if best.all (· < lb) then best := some lb
  return best

private def findRegion (H a n : Expr) :
    MetaM (Option (Bool × Expr × Expr × Expr × MVarId)) := do
  -- the base nearest to `a` (fewest added terms) first, then a base at a literal offset of
  -- the same root, then (symbolic offset) the closest base below `a` by atoms
  for d in [0, 1, 2, 3, 4, 99] do
    if let some r ← findRegionAt H a n d then return some r
  if let some lb ← bestSymBase H a then
    if let some r ← findRegionAt H a n (100 + lb) then return some r
  return none
where
  isPrefix (b a : Expr) (d : Nat) : MetaM Bool := do
    if d ≥ 100 then return (← symBase? b a) == some (d - 100)
    if d == 99 then litMatch b a else return (← prefixDepth b a) == some d
  /-- `isPrefix` and the access fits (when the offset and length are literals). -/
  fits (b a n len : Expr) (d : Nat) : MetaM Bool := do
    if !(← isPrefix b a d) then return false
    if d ≥ 100 then return true
    if !(← litOk b a n len) then return false
    if d == 99 then return true else prefixFits b a n len
  findRegionAt (H a n : Expr) (d : Nat) :
    MetaM (Option (Bool × Expr × Expr × Expr × MVarId)) := do
  let found : IO.Ref (Option (Bool × Expr × MVarId)) ← IO.mkRef none
  let pred := fun (P : Expr) => do
    if let some (.block b len) := cellOf? P then
      if ← fits b a n len d then
        let ty ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
          #[← mkAppM ``HSub.hSub #[a, b]], n], len]
        let mv ← mkFreshExprSyntheticOpaqueMVar ty (if d ≥ 100 then `sep_off else .anonymous)
        found.set (some (false, mv, mv.mvarId!)); return true
      return false
    if P.isAppOfArity ``Mem.Blocks 2 then
      let bs := P.getArg! 1
      let some (_, elems) := (← instantiateMVars bs).listLit? | return false
      -- membership proof built along the list
      let mut i := 0
      for el in elems do
        if el.isAppOfArity ``Prod.mk 4 then
          let b := el.getArg! 2
          let len := el.getArg! 3
          if ← fits b a n len d then
            let ty ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
              #[← mkAppM ``HSub.hSub #[a, b]], n], len]
            let mv ← mkFreshExprSyntheticOpaqueMVar ty (if d ≥ 100 then `sep_off else .anonymous)
            let mem ← mkFreshExprMVar (← mkAppM ``Membership.mem #[bs, el])
            -- `(b, len) ∈ bs` by `simp`
            let ok ← try
                let gs ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run mem.mvarId!
                  (Lean.Elab.Tactic.evalTactic (← `(tactic| simp))))
                pure gs.isEmpty
              catch _ => pure false
            unless ok do return false
            let hin ← mkAppM ``Mem.Blocks.Inside.of_mem #[mem, mv]
            found.set (some (true, hin, mv.mvarId!)); return true
        i := i + 1
      return false
    return false
  let some (_, R, hs) ← findSplit pred H | return none
  let some (isB, hin, side) ← found.get | return none
  return some (isB, R, hs, hin, side)

/-- An access off the base of a known cell `bs =@ b` (`b` a prefix of `a`, or at a literal
offset of the same root): `(R, split, inside goal, width goal)`, the side goals being
`(a - b).toNat + n ≤ bs.length` and `bs.length ≤ 2 ^ w`. -/
private def findValRegionAt (H a n w : Expr) (d : Nat) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  repeat
    let found : IO.Ref (Option (Expr × Expr)) ← IO.mkRef none
    let pred := fun (P : Expr) => do
      if let some (.val b bs) := cellOf? P then
        let bs' ← instantiateMVars bs
        let lenE := if bs'.isAppOfArity ``Int.toBytes 2 then bs'.appFn!.appArg!
          else match bs'.listLit? with
            | some (_, es) => mkNatLit es.length
            | none => mkNatLit (2 ^ 64)
        -- a literal-offset match needs a known length (cells are disjoint: only the
        -- containing one passes `litOk`)
        let known := bs'.isAppOfArity ``Int.toBytes 2 || bs'.listLit?.isSome
        if d == 99 && !known then return false
        if ← findRegion.fits b a n lenE d then
          found.set (some (bs, b)); return true
      return false
    if let some (_, R, hs) ← findSplit pred H then
      let some (bs, b) ← found.get | break
      let len ← mkAppM ``List.length #[bs]
      let ty ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat
        #[← mkAppM ``HSub.hSub #[a, b]], n], len]
      let hin ← mkFreshExprSyntheticOpaqueMVar ty (if d ≥ 100 then `sep_off else .anonymous)
      let hw ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[len, ← mkAppM ``HPow.hPow #[mkNatLit 2, w]])
        (if d ≥ 100 then `sep_off else .anonymous)
      return some (R, hs, hin, hw)
    break
  return none

/-- A region access, Val slice or Block/Blocks, base nearest to the address first (a Val cell
deeper than a block base is never preferred over it). -/
inductive RegionHit where
  | val (R hs hin hw : Expr)
  | blk (isB : Bool) (R hs hin : Expr) (sg : MVarId)

private def findAnyRegion (H a n w : Expr) : MetaM (Option RegionHit) := do
  for d in [0, 1, 2, 3, 4, 99] do
    if let some (R, hs, hin, hw) ← findValRegionAt H a n w d then
      return some (.val R hs hin hw)
    if let some (isB, R, hs, hin, sg) ← findRegion.findRegionAt H a n d then
      return some (.blk isB R hs hin sg)
  -- symbolic offset: only when nothing matched syntactically (computed lazily)
  let some lb ← bestSymBase H a | return none
  let d := 100 + lb
  if let some (R, hs, hin, hw) ← findValRegionAt H a n w d then
    return some (.val R hs hin hw)
  if let some (isB, R, hs, hin, sg) ← findRegion.findRegionAt H a n d then
    return some (.blk isB R hs hin sg)
  return none

/-- The innermost `storeInt m a n v` of `e` over the memory `m`. -/
private partial def findStore (m : Expr) (e : Expr) : Option (Expr × Expr × Expr) :=
  e.find? (fun t => t.isAppOfArity ``Mem.storeInt 5 && t.getArg! 1 == m) |>.map
    fun t => (t.getArg! 2, t.getArg! 3, t.getArg! 4)

/-- The fact after one store: from `hE : m =⋆ H`, a proof of `m.storeInt a n v =⋆ H'`
(side goals of region accesses pushed to `side`). -/
private def storeProof (hE H m a n v : Expr) (side : IO.Ref (Array MVarId)) : MetaM Expr := do
  match ← findCell H a n with
  | some (c, _R, hs, hl) => match c with
    | .block _ len => match hl with
      | none => mkAppM ``Mem.Block.storeInt_val #[hE, hs, v]
      | some hin =>
        let split := sep_mem.splitNarrow.get (← getOptions)
        match split, (← instantiateMVars n).nat?, (← instantiateMVars len).nat? with
        | true, some nv, some lv =>
          let k := mkNatLit (lv - nv)
          let hn ← mkDecideProof (← mkEq (← mkAppM ``HAdd.hAdd #[n, k]) len)
          mkAppM ``Mem.Block.storeInt_val_split #[hE, hs, hn, ← widthProof len (← memWidth m), v]
        | _, _, _ => mkAppM ``Mem.Block.storeInt_split #[hE, hs, hin, v]
    | .val .. => mkAppM ``Mem.Val.storeInt #[hE, hs, hl.get!, v]
  | none =>
    match ← findAnyRegion H a n (← memWidth m) with
    | some (.val _ hs hin hw) =>
      side.modify (·.push hin.mvarId! |>.push hw.mvarId!)
      mkAppM ``Mem.Val.storeInt_slice_split #[hE, hs, hin, hw, v]
    | some (.blk isB _ hs hin sg) =>
      side.modify (·.push sg)
      if isB then mkAppM ``Mem.Blocks.storeInt_split #[hE, hs, hin, v]
      else mkAppM ``Mem.Block.storeInt_split #[hE, hs, hin, v]
    | none => throwError "sep_mem: no cell at {a} of size {n} in the memory fact"

/-- One store step: returns the new fact's fvar, or none. -/
private def storeStep (g : MVarId) (h : FVarId) (side : IO.Ref (Array MVarId)) :
    MetaM (Option (MVarId × FVarId)) := g.withContext do
  let hty := (← instantiateMVars (← h.getType)).consumeMData
  let H := hty.appFn!
  let m := hty.appArg!
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let some (a, n, v) := findStore m tgt | return none
  let pf ← storeProof (.fvar h) H m a n v side
  let ty ← inferType pf
  let name ← h.getUserName
  let (fv, g) ← g.assert name ty pf >>= fun g => g.intro1P
  let g ← g.tryClear h
  return some (g, fv)

/-- A fact for the memory `m'`, a chain of stores over the fact's memory `m`
(`hE : m =⋆ H`): the proof and its separation tree, or none. -/
private partial def factAt (hE H m m' : Expr) (side : IO.Ref (Array MVarId)) :
    MetaM (Option (Expr × Expr)) := do
  if m' == m then return some (hE, H)
  unless m'.isAppOfArity ``Mem.storeInt 5 do return none
  let some (hE', H') ← factAt hE H m (m'.getArg! 1) side | return none
  let pf ← storeProof hE' H' (m'.getArg! 1) (m'.getArg! 2) (m'.getArg! 3) (m'.getArg! 4) side
  let ty := (← instantiateMVars (← inferType pf)).consumeMData
  return some (pf, ty.appFn!)

/-- Unfold reducible atoms of a tree (`abbrev` groups of cells, `RetCell`) until
every atom is a cell or an irreducible predicate. -/
partial def normTree (e : Expr) : MetaM Expr := do
  if isSep e then
    let (l, r) := sepArgs e
    return mkSepLike e (← normTree l) (← normTree r)
  let e' ← whnfR e
  if e' == e then return e
  if isSep e' || (cellOf? e').isSome then normTree e' else return e

/-- `normTree`; under `kraken.sepFast` memoised per command (a fact's tree is normalised once,
later `sep_*` calls on it, in this goal or the block's other goals, are a lookup). -/
def normTreeC (e : Expr) : MetaM Expr := do
  unless kraken.sepFast.get (← getOptions) && (← sepCacheable e) do return ← normTree e
  if let some r ← sepCacheGet? normTreeCache e then
    if kraken.sepFast.check.get (← getOptions) then
      let r' ← sepUncounted (normTree e)
      if r != r' then sepFastDiff m!"normTree: cached{indentExpr r}\nfresh{indentExpr r'}"
    return r
  let r ← normTree e
  sepCacheSet normTreeCache e r
  sepCacheSet normTreeCache r r
  return r

/-- Bring the fact `h : H m` to `normTree H`, by `change`. -/
def normFact (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← h.getType)).consumeMData
  unless ty.isApp do throwError "sep: the fact is not `H m`:{indentExpr ty}"
  let H' ← normTreeC ty.appFn!
  if H' == ty.appFn! then return g
  g.replaceLocalDeclDefEq h (mkApp H' ty.appArg!)

/-- Bring the goal `G m` to `normTree G`, by `change`. -/
def normGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isApp do throwError "sep: the goal is not `G m`:{indentExpr ty}"
  let G' ← normTreeC ty.appFn!
  if G' == ty.appFn! then return g
  g.replaceTargetDefEq (mkApp G' ty.appArg!)

private partial def collectGo (p : Expr → Bool) (e : Expr) :
    StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a) => (s.insert e, if p e then a.push e else a)
  match e with
  | .app f a => collectGo p f; collectGo p a
  | .lam _ t b _ | .forallE _ t b _ => collectGo p t; collectGo p b
  | .letE _ t v b _ => collectGo p t; collectGo p v; collectGo p b
  | .mdata _ b | .proj _ _ b => collectGo p b
  | _ => pure ()

/-- All distinct subterms of `e` satisfying `p` (outermost first), each shared subterm
visited once (vector values are heavily shared: a tree walk is exponential). -/
private def collect (p : Expr → Bool) (e : Expr) (acc : Array Expr) : Array Expr :=
  ((collectGo p e).run ({}, acc)).2.2

/-- Assign a constructed proof after checking its type against the goal: a mismatch fails
here with a clear message instead of in the kernel ("application type mismatch"). -/
def assignChecked (tac : String) (g : MVarId) (pf : Expr) : MetaM Unit := do
  let ty ← inferType pf
  let gt ← g.getType
  unless ← isDefEq ty gt do
    throwError "{tac}: internal error, constructed proof has type{indentExpr ty}\nbut the goal is{indentExpr gt}"
  g.assign pf

/-- Close `(loadInt m a n).isSome = true`, or rewrite known loads. -/
private def loadStep (g : MVarId) (h : FVarId) (side : IO.Ref (Array MVarId)) :
    MetaM (Option MVarId) := g.withContext do
  let hty := (← instantiateMVars (← h.getType)).consumeMData
  let H := hty.appFn!
  let m := hty.appArg!
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let w ← memWidth m
  -- isSome goal
  if let some (_, lhs, _) := tgt.eq? then
    if lhs.isAppOfArity ``Option.isSome 2 then
      let ld := lhs.appArg!
      if ld.isAppOfArity ``Mem.loadInt 4 && ld.getArg! 1 == m then
        let a := ld.getArg! 2
        let n := ld.getArg! 3
        let pf ← match ← findCell H a n with
          | some (c, _, hs, hl) => match c with
            | .block .. => match hl with
              | none => mkAppM ``Mem.Block.loadInt_isSome_here #[.fvar h, hs]
              | some hin => mkAppM ``Mem.Block.loadInt_isSome_split #[.fvar h, hs, hin]
            | .val .. => mkAppM ``Mem.Val.loadInt_isSome #[.fvar h, hs, hl.get!, ← widthProof n w]
          | none =>
            match ← findAnyRegion H a n w with
            | some (.val _ hs hin hw) =>
              side.modify (·.push hin.mvarId! |>.push hw.mvarId!)
              assignChecked "sep_mem" g (← mkAppM ``Mem.Val.loadInt_isSome_slice #[.fvar h, hs, hin, hw])
              return none
            | some (.blk isB _ hs hin sg) =>
              side.modify (·.push sg)
              if isB then mkAppM ``Mem.Blocks.loadInt_isSome_split #[.fvar h, hs, hin]
              else mkAppM ``Mem.Block.loadInt_isSome_split #[.fvar h, hs, hin]
            | none => throwError "sep_mem: no cell at {a} of size {n} for the load"
        assignChecked "sep_mem" g pf
        return none
  -- rewrite loads of known cells
  let mut g := g
  let loads := collect (fun t => t.isAppOfArity ``Mem.loadInt 4 && t.getArg! 1 == m) tgt #[]
  let mut seen : Array Expr := #[]
  for ld in loads do
    -- a rewrite replaces every occurrence: skip repeats and loads already rewritten away
    if seen.contains ld then continue
    seen := seen.push ld
    unless ((← instantiateMVars (← g.getType)).find? (· == ld)).isSome do continue
    let a := ld.getArg! 2
    let n := ld.getArg! 3
    if let some (.val .., _, hs, some hl) ← findCell H a n then
      let eq ← mkAppM ``Mem.Val.loadInt #[.fvar h, hs, hl, ← widthProof n w]
      let r ← g.rewrite (← g.getType) eq
      g ← g.replaceTargetEq r.eNew r.eqProof
    else if (← findCell H a n).isNone then
      if let some (.val _ hs hin hw) ← findAnyRegion H a n w then
        side.modify (·.push hin.mvarId! |>.push hw.mvarId!)
        let eq ← mkAppM ``Mem.Val.loadInt_slice_split #[.fvar h, hs, hin, hw]
        let r ← g.rewrite (← g.getType) eq
        g ← g.replaceTargetEq r.eNew r.eqProof
  return some g

/-- Forget known cells of `h` that the goal `G m` lists as unknown. -/
private def forgetFor (g : MVarId) (h : FVarId) (G : Expr) : MetaM (MVarId × FVarId) := do
  let mut g := g
  let mut h := h
  let goalAtoms ← reifyClauses extHashMapOps G
  for atom in goalAtoms do
    let some (.block a n) := cellOf? atom | continue
    let (g', h') ← g.withContext do
      let hty := (← instantiateMVars (← h.getType)).consumeMData
      let H := hty.appFn!
      let m := hty.appArg!
      let hypAtoms ← reifyClauses extHashMapOps H
      if hypAtoms.any (· == atom) then return (g, h)
      let some (.val .., _, hs, some hl) ← findCell H a n | return (g, h)
      let pf ← mkAppM ``Mem.Val.forget_len #[.fvar h, hs, hl, ← widthProof n (← memWidth m)]
      let name ← h.getUserName
      let (fv, g) ← g.assert name (← inferType pf) pf >>= fun g => g.intro1P
      let g ← g.tryClear h
      return (g, fv)
    g := g'; h := h'
  return (g, h)

/-- Run a tactic on a fresh goal of type `ty`: the proof if it closes it. -/
private def proveBy (ty : Expr) (tac : TSyntax `tactic) : MetaM (Option Expr) := do
  let mv ← mkFreshExprMVar ty
  try
    let gs ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run mv.mvarId!
      (Lean.Elab.Tactic.evalTactic tac))
    if gs.isEmpty then return some (← instantiateMVars mv) else return none
  catch _ => return none

private def foldAdd (xs : Array Expr) : MetaM Expr := do
  let mut acc := xs[0]!
  for x in xs[1:] do acc ← mkAppM ``HAdd.hAdd #[acc, x]
  return acc

/-- `a - b = x`, `x = ofNat d + (the atoms of a not in b)` (or `ofNat d`): `(x, proof)`. The
permutations by `ac_rfl`, the literal arithmetic by `decide`. -/
def offsetEq (a b w : Expr) : MetaM (Option (Expr × Expr)) := do
  let (aa, la, sa) ← addView a
  let (ab, lbs, sb) ← addView b
  let some rest ← atomsMinus aa ab | return none
  if aa.isEmpty then return none
  let some wn := (← instantiateMVars w).nat? | return none
  let m := 2 ^ wn
  let d := (sa % m + m - sb % m) % m
  let dE ← mkAppM ``BitVec.ofNat #[w, mkNatLit d]
  let x ← if rest.isEmpty then pure dE else mkAppM ``HAdd.hAdd #[dE, ← foldAdd rest]
  let Sa ← foldAdd aa
  let La ← if la.isEmpty then mkAppM ``BitVec.ofNat #[w, mkNatLit 0] else foldAdd la
  let Lbd ← foldAdd (lbs.push dE)
  let lhs1 ← mkAppM ``HAdd.hAdd #[Sa, La]
  let rhs2 ← mkAppM ``HAdd.hAdd #[Sa, Lbd]
  let some e1 ← proveBy (← mkEq a lhs1)
      (← `(tactic| first | ac_rfl | (rw [BitVec.add_zero]; ac_rfl))) | return none
  let some e2 ← proveBy (← mkEq (← mkAppM ``HAdd.hAdd #[b, x]) rhs2) (← `(tactic| ac_rfl))
    | return none
  let some e3 ← proveBy (← mkEq La Lbd) (← `(tactic| decide)) | return none
  let pf ← mkEqTrans (← mkEqTrans e1 (← mkCongrArg lhs1.appFn! e3)) (← mkEqSymm e2)
  return some (x, ← mkAppM ``Mem.sub_eq_of_eq_add #[pf])

/-- `a = b` for two spellings of one address: the same atoms (as multisets) and the same
literal sum mod `2^w` (e.g. `X + 128#64 + 8#64` and `X + 136#64`). By `ac_rfl` + `decide`. -/
def addrEq? (a b w : Expr) : MetaM (Option Expr) := do
  let (aa, la, sa) ← addView a
  let (ab, lb, sb) ← addView b
  if aa.isEmpty || aa.size != ab.size then return none
  let some wn := (← instantiateMVars w).nat? | return none
  if sa % 2 ^ wn != sb % 2 ^ wn then return none
  let some r ← atomsMinus aa ab | return none
  unless r.isEmpty do return none
  let Sa ← foldAdd aa
  let zero ← mkAppM ``BitVec.ofNat #[w, mkNatLit 0]
  let La ← if la.isEmpty then pure zero else foldAdd la
  let Lb ← if lb.isEmpty then pure zero else foldAdd lb
  let ra ← mkAppM ``HAdd.hAdd #[Sa, La]
  let rb ← mkAppM ``HAdd.hAdd #[Sa, Lb]
  let tac ← `(tactic| first | ac_rfl | (rw [BitVec.add_zero]; ac_rfl))
  let some e1 ← proveBy (← mkEq a ra) tac | return none
  let some e2 ← proveBy (← mkEq b rb) tac | return none
  let some e3 ← proveBy (← mkEq La Lb) (← `(tactic| decide)) | return none
  return some (← mkEqTrans (← mkEqTrans e1 (← mkCongrArg ra.appFn! e3)) (← mkEqSymm e2))

/-- The bases of the cells of `H` with their `+` views (atoms, literal sum). -/
def baseViews (H : Expr) : MetaM (Array (Expr × Array Expr × Nat)) := do
  let mut out := #[]
  for P in ← reifyClauses extHashMapOps H do
    for b in ← atomBases P do
      let (ab, _, lb) ← addView b
      unless ab.isEmpty do out := out.push (b, ab, lb)
  return out

/-- Among the bases `bv` (with views), another spelling of the address `a`: `(b, a = b)`.
Cheap filters first (exact base, atom count, literal sum); `ac_rfl` only on a candidate. -/
def respellIn? (bv : Array (Expr × Array Expr × Nat)) (a w : Expr) : MetaM (Option (Expr × Expr)) := do
  if bv.any (·.1 == a) then return none
  let (aa, _, sa) ← addView a
  if aa.isEmpty then return none
  let some wn := (← instantiateMVars w).nat? | return none
  for (b, ab, lb) in bv do
    if ab.size != aa.size || lb % 2 ^ wn != sa % 2 ^ wn then continue
    let some r ← atomsMinus aa ab | continue
    unless r.isEmpty do continue
    if let some eq ← addrEq? a b w then return some (b, eq)
  return none

/-- A cell / region base of `H` that is another spelling of the address `a`: `(b, a = b)`. -/
def respellAddr? (H a w : Expr) : MetaM (Option (Expr × Expr)) := do
  respellIn? (← baseViews H) a w

/-- Respell the addresses of the goal's loads and stores as the bases of the cells of `h`
they denote (`X + 128#64 + 8#64` ↦ `X + 136#64`), so that exact-cell lookups match. -/
def respellGoal (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let hty := (← instantiateMVars (← h.getType)).consumeMData
  let H := hty.appFn!
  let w ← memWidth hty.appArg!
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let accs := collect (fun t => t.isAppOfArity ``Mem.loadInt 4 || t.isAppOfArity ``Mem.storeInt 5) tgt #[]
  if accs.isEmpty then return g
  let bv ← baseViews H
  let mut g := g
  let mut seen : Array Expr := #[]
  for t in accs do
    let a := t.getArg! 2
    if seen.contains a then continue
    seen := seen.push a
    let some (_, eq) ← respellIn? bv a w | continue
    let r ← try some <$> g.rewrite (← g.getType) eq catch _ => pure none
    let some r := r | continue
    g ← g.replaceTargetEq r.eNew r.eqProof
  return g

/-- An upper bound `B` of `x.toNat`, `%`-free: `(B, proof of x.toNat ≤ B)`. -/
partial def toNatBound (x : Expr) : MetaM (Expr × Expr) := do
  let x ← instantiateMVars x
  if x.isAppOfArity ``HAdd.hAdd 6 || x.isAppOfArity ``HMul.hMul 6 then
    let isAdd := x.isAppOfArity ``HAdd.hAdd 6
    let (B1, p1) ← toNatBound (x.getArg! 4)
    let (B2, p2) ← toNatBound (x.getArg! 5)
    let (op, le, mono) := if isAdd then (``HAdd.hAdd, ``Mem.toNat_add_le, ``Nat.add_le_add)
      else (``HMul.hMul, ``Mem.toNat_mul_le, ``Nat.mul_le_mul)
    let B ← mkAppM op #[B1, B2]
    let pf ← mkAppM ``Nat.le_trans #[← mkAppM le #[x.getArg! 4, x.getArg! 5], ← mkAppM mono #[p1, p2]]
    return (B, pf)
  if x.isAppOfArity ``BitVec.ofNat 2 then
    return (x.getArg! 1, ← mkAppM ``Mem.toNat_ofNat_le #[x.getArg! 0, x.getArg! 1])
  if let some ⟨_, v⟩ ← getBitVecValue? x then
    let B := mkNatLit v.toNat
    return (B, ← mkDecideProof (← mkAppM ``LE.le #[← mkAppM ``BitVec.toNat #[x], B]))
  if x.isAppOfArity ``BitVec.setWidth 3 then
    let (B, p) ← toNatBound (x.getArg! 2)
    return (B, ← mkAppM ``Nat.le_trans #[← mkAppM ``Mem.toNat_setWidth_le #[x.getArg! 2], p])
  if x.isAppOfArity ``HShiftLeft.hShiftLeft 6 && (x.getArg! 1).isConstOf ``Nat then
    let (B, p) ← toNatBound (x.getArg! 4)
    let k := x.getArg! 5
    let B' ← mkAppM ``HMul.hMul #[B, ← mkAppM ``HPow.hPow #[mkNatLit 2, k]]
    let mono ← mkAppM ``Nat.mul_le_mul_right #[← mkAppM ``HPow.hPow #[mkNatLit 2, k], p]
    return (B', ← mkAppM ``Nat.le_trans #[← mkAppM ``Mem.toNat_shiftLeft_le #[x.getArg! 4, k], mono])
  let t ← mkAppM ``BitVec.toNat #[x]
  return (t, ← mkAppM ``Nat.le_refl #[t])

/-- Reduce `(a - b).toNat + n ≤ len` (a symbolic-offset access) to `B + n ≤ len`. -/
def sepOffCore (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  unless tgt.isAppOfArity ``LE.le 4 do return none
  let lhs := tgt.getArg! 2
  let len := tgt.getArg! 3
  unless lhs.isAppOfArity ``HAdd.hAdd 6 do return none
  let tn := lhs.getArg! 4
  let n := lhs.getArg! 5
  unless tn.isAppOfArity ``BitVec.toNat 2 do return none
  let w := tn.getArg! 0
  let sub := tn.getArg! 1
  unless sub.isAppOfArity ``HSub.hSub 6 do return none
  let some (x, hx) ← offsetEq (sub.getArg! 4) (sub.getArg! 5) w | return none
  let (B, hB) ← toNatBound x
  let rest ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[B, n], len])
    (← g.getTag)
  assignChecked "sep_off" g (← mkAppM ``Mem.inside_of_bound #[hx, hB, rest])
  return some rest.mvarId!

/-- `omega` on a `Nat` goal, in a copy of the context without hypotheses that mention `%`
(on a symbolic `x % 2^64` omega's case splits do not terminate in practice, and heartbeats
do not stop it). -/
def omegaNoMod (g : MVarId) : MetaM Bool := g.withContext do
  let mut g' := (← mkFreshExprSyntheticOpaqueMVar (← g.getType)).mvarId!
  let pf := Expr.mvar g'
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).find? (fun t => t.isAppOfArity ``HMod.hMod 6) |>.isSome then
      g' ← g'.tryClear d.fvarId
  let ok ← try
      let gs ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run g'
        (Lean.Elab.Tactic.evalTactic (← `(tactic|
          ((try simp only [Int.toBytes_length, List.length_cons, List.length_nil, List.length_append,
              List.length_take, List.length_drop, Nat.reducePow, Nat.reduceAdd, Nat.reduceLeDiff,
              Nat.reduceMul])
           first | done | omega)))))
      pure gs.isEmpty
    catch _ => pure false
  if ok then g.assign (← instantiateMVars pf)
  return ok

/-- `sep_off`: a side goal `(a - b).toNat + n ≤ len` of an access at a symbolic offset
from a region base `b`: `a - b` is normalised to `d + (index terms)`, the offset bounded
structurally (`toNat_add_le`, `toNat_mul_le`, `toNat_ofNat_le`, …), and the `%`-free rest
`B + n ≤ len` is left to `omega` over the `%`-free hypotheses (e.g. `j ≤ 8`,
`rbx.toNat < 48`); if `omega` fails, that goal is left. -/
syntax (name := sepOff) "sep_off" : tactic

@[tactic sepOff]
def evalSepOff : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some r ← sepOffCore g | throwError "sep_off: not an access-offset goal (a - b).toNat + n ≤ len"
  if ← omegaNoMod r then replaceMainGoal [] else replaceMainGoal [r]

/-- `sep_mem h`: step the goal's stores over the memory of `h : m =⋆ H`, then
close a load-succeeds goal or rewrite known loads. -/
syntax (name := sepMem) "sep_mem " ident : tactic

@[tactic sepMem]
def evalSepMem : Tactic := fun stx => withSepKey <| withMainContext do
  let h ← getFVarId stx[1]
  let mut g ← normFact (← getMainGoal) h
  g ← (try respellGoal g h catch _ => pure g)
  let mut h := h
  let side ← IO.mkRef #[]
  repeat
    match ← storeStep g h side with
    | some (g', h') => g := g'; h := h'
    | none => break
  let rest := (← side.get).toList
  let res ← loadStep g h side
  -- symbolic-offset side goals: `sep_off` (left as `B + n ≤ len` if omega fails)
  let mut sides : List MVarId := []
  for sg in (← side.get).toList do
    if (← sg.getTag) == `sep_off then
      match ← (try sepOffCore sg catch _ => pure none) with
      | some r => if !(← omegaNoMod r) then sides := sides ++ [r]
      | none => if !(← omegaNoMod sg) then sides := sides ++ [sg]
    else sides := sides ++ [sg]
  match res with
  | some g' => replaceMainGoal (g' :: sides)
  | none => let _ := rest; replaceMainGoal sides

/-- `solveSepEq` with every atom first replaced by a fresh variable: the AC normaliser then
sees only `⋆` (it also normalises `+` inside atoms, e.g. `664 + k`, and under dependent
types such a rewrite yields an ill-typed proof — a kernel "application type mismatch"). -/
def solveSepEqAbs (H G : Expr) : MetaM (Option Expr) := do
  let H ← instantiateMVars H
  let G ← instantiateMVars G
  if H == G then return some (← mkEqRefl H)
  let mut atoms : Array Expr := #[]
  for a in (← reifyClauses extHashMapOps H) ++ (← reifyClauses extHashMapOps G) do
    unless atoms.contains a do atoms := atoms.push a
  if atoms.any (·.hasMVar) then return ← solveSepEq extHashMapOps H G
  let predType ← inferType H
  let decls := atoms.mapIdx fun i _ => ((`sepAtom).appendIndexAfter i, fun _ => pure predType)
  withLocalDeclsD decls fun xs => do
    let abs := fun (e : Expr) => e.replace fun t =>
      match atoms.idxOf? t with
      | some i => some xs[i]!
      | none => none
    let some eq ← solveSepEq extHashMapOps (abs H) (abs G) | return none
    let eq ← instantiateMVars eq
    return some (eq.replaceFVars xs atoms)

/-- Are two memory terms equal: syntactically along the common application spine, and at the
first differing subterms up to default-transparency defeq (e.g. `↑0` vs
`(setWidth 32 0#64).toInt`). Never unfolds the whole memory term; a runtime exception
(recursion depth, heartbeats) on a leaf counts as "not equal". -/
partial def memDefEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if a.isApp && b.isApp && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs then
    for x in a.getAppArgs, y in b.getAppArgs do
      unless ← memDefEq x y do return false
    return true
  if ← withReducible (withNewMCtxDepth (isDefEq a b)) then return true
  -- own small budget: a hard leaf must not exhaust the declaration's heartbeats
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000 * 1000 })
      (withNewMCtxDepth (isDefEq a b)))
    (fun _ => pure false)

/-! ### Frame-level `sep_close` (option `kraken.sepCloseFrame`)

At a whole-frame exit the goal's tree `G` (the unfolded frame) and the fact's tree `H` mostly
agree: most cells are untouched, and whole groups are untouched subtrees. The default path pays
per cell: a goal atom spelled differently from the fact's (`lab l` vs `(label l).toBitVec`,
`Nat.cast` vs `NatCast.natCast`) is not found by `==`, so `forgetFor` walks the tree with
`isDefEq` for it, the first `solveSepEqAbs` fails, every unmatched pair is compared, and the
AC proof then runs over all cells. The frame path instead
1. respells each goal atom missing from `H` as its partner in `H` (looked up by head constant
   and address, then by head and size/contents; one `memDefEq` per candidate);
2. forgets with the fact's atom set computed once;
3. abstracts the maximal `⋆`-subtrees common to both trees as single atoms, so the AC proof
   runs over a few dozen atoms instead of every cell.
The goal is closed up to the defeq respelling (`mkExpectedTypeHint`). If any step fails, the
default path runs from the original goal.

Off by default: together with `kraken.sepAC` and `kraken.sepFast` the frame path saved only
about 2.8% heartbeats on the measured Apply blocks (below the 5% bar for a new default path).
The code is kept for diagnosis and for proofs dominated by whole-frame exits. -/

register_option kraken.sepCloseFrame : Bool := {
  defValue := false
  descr := "sep_close: try the frame-level path first (respell atoms, abstract common subtrees)"
}

initialize registerTraceClass `kraken.sepCloseFrame

/-- A key of an atom for partner lookup: its head constant and its address (argument 1). -/
private def frameAtomKey (e : Expr) : Option (Name × Expr) :=
  match e.getAppFn.constName? with
  | some c => if e.getAppNumArgs ≥ 2 then some (c, e.getArg! 1) else none
  | none => none

/-- Two atoms equal up to defeq: `memDefEq` (syntactic spine, cheap), else a whole-term
`isDefEq` with its own small budget (e.g. `DScW x.d0 t 0` vs `DScW x.push.d0 t 0`, which
the spine walk rejects at `x` vs `x.push`). -/
private def frameAtomDefEq (a b : Expr) : MetaM Bool := do
  if ← memDefEq a b then return true
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000 * 1000 })
      (withNewMCtxDepth (isDefEq a b)))
    (fun _ => pure false)

/-- Respell the atoms of `G` that are not atoms of `H` as their (defeq) partner atom of `H`.
Returns the respelled `G` and the number of atoms respelled. -/
def respellFrameAtoms (H G : Expr) : MetaM (Expr × Nat) := do
  let lH ← reifyClauses extHashMapOps H
  let lG ← reifyClauses extHashMapOps G
  let sH : Std.HashSet Expr := lH.foldl (·.insert ·) {}
  let sG : Std.HashSet Expr := lG.foldl (·.insert ·) {}
  let candH := lH.filter (!sG.contains ·)
  if candH.isEmpty then return (G, 0)
  let mut byKey : Std.HashMap (Name × Expr) (List Expr) := {}
  let mut byKeyR : Std.HashMap (Name × Expr) (List Expr) := {}
  for a in candH do
    if let some k := frameAtomKey a then
      byKey := byKey.insert k (a :: byKey.getD k [])
      let k' := (k.1, ← whnfR k.2)
      byKeyR := byKeyR.insert k' (a :: byKeyR.getD k' [])
  let mut rep : Std.HashMap Expr Expr := {}
  let mut used : Std.HashSet Expr := {}
  for b in lG do
    if sH.contains b || rep.contains b then continue
    let some k := frameAtomKey b | continue
    let mut found := false
    for a in byKey.getD k [] do
      if !used.contains a && (← frameAtomDefEq a b) then
        rep := rep.insert b a; used := used.insert a; found := true; break
    unless found do
      for a in byKeyR.getD (k.1, ← whnfR k.2) [] do
        if !used.contains a && (← frameAtomDefEq a b) then
          rep := rep.insert b a; used := used.insert a; found := true; break
    unless found do
      -- same head and same last argument (size or contents), the address spelled otherwise
      for a in candH do
        if used.contains a then continue
        if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs
            && a.appArg! == b.appArg! then
          if ← frameAtomDefEq a b then
            rep := rep.insert b a; used := used.insert a; found := true; break
  -- last resort, among the few atoms left: any atom with the same head (e.g. `Blocks` lists
  -- whose addresses are spelled otherwise)
  let restH := candH.filter (!used.contains ·)
  if restH.length ≤ 16 then
    for b in lG do
      if sH.contains b || rep.contains b then continue
      for a in restH do
        if used.contains a then continue
        -- with very few left, any pair (e.g. a folded `abbrev` atom vs its unfolded body)
        if (a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs) || restH.length ≤ 4 then
          if ← frameAtomDefEq a b then
            rep := rep.insert b a; used := used.insert a; break
  if rep.isEmpty then return (G, 0)
  return (G.replace fun t => rep.get? t, rep.size)

/-- All `⋆`-subtrees (and leaves) of a tree. -/
private partial def sepSubtrees (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  let acc := acc.insert e
  if isSep e then
    let (l, r) := sepArgs e
    sepSubtrees r (sepSubtrees l acc)
  else acc

/-- The maximal subtrees of `e` that are in `sg`, and the leaves of `e` not inside one. -/
private partial def frameAtoms (sg : Std.HashSet Expr) (e : Expr) (acc : Array Expr) :
    Array Expr :=
  if sg.contains e then acc.push e
  else if isSep e then
    let (l, r) := sepArgs e
    frameAtoms sg r (frameAtoms sg l acc)
  else acc.push e

/-- `H = G` up to AC, with the maximal `⋆`-subtrees common to `H` and `G` abstracted as single
atoms (fresh variables) for the AC proof. Closed trees only. -/
def solveSepEqFrame (H G : Expr) : MetaM (Option Expr) := do
  let H ← instantiateMVars H
  let G ← instantiateMVars G
  if H == G then return some (← mkEqRefl H)
  if H.hasMVar || G.hasMVar then return none
  let aH := frameAtoms (sepSubtrees G {}) H #[]
  let aG := frameAtoms (sepSubtrees H {}) G #[]
  let mut idx : Std.HashMap Expr Nat := {}
  let mut atoms : Array Expr := #[]
  for a in aH ++ aG do
    unless idx.contains a do
      idx := idx.insert a atoms.size
      atoms := atoms.push a
  let predType ← inferType H
  let decls := atoms.mapIdx fun i _ => ((`sepAtom).appendIndexAfter i, fun _ => pure predType)
  withLocalDeclsD decls fun xs => do
    let abs := fun (e : Expr) => e.replace fun t => (idx.get? t).map (xs[·]!)
    let some eq ← solveSepEq extHashMapOps (abs H) (abs G) | return none
    let eq ← instantiateMVars eq
    return some (eq.replaceFVars xs atoms)

/-- `forgetFor`, with the fact's atom set computed once (and again after each forget). -/
private def forgetForFrame (g : MVarId) (h : FVarId) (G : Expr) : MetaM (MVarId × FVarId) := do
  let mut g := g
  let mut h := h
  let atomsOf := fun (g : MVarId) (h : FVarId) => g.withContext do
    let hty := (← instantiateMVars (← h.getType)).consumeMData
    return (← reifyClauses extHashMapOps hty.appFn!).foldl
      (fun (s : Std.HashSet Expr) a => s.insert a) {}
  let mut hyp ← atomsOf g h
  for atom in ← reifyClauses extHashMapOps G do
    let some (.block a n) := cellOf? atom | continue
    if hyp.contains atom then continue
    let r ← g.withContext do
      let hty := (← instantiateMVars (← h.getType)).consumeMData
      let H := hty.appFn!
      let m := hty.appArg!
      let some (.val .., _, hs, some hl) ← findCell H a n | return none
      let pf ← mkAppM ``Mem.Val.forget_len #[.fvar h, hs, hl, ← widthProof n (← memWidth m)]
      let name ← h.getUserName
      let (fv, g) ← g.assert name (← inferType pf) pf >>= fun g => g.intro1P
      return some (← g.tryClear h, fv)
    if let some (g', h') := r then
      g := g'; h := h'
      hyp ← atomsOf g h
  return (g, h)

/-- The frame-level path of `sep_close` on the normalised goal `g` (`m =⋆ G`) and fact `h`:
the remaining goals, or none (nothing assigned). -/
def sepCloseFrame (g : MVarId) (h : FVarId) : MetaM (Option (List MVarId)) := do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let G := tgt.appFn!
  let H0 ← g.withContext do return (← instantiateMVars (← h.getType)).consumeMData.appFn!
  let (G', nrep) ← g.withContext <| respellFrameAtoms H0 G
  let (g, h) ← forgetForFrame g h G'
  g.withContext do
    let hty := (← instantiateMVars (← h.getType)).consumeMData
    let H := hty.appFn!
    -- the forgets may leave a few atoms to pair that were too many to try before
    let (G', nrep2) ← respellFrameAtoms H G'
    let nrep := nrep + nrep2
    let some eq ← solveSepEqFrame H G' | do
      if ← isTracingEnabledFor `kraken.sepCloseFrame then
        let l ← reifyClauses extHashMapOps H
        let r ← reifyClauses extHashMapOps G'
        let l' := l.filter (!r.contains ·)
        let r' := r.filter (!l.contains ·)
        trace[kraken.sepCloseFrame] "frame solve failed ({nrep} respelled); fact only:{indentD (MessageData.joinSep ((l'.take 4).map toMessageData) Format.line)}\ngoal only:{indentD (MessageData.joinSep ((r'.take 4).map toMessageData) Format.line)}"
      return none
    let eq ← if nrep == 0 then pure eq else mkExpectedTypeHint eq (← mkEq H G)
    let mH := hty.appArg!
    let mG := tgt.appArg!
    let hm ← mkExpectedTypeHint (.fvar h) (mkApp H mH)
    let pf ← mkAppM ``Eq.mp #[← mkAppM ``congrFun #[eq, mH], hm]
    if ← memDefEq mH mG then
      assignChecked "sep_close" g pf
      return some []
    let heq ← mkFreshExprSyntheticOpaqueMVar (← mkEq mH mG) `sep_close_mem
    assignChecked "sep_close" g (← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[G, heq], pf])
    return some [heq.mvarId!]

/-- `sep_close h`: close `m =⋆ G` from `h : m =⋆ H`, forgetting contents where
`G` asks for unknown cells, up to AC. -/
syntax (name := sepClose) "sep_close " ident : tactic

@[tactic sepClose]
def evalSepClose : Tactic := fun stx => withSepKey <| withMainContext do
  let h ← getFVarId stx[1]
  let g ← normGoal (← normFact (← getMainGoal) h)
  let mut fellBack := false
  if kraken.sepCloseFrame.get (← getOptions) then
    let s ← saveState
    match ← (try sepCloseFrame g h catch _ => pure none) with
    | some gs =>
      trace[kraken.sepCloseFrame] "frame path"
      replaceMainGoal gs; return
    | none =>
      trace[kraken.sepCloseFrame] "fallback"
      s.restore
      fellBack := true
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let G := tgt.appFn!
  let (g, h) ← forgetFor g h G
  g.withContext do
    let hty := (← instantiateMVars (← h.getType)).consumeMData
    let mut H := hty.appFn!
    let mut eq? ← solveSepEqAbs H G
    if eq?.isNone then
      -- atoms equal only up to unfolding (an `abbrev` the fact has unfolded): respell
      -- the fact's atom as the goal's (reducible defeq) and retry
      let l ← reifyClauses extHashMapOps H
      let r ← reifyClauses extHashMapOps G
      let l' := l.filter fun a => !r.contains a
      let r' := r.filter fun a => !l.contains a
      for b in r' do
        for a in l' do
          if ← withReducible (withNewMCtxDepth (isDefEq a b)) then
            H := H.replace fun e => if e == a then some b else none
            break
      eq? ← solveSepEqAbs H G
    let some eq := eq?
      | do
        let l ← reifyClauses extHashMapOps H
        let r ← reifyClauses extHashMapOps G
        let l' := l.filter fun a => !r.contains a
        let r' := r.filter fun a => !l.contains a
        throwError "sep_close: unmatched in the fact:{indentD (MessageData.joinSep (l'.map toMessageData) Format.line)}\nunmatched in the goal:{indentD (MessageData.joinSep (r'.map toMessageData) Format.line)}"
    if fellBack then trace[kraken.sepCloseFrame] "fallback closed by the default path"
    let mH := hty.appArg!
    let mG := tgt.appArg!
    let hm ← mkExpectedTypeHint (.fvar h) (mkApp H mH)
    let pf ← mkAppM ``Eq.mp #[← mkAppM ``congrFun #[eq, mH], hm]
    if ← memDefEq mH mG then
      assignChecked "sep_close" g pf
      replaceMainGoal []
    else
      -- the goal's memory was rewritten (e.g. `BitVec.add_assoc` on store addresses) and is
      -- no longer the fact's: leave the memory equation (normalise `hm` and the goal alike)
      let heq ← mkFreshExprSyntheticOpaqueMVar (← mkEq mH mG) `sep_close_mem
      assignChecked "sep_close" g (← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[G, heq], pf])
      replaceMainGoal [heq.mvarId!]

/-- Pull the atoms `ts` (in order) to the front of the tree `T`: the new tree
`t₁ ⋆ (t₂ ⋆ … ⋆ R)` and a proof of `T = ` it. -/
partial def pullAtoms (T : Expr) : List Expr → MetaM (Expr × Expr)
  | [] => return (T, ← mkEqRefl T)
  | t :: ts => do
    let pred := fun (P : Expr) => do
      if P == t then return true
      withReducible (withNewMCtxDepth (isDefEq P t))
    let some (P, R, hs) ← findSplit pred T
      | throwError "sep_pull: no atom{indentExpr t}\nin{indentExpr T}"
    let (R', pr) ← pullAtoms R ts
    let new ← mkAppM ``Std.ExtHashMap.sep #[P, R']
    let e1 ← mkExpectedTypeHint hs (← mkEq T (← mkAppM ``Std.ExtHashMap.sep #[P, R]))
    let ctx ← withLocalDeclD `x (← inferType R) fun x => do
      mkLambdaFVars #[x] (← mkAppM ``Std.ExtHashMap.sep #[P, x])
    return (new, ← mkEqTrans e1 (← mkAppM ``congrArg #[ctx, pr]))

/-- The innermost rest of `t₁ ⋆ (t₂ ⋆ … ⋆ R)` after `n` atoms. -/
private def restAfter : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => restAfter n (sepArgs e).2

/-- `sep_pull h [t₁, …, tₙ] as R hR`: rewrite `h : m =⋆ H` to
`m =⋆ t₁ ⋆ (… ⋆ (tₙ ⋆ R))` with `R` a new variable for the remaining cells and
`hR : (the remaining cells) = R`. For a call: pull the push slot, the callee's
reservation and its footprint, and pass `R` as the callee's frame. -/
syntax (name := sepPull) "sep_pull " ident " [" term,* "]" " as " ident ident : tactic

@[tactic sepPull]
def evalSepPull : Tactic := fun stx => withSepKey <| withMainContext do
  let h ← getFVarId stx[1]
  let ts := stx[3].getSepArgs
  let rName := stx[6].getId
  let hName := stx[7].getId
  let g ← normFact (← getMainGoal) h
  g.withContext do
    let hty := (← instantiateMVars (← h.getType)).consumeMData
    let ts ← ts.toList.mapM fun t => do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      normTree (← instantiateMVars e)
    let (new, pr) ← pullAtoms hty.appFn! ts
    let m := hty.appArg!
    let pf ← mkAppM ``Eq.mp #[← mkAppM ``congrFun #[pr, m], .fvar h]
    let name ← h.getUserName
    let (fv, g) ← g.assert name (mkApp new m) pf >>= fun g => g.intro1P
    let g ← g.tryClear h
    let rest := restAfter ts.length new
    let (_, _, g) ← g.withContext <|
      g.generalizeHyp #[{ expr := rest, xName? := rName, hName? := hName }] #[fv]
    replaceMainGoal [g]

/-- `sep_vals h`: for every hypothesis `loadInt m a n = some v` (as `vcgen`
leaves a load) where `h : m =⋆ H` has a known cell at `a`, replace `v` by the
cell's value `Int.ofBytes bs` everywhere. -/
syntax (name := sepVals) "sep_vals " ident : tactic

@[tactic sepVals]
def evalSepVals : Tactic := fun stx => withSepKey <| withMainContext do
  let h ← getFVarId stx[1]
  let mut g ← normFact (← getMainGoal) h
  let decls ← g.withContext do return (← getLCtx).decls.toList.filterMap id
  for d in decls do
    if d.isImplementationDetail then continue
    let g' ← g.withContext do
      let some d := (← getLCtx).find? d.fvarId | return g
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | return g
      unless lhs.isAppOfArity ``Mem.loadInt 4 && rhs.isAppOfArity ``Option.some 2 do return g
      let v := rhs.appArg!
      unless v.isFVar do return g
      let hty := (← instantiateMVars (← h.getType)).consumeMData
      -- a load over the fact's memory, or over stores on it (facts stepped on the fly)
      let side ← IO.mkRef #[]
      let some (hE, H) ← (try factAt (.fvar h) hty.appFn! hty.appArg! (lhs.getArg! 1) side
        catch _ => pure none) | return g
      unless (← side.get).isEmpty do return g
      let a := lhs.getArg! 2
      let n := lhs.getArg! 3
      let w ← memWidth hty.appArg!
      -- the load's hypothesis, at the cell's spelling of the address
      let (a, dE) ← match ← findCell H a n with
        | some _ => pure (a, d.toExpr)
        | none =>
          let some (b, eq) ← respellAddr? H a w | return g
          let ctx ← withLocalDeclD `x (← inferType a) fun x => do
            mkLambdaFVars #[x] (← mkAppM ``Mem.loadInt #[lhs.getArg! 1, x, n])
          pure (b, ← mkEqTrans (← mkEqSymm (← mkCongrArg ctx eq)) d.toExpr)
      let some (.val .., _, hs, some hl) ← findCell H a n | return g
      let eq ← mkAppM ``Mem.Val.loadInt #[hE, hs, hl, ← widthProof n w]
      let pf ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm dE) eq]
      let (fv, g) ← g.assert `hv (← inferType pf) pf >>= fun g => g.intro1P
      let g ← g.withContext <| subst g fv
      return g
    g := g'
  replaceMainGoal [g]

/-- `simp only [lemmas]` at the hypotheses `l = r` whose left side is an application of `c`. -/
def simpHypsHeaded (c : Name) (tac : String) (stx : Syntax) : TacticM Unit := withMainContext do
  let ts : Syntax.TSepArray `term "," := ⟨stx[2].getArgs⟩
  let args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let simpStx ← `(tactic| simp only [$args,*])
  let { ctx, simprocs, .. } ← mkSimpContext simpStx (eraseLocal := false)
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut acc := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, _) := ty.eq? then
        if l.isAppOf c then acc := acc.push d.fvarId
    pure acc
  if fvs.isEmpty then throwError "{tac}: no such hypotheses"
  let (r, _) ← simpGoal g ctx simprocs (fvarIdsToSimp := fvs) (simplifyTarget := false)
  match r with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- `simp_loads [lemmas]`: `simp only [lemmas]` at every hypothesis `loadInt m a n = some v` (as
`vcgen` leaves loads, under inaccessible names), e.g. to normalise their addresses before
`sep_vals`, without touching the register facts used as lemmas. -/
syntax (name := simpLoads) "simp_loads " "[" term,* "]" : tactic

@[tactic simpLoads]
def evalSimpLoads : Tactic := simpHypsHeaded ``Mem.loadInt "simp_loads"

/-- `simp_conds [lemmas]`: `simp only [lemmas]` at every branch-condition hypothesis
`cc.interp flags = b` (closes the goal when one becomes `False`). -/
syntax (name := simpConds) "simp_conds " "[" term,* "]" : tactic

@[tactic simpConds]
def evalSimpConds : Tactic := simpHypsHeaded `CondCode.interp "simp_conds"

end Kraken.Tactic.SepStep

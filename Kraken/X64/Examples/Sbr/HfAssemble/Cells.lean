import Kraken.SepCells
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas

/-!
# Cell closers for `sbr_hf_assemble`'s block proofs

Most side goals of a block proof read a cell of the frame: `(m.loadInt a n).isSome = true`, where
`m` is the entry memory behind a few stores and `a` is syntactically the base of one cell of the
memory fact `hm : s.dmem =⋆ H`. `grind` finds that cell too, but it internalizes the whole
40-cell frame and every hypothesis first (20-50k heartbeats a goal). `cell_some` walks `H`
instead: it peels the stores (`Mem.loadInt_isSome_storeInt`), finds the cell whose base is `a`
(through `Mem.Hid`), builds the `Mem.Split` path and closes the goal with one access lemma.
It fails when no cell starts at `a`; the block proofs keep `grind` as the fallback.
`find_split h c` is the same walk for the first cell whose head constant is `c` (a named group
such as `DataW`): it adds `hsplit : Mem.Split (c …) R H`.
-/

open Lean Meta Elab Tactic
open Std.ExtHashMap

namespace Mem

/-- A load of at most a cell's size at its base succeeds. -/
theorem Block.loadInt_isSome_base {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {len n : Nat} (h : m =⋆ H) (hs : Split (len ?@ a) R H) (hn : n ≤ len) :
    (m.loadInt a n).isSome = true :=
  Block.loadInt_isSome_split h hs (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- A load of at most a known cell's size at its base succeeds. -/
theorem Val.loadInt_isSome_base {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Split (bs =@ a) R H) (hn : n ≤ bs.length)
    (hw : bs.length ≤ 2 ^ w) : (m.loadInt a n).isSome = true :=
  Block.loadInt_isSome_base (Val.forget h hs hw) (Split.here _ _) hn

end Mem

namespace Kraken.Examples.Sbr.HfAssemble.Cells

/-- `(p, q)` when `e` is `p ⋆ q`. -/
def sepArgs? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Std.ExtHashMap.sep 8 then some (e.getArg! 6, e.getArg! 7) else none

/-- Unfold `Mem.Hid` and reducible heads (`c8`-style abbreviations) one step at a time. -/
partial def expose (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Mem.Hid 1 then return ← expose (e.getArg! 0)
  if (sepArgs? e).isSome || e.isAppOfArity ``Mem.Block 3 || e.isAppOfArity ``Mem.Val 3 then
    return e
  let e' ← whnfR e
  if e' == e then return e else expose e'

/-- A proof of `Mem.Split P ?R H` for the first leaf `P` of the `⋆`-tree `H` (left to right) that
satisfies `ok`. A tree that is a single leaf is not split (the frames end in a named rest). -/
partial def findSplit (H : Expr) (ok : Expr → MetaM Bool) : MetaM (Option Expr) := do
  let H' ← expose H
  let some (p, q) := sepArgs? H' | return none
  let p' ← expose p
  if (sepArgs? p').isNone then
    if ← ok p' then
      return some (← mkAppM ``Mem.Split.here #[p', q])
  else if let some h ← findSplit p' ok then
    return some (← mkAppM ``Mem.Split.left #[h, q])
  if let some h ← findSplit q ok then
    return some (← mkAppM ``Mem.Split.right #[h, p])
  return none

/-- The hypothesis `h : m =⋆ H` for the memory `m`. -/
def findMemFact (m : Expr) : MetaM (Option (Expr × Expr)) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- `m =⋆ H` is `H m`: an application of a `⋆`-tree to `m`
    if ty.isApp && ty.appArg! == m then
      let H := ty.appFn!
      if (sepArgs? (← expose H)).isSome then return some (d.toExpr, H)
  return none

/-- Strip `storeInt`s: `((m.storeInt …).storeInt …)` ↦ `m`. -/
partial def baseMem (m : Expr) : Expr :=
  if m.isAppOfArity ``Mem.storeInt 5 then baseMem (m.getArg! 1) else m

def sameAddr (a b : Expr) : MetaM Bool := do
  if a == b then return true
  withReducible (isDefEq a b)

/-- The facts `h : s.regs.get64 r = e` of the context. -/
def regFacts : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    if l.isAppOfArity ``Reg64s.get64 2 then out := out.push (l, r, d.toExpr)
  return out

/-- Close `(m.loadInt a n).isSome = true` from the cell at `a` of `m`'s memory fact (register
reads in `a` are first rewritten by their facts `s.regs.get64 r = e`). -/
elab "cell_some_raw" : tactic => do
  -- peel the stores
  evalTactic (← `(tactic| repeat (with_reducible apply Mem.loadInt_isSome_storeInt)))
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for (l, _, h) in ← regFacts do
      let t ← instantiateMVars (← g.getType)
      if (t.find? (· == l)).isSome then
        let res ← g.rewrite t h
        g ← g.replaceTargetEq res.eNew res.eqProof
    return g
  replaceMainGoal [g]
  let g ← getMainGoal
  g.withContext do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    let some (_, lhs, _) := tgt.eq? | throwError "cell_some: not an equation"
    -- lhs = Option.isSome (Mem.loadInt m a n)
    let ld := lhs.getAppArgs.back!
    unless ld.isAppOfArity ``Mem.loadInt 4 do throwError "cell_some: not a load"
    let m := ld.getArg! 1
    let a := ld.getArg! 2
    let some (h, H) ← findMemFact m | throwError "cell_some: no memory fact"
    let ok (leaf : Expr) : MetaM Bool := do
      if leaf.isAppOfArity ``Mem.Block 3 || leaf.isAppOfArity ``Mem.Val 3 then
        sameAddr (leaf.getArg! 1) a
      else return false
    let some hs ← findSplit H ok | throwError "cell_some: no cell at the address"
    let hsTy ← inferType hs
    let leaf := hsTy.getAppArgs[hsTy.getAppNumArgs - 3]!
    let lem := if leaf.isAppOfArity ``Mem.Block 3 then ``Mem.Block.loadInt_isSome_base
      else ``Mem.Val.loadInt_isSome_base
    let e ← mkConstWithFreshMVarLevels lem
    let (args, _, concl) ← forallMetaTelescopeReducing (← inferType e)
    unless ← isDefEq args[7]! h do throwError "cell_some: memory fact mismatch"
    unless ← isDefEq args[8]! hs do throwError "cell_some: split mismatch"
    unless ← isDefEq concl (← g.getType) do throwError "cell_some: goal mismatch"
    g.assign (mkAppN e args)
    let rest ← args[9:].toArray.filterMapM fun a => do
      let a ← instantiateMVars a
      return if a.isMVar then some a.mvarId! else none
    replaceMainGoal rest.toList
  -- side conditions: `n ≤ len`, `n ≤ bs.length`, `bs.length ≤ 2 ^ w`
  evalTactic (← `(tactic| all_goals first | decide | (simp only [Int.toBytes_length]; done) | (simp only [Int.toBytes_length]; decide)))

/-- Add `hsplit : Mem.Split (c …) R H` for the first cell with head constant `c` in `h : m =⋆ H`. -/
elab "find_split " h:ident c:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let hf ← getFVarFromUserName h.getId
    let ty ← instantiateMVars (← inferType hf)
    unless ty.isApp do throwError "find_split: not a memory fact"
    let H := ty.appFn!
    let cn ← realizeGlobalConstNoOverload c
    let some hs ← findSplit H (fun leaf => pure (leaf.isAppOf cn))
      | throwError "find_split: no cell {cn}"
    let (_, g') ← (← g.assert `hsplit (← inferType hs) hs).intro1P
    replaceMainGoal [g']

end Kraken.Examples.Sbr.HfAssemble.Cells

namespace Kraken.Examples.Sbr.HfAssemble.Cells

/-- `cell_guard n tac`: run `tac` under a sub-budget of `n` heartbeats (`maxHeartbeats` units), capped
by what is left of the enclosing budget, and turn every exception, also a heartbeat or
recursion-depth one, into a plain failure (state restored), so that a `first | … | grind` falls
through to the next alternative instead of failing the proof. The sub-budget never extends the
enclosing one: the heartbeats the attempt spent still count for the declaration, and its
`maxHeartbeats` is checked as before. Interrupts are rethrown. -/
elab "cell_guard " n:num t:tactic : tactic => do
  let s ← saveState
  let ctx ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let own := n.getNat * 1000
  let lim := if ctx.maxHeartbeats == 0 then own else min own (ctx.maxHeartbeats - used)
  if lim == 0 then throwError "cell_guard: no heartbeats left"
  let r ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := lim })
      (withCurrHeartbeats (do evalTactic t; pure none)))
    (fun e => pure (some e))
  if let some e := r then
    if e.isInterrupt then throw e
    s.restore
    throwError "cell_guard: {e.toMessageData}"

end Kraken.Examples.Sbr.HfAssemble.Cells

namespace Mem

/-- A store of at most a cell's size at its base keeps the tree. -/
theorem Block.storeInt_base {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {len n : Nat} (h : m =⋆ H) (hs : Split (len ?@ a) R H) (hn : n ≤ len) (v : Int) :
    m.storeInt a n v =⋆ H :=
  Block.storeInt_split h hs (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega) v

/-- A load agrees with a load fact of the same address. -/
theorem loadInt_some_eq {w : Nat} {m : Mem w} {a : BitVec w} {n : Nat} {x y : Int}
    (hx : m.loadInt a n = some x) (hy : m.loadInt a n = some y) : x = y :=
  Option.some.inj (hx.symm.trans hy)

end Mem

namespace Kraken.Examples.Sbr.HfAssemble.Cells

/-- `M =⋆ H'` for a memory `M` that is `hm`'s memory behind stores at cell bases: a store into
an unknown cell keeps the tree (or, when it covers the cell, makes it known), a store over a known
cell of the same size puts the new bytes in front. -/
partial def frameOf (hm H m0 M : Expr) : MetaM (Option (Expr × Expr)) := do
  if M == m0 then return some (hm, H)
  unless M.isAppOfArity ``Mem.storeInt 5 do return none
  let M' := M.getArg! 1
  let b := M.getArg! 2
  let k := M.getArg! 3
  let v := M.getArg! 4
  let some (h, H') ← frameOf hm H m0 M' | return none
  let some kn ← (evalNat k).run | return none
  let ok (leaf : Expr) : MetaM Bool := do
    if leaf.isAppOfArity ``Mem.Block 3 || leaf.isAppOfArity ``Mem.Val 3 then
      sameAddr (leaf.getArg! 1) b
    else return false
  let some hs ← findSplit H' ok | return none
  let hsTy ← inferType hs
  let leaf := hsTy.getAppArgs[hsTy.getAppNumArgs - 3]!
  let R := hsTy.getAppArgs[hsTy.getAppNumArgs - 2]!
  if leaf.isAppOfArity ``Mem.Block 3 then
    let some len ← (evalNat (leaf.getArg! 2)).run | return none
    if kn == len then
      let pf ← mkAppM ``Mem.Block.storeInt_val #[h, hs, v]
      return some (pf, ← mkAppM ``Std.ExtHashMap.sep #[← mkAppM ``Mem.Val #[b, ← mkAppM ``Int.toBytes #[k, v]], R])
    else if kn < len then
      let hn ← mkDecideProof (← mkAppM ``LE.le #[k, leaf.getArg! 2])
      let pf ← mkAppM ``Mem.Block.storeInt_base #[h, hs, hn, v]
      return some (pf, H')
    else return none
  else
    let bs := leaf.getArg! 2
    unless bs.isAppOfArity ``Int.toBytes 2 do return none
    let some bn ← (evalNat (bs.getArg! 0)).run | return none
    unless bn == kn do return none
    let hlen ← mkAppM ``Int.toBytes_length #[bs.getArg! 0, bs.getArg! 1]
    let pf ← mkAppM ``Mem.Val.storeInt #[h, hs, hlen, v]
    return some (pf, ← mkAppM ``Std.ExtHashMap.sep #[← mkAppM ``Mem.Val #[b, ← mkAppM ``Int.toBytes #[k, v]], R])

/-- Rewrite the register reads of the address `a` of the load fact `hx` by `regFacts`:
the new address and the rewritten fact. -/
def normAddr (a hx : Expr) : MetaM (Expr × Expr) := do
  let mut a := a
  let mut hx := hx
  for (l, r, h) in ← regFacts do
    if (a.find? (· == l)).isSome then
      let a' := a.replace fun e => if e == l then some r else none
      let ty ← inferType hx
      let motive ← withLocalDeclD `y (← inferType l) fun y => do
        mkLambdaFVars #[y] (ty.replace fun e => if e == l then some y else none)
      hx ← mkEqMP (← mkCongrArg motive h) hx
      a := a'
  return (a, hx)

/-- For every load fact `hx : M.loadInt a n = some x` (`x` a local) whose cell at `a` is known in
`hm`'s tree (behind the stores of `M`), replace `x` by the cell's value `Int.ofBytes bs`. -/
elab "cell_reads_raw" : tactic => do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    let mut eqs : Array Expr := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``Mem.loadInt 4 && rhs.isAppOfArity ``Option.some 2 do continue
      let x := rhs.getArg! 1
      unless x.isFVar do continue
      let M := lhs.getArg! 1
      -- a register read in the address: rewrite it by its fact `s.regs.get64 r = e`
      let (a, hxe) ← normAddr (lhs.getArg! 2) d.toExpr
      let lhs ← mkAppM ``Mem.loadInt #[M, a, lhs.getArg! 3]
      let some n ← (evalNat (lhs.getArg! 3)).run | continue
      let some (hm, H) ← findMemFact (baseMem M) | continue
      let some (h, H') ← frameOf hm H (baseMem M) M | continue
      let ok (leaf : Expr) : MetaM Bool := do
        if leaf.isAppOfArity ``Mem.Val 3 then
          let bs := leaf.getArg! 2
          if bs.isAppOfArity ``Int.toBytes 2 then
            if (← (evalNat (bs.getArg! 0)).run) == some n then return ← sameAddr (leaf.getArg! 1) a
        return false
      let some hs ← try findSplit H' ok catch _ => pure none | continue
      let hsTy ← inferType hs
      let bs := (hsTy.getAppArgs[hsTy.getAppNumArgs - 3]!).getArg! 2
      let hlen ← mkAppM ``Int.toBytes_length #[bs.getArg! 0, bs.getArg! 1]
      let hw ← mkDecideProof (← mkAppM ``LE.le #[lhs.getArg! 3, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]])
      let some hval ← (try some <$> mkAppM ``Mem.Val.loadInt #[h, hs, hlen, hw] catch _ => pure none) | continue
      let some e ← (try some <$> mkAppM ``Mem.loadInt_some_eq #[hxe, hval] catch _ => pure none) | continue
      eqs := eqs.push e
    for e in eqs do
      let (fv, g') ← (← g.assert `hcell (← inferType e) e).intro1P
      g := g'
      try
        g := (← substCore g fv (symm := false) (tryToSkip := true)).2
      catch _ => pure ()
    return g
  replaceMainGoal [g]

/-- `cell_some_raw` under a 20k-heartbeat `cell_guard`. -/
macro "cell_some" : tactic => `(tactic| cell_guard 20000 cell_some_raw)

/-- `cell_reads_raw` under a 400k-heartbeat `cell_guard`. -/
macro "cell_reads" : tactic => `(tactic| cell_guard 400000 cell_reads_raw)

end Kraken.Examples.Sbr.HfAssemble.Cells

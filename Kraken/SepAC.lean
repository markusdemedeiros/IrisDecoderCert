import Lean.Meta.Basic
import Lean.Meta.SynthInstance
import Lean.Meta.AppBuilder

/-!
# Explicit AC permutation proofs for separating conjunction

`proveACPerm` proves `lhs = rhs` for two trees over an associative, commutative operator
(with a lawful identity) whose leaves agree up to permutation. Unlike
`Lean.Meta.AC.rewriteUnnormalizedRefl`, which emits a reflection proof the kernel
re-evaluates (an insertion sort over unary `Nat` atom indices), the proof here is an explicit
chain of `assoc`/`comm`/`left_comm`/identity steps with `congrArg (op a)` contexts: every step
is a constant-size term, so the kernel only instantiates lemma types and compares shared terms.

Size: flattening each side to a right comb takes one step per node; the permutation moves
each target atom to the front of the comb with one `left_comm` per position it skips, so it
costs the number of skipped positions (O(n·k) when only k atoms are out of place, O(n²) in
the worst case). The cheaper of the two directions is chosen.
-/

open Lean Meta

namespace Kraken.Tactic.SepAC

universe u

theorem left_comm {α : Sort u} {op : α → α → α} [Std.Associative op] [Std.Commutative op]
    (a b c : α) : op a (op b c) = op b (op a c) := by
  rw [← Std.Associative.assoc (op := op), Std.Commutative.comm (op := op) a b,
    Std.Associative.assoc (op := op)]

/-- Use `proveACPerm` (explicit permutation proofs) instead of the reflection-based
`Lean.Meta.AC` in `ecancel`/`solveSepEq`; `Lean.Meta.AC` stays as the fallback. Set it to
`false` to diagnose with the old path. -/
register_option kraken.sepAC : Bool := {
  defValue := true
  descr := "solveSepEq: prove AC equalities by explicit permutation (kernel-cheap) instead of Lean.Meta.AC"
}

initialize registerTraceClass `kraken.sepAC

/-- One message per `proveSeqEq` call where `proveACPerm` failed and `Lean.Meta.AC` was
used instead (enable with `set_option trace.kraken.sepAC.fallback true`, or tree-wide with
`-Dweak.trace.kraken.sepAC.fallback=true`). -/
initialize registerTraceClass `kraken.sepAC.fallback

/-- The operator and the instances the proof is stated with. -/
structure Ctx where
  α : Expr
  u : Level
  /-- The operator, the head constant applied to its common prefix of arguments. -/
  op : Expr
  head : Name
  emp : Name
  assocInst : Expr
  commInst : Expr

/-- A right comb `l₀ ⋆ (l₁ ⋆ (… ⋆ lₙ))` (`e`) with its leaves; `leaves = []` means `e` is a
unit. -/
structure NF where
  e : Expr
  leaves : List Expr

abbrev M := ReaderT Ctx (StateRefT (Std.HashMap Expr Expr) MetaM)

section
variable (c : Ctx)

def mkOp (a b : Expr) : Expr := mkApp2 c.op a b

/-- `a = b`, `b = d` ⊢ `a = d`; `none` stands for `rfl`. -/
def trans (a b d : Expr) : Option Expr → Option Expr → Option Expr
  | none, q => q
  | p, none => p
  | some p, some q => some (mkApp6 (mkConst ``Eq.trans [c.u]) c.α a b d p q)

def symm (a b : Expr) : Option Expr → Option Expr
  | none => none
  | some p => some (mkApp4 (mkConst ``Eq.symm [c.u]) c.α a b p)

/-- `x = y` ⊢ `a ⋆ x = a ⋆ y`. -/
def congrR (a x y : Expr) : Option Expr → Option Expr
  | none => none
  | some p => some (mkApp6 (mkConst ``congrArg [c.u, c.u]) c.α c.α x y (mkApp c.op a) p)

/-- `(a ⋆ b) ⋆ d = a ⋆ (b ⋆ d)` -/
def assoc (a b d : Expr) : Expr :=
  mkApp6 (mkConst ``Std.Associative.assoc [c.u]) c.α c.op c.assocInst a b d

/-- `a ⋆ b = b ⋆ a` -/
def comm (a b : Expr) : Expr :=
  mkApp5 (mkConst ``Std.Commutative.comm [c.u]) c.α c.op c.commInst a b

/-- `a ⋆ (b ⋆ d) = b ⋆ (a ⋆ d)` -/
def leftComm (a b d : Expr) : Expr :=
  mkAppN (mkConst ``left_comm [c.u]) #[c.α, c.op, c.assocInst, c.commInst, a, b, d]

end

/-- Does a node's operator agree with the context's, up to its proof arguments (instances
such as `EquivBEq`/`LawfulHashable` are proved by different terms in different places; the
kernel identifies them by proof irrelevance)? -/
def sameOp (op e : Expr) : MetaM Bool := do
  let n := e.getAppNumArgs
  unless e.getAppFn == op.getAppFn && op.getAppNumArgs + 2 == n do return false
  let opArgs := op.getAppArgs
  for i in [0:n - 2] do
    let x := opArgs[i]!
    let y := e.getArg! i
    unless x == y do
      unless (← isProof x) && (← isProof y) do return false
  return true

def isSep (e : Expr) : M (Option (Expr × Expr)) := do
  let c ← read
  unless e.getAppFn.constName? == some c.head do return none
  unless ← sameOp c.op e do
    throwError "sepAC: operator spelled differently:{indentExpr (e.appFn!.appFn!)}\nvs{indentExpr c.op}"
  return some (e.appFn!.appArg!, e.appArg!)

def isEmp (e : Expr) : M Bool := do
  return e.getAppFn.constName? == some (← read).emp

/-- The `LawfulIdentity op e` instance, cached per unit spelling. -/
def idInst (e : Expr) : M Expr := do
  if let some i := (← get).get? e then return i
  let c ← read
  let some i ← synthInstance? (mkApp3 (mkConst ``Std.LawfulIdentity [c.u]) c.α c.op e)
    | throwError "sepAC: no LawfulIdentity instance"
  modify (·.insert e i)
  return i

/-- `e ⋆ a = a` for a unit `e`. -/
def leftId (e a : Expr) : M Expr := do
  let c ← read
  let i ← idInst e
  return mkApp6 (mkConst ``Std.LawfulLeftIdentity.left_id [c.u, c.u]) c.α c.α c.op e
    (mkApp4 (mkConst ``Std.LawfulIdentity.toLawfulLeftIdentity [c.u]) c.α c.op e i) a

/-- `a ⋆ e = a` for a unit `e`. -/
def rightId (e a : Expr) : M Expr := do
  let c ← read
  let i ← idInst e
  return mkApp6 (mkConst ``Std.LawfulRightIdentity.right_id [c.u, c.u]) c.α c.α c.op e
    (mkApp4 (mkConst ``Std.LawfulIdentity.toLawfulRightIdentity [c.u]) c.α c.op e i) a

/-- Flatten `t` onto the comb `acc` (never a unit): returns the comb `N` and a proof of
`t = N.e` (no `acc`) or `t ⋆ acc.e = N.e`. -/
partial def norm (t : Expr) (acc : Option NF) : M (NF × Option Expr) := do
  let c ← read
  if let some (a, b) ← isSep t then
    match acc with
    | none =>
      let (nb, pb) ← norm b none
      -- `a ⋆ b = a ⋆ nb`
      let p1 := congrR c a b nb.e pb
      if nb.leaves.isEmpty then
        -- `a ⋆ nb = a`, then `a = na`
        let p2 ← rightId nb.e a
        let (na, pa) ← norm a none
        let p := trans c (mkOp c a b) (mkOp c a nb.e) na.e p1 (trans c (mkOp c a nb.e) a na.e (some p2) pa)
        return (na, p)
      else
        let (na, pa) ← norm a (some nb)
        return (na, trans c (mkOp c a b) (mkOp c a nb.e) na.e p1 pa)
    | some x =>
      -- `(a ⋆ b) ⋆ x = a ⋆ (b ⋆ x) = a ⋆ nb = na`
      let p1 := assoc c a b x.e
      let (nb, pb) ← norm b (some x)
      let p2 := congrR c a (mkOp c b x.e) nb.e pb
      let (na, pa) ← norm a (some nb)
      let lhs := mkOp c (mkOp c a b) x.e
      let mid1 := mkOp c a (mkOp c b x.e)
      let mid2 := mkOp c a nb.e
      return (na, trans c lhs mid1 na.e (some p1) (trans c mid1 mid2 na.e p2 pa))
  else if ← isEmp t then
    match acc with
    | none => return ({ e := t, leaves := [] }, none)
    | some x => return (x, some (← leftId t x.e))
  else
    match acc with
    | none => return ({ e := t, leaves := [t] }, none)
    | some x => return ({ e := mkOp c t x.e, leaves := t :: x.leaves }, none)

/-- For a comb `l` (≥ 2 leaves) and `k < l.leaves.length`, `k > 0`: the comb `l'` of the other
leaves and a proof of `l.e = l[k] ⋆ l'.e`. -/
partial def moveFront (l : NF) (k : Nat) : M (NF × Option Expr) := do
  let c ← read
  match l.leaves with
  | r0 :: rs@(_ :: _) =>
    if k == 0 then
      let some (_, rest) ← isSep l.e | throwError "sepAC: moveFront"
      return ({ e := rest, leaves := rs }, none)
    let some (_, rest) ← isSep l.e | throwError "sepAC: moveFront"
    match rs with
    | [r1] =>
      -- `r0 ⋆ r1 = r1 ⋆ r0`
      return ({ e := r0, leaves := [r0] }, some (comm c r0 r1))
    | _ =>
      let t := rs[k - 1]!
      let (r', p1) ← moveFront { e := rest, leaves := rs } (k - 1)
      -- `r0 ⋆ rest = r0 ⋆ (t ⋆ r'.e) = t ⋆ (r0 ⋆ r'.e)`
      let mid := mkOp c r0 (mkOp c t r'.e)
      let p := trans c l.e mid (mkOp c t (mkOp c r0 r'.e)) (congrR c r0 rest (mkOp c t r'.e) p1)
        (some (leftComm c r0 t r'.e))
      return ({ e := mkOp c r0 r'.e, leaves := r0 :: r'.leaves }, p)
  | _ => throwError "sepAC: moveFront on a short comb"

/-- A proof of `l.e = t.e` for combs with the same leaves up to permutation. -/
partial def perm (l t : NF) : M (Option Expr) := do
  let c ← read
  match t.leaves with
  | [] | [_] =>
    unless l.e == t.e do throwError "sepAC: leaves differ"
    return none
  | x :: _ =>
    let some k := l.leaves.idxOf? x | throwError "sepAC: leaf not found"
    let some (_, trest) ← isSep t.e | throwError "sepAC: perm"
    let (l', p1) ← if k == 0 then
        let some (_, lrest) ← isSep l.e | throwError "sepAC: perm"
        pure ({ e := lrest, leaves := l.leaves.tail }, none)
      else moveFront l k
    let p2 ← perm l' { e := trest, leaves := t.leaves.tail }
    let mid := mkOp c x l'.e
    return trans c l.e mid t.e p1 (congrR c x l'.e trest p2)

/-- The number of `left_comm` steps of `perm l t`. -/
def permCost (l t : List Expr) : Nat := Id.run do
  let mut l := l
  let mut n := 0
  for x in t do
    match l.idxOf? x with
    | some k => n := n + k; l := l.eraseIdx k
    | none => return 0
  return n

/-- Prove `lhs = rhs` for trees over the operator `head` (with unit `emp`) whose leaves agree
up to permutation (syntactically). Returns `none` when the trees are not of that shape or the
instances are missing. -/
def proveACPerm (head emp : Name) (lhs rhs : Expr) (rethrow := false) : MetaM (Option Expr) := do
  -- the operator: a sep node's head with its prefix
  let rec findOp (e : Expr) : Option Expr :=
    if e.getAppFn.constName? == some head && e.getAppNumArgs ≥ 2 then
      some (mkAppN e.getAppFn (e.getAppArgs.extract 0 (e.getAppNumArgs - 2)))
    else none
  if lhs == rhs then return some (← mkEqRefl lhs)
  let some op := findOp lhs <|> findOp rhs
    | trace[kraken.sepAC] "no operator in {lhs} = {rhs}"; return none
  let α ← inferType lhs
  let u ← getLevel α
  let some assocInst ← synthInstance? (mkApp2 (mkConst ``Std.Associative [u]) α op)
    | trace[kraken.sepAC] "no Associative instance for {op}"; return none
  let some commInst ← synthInstance? (mkApp2 (mkConst ``Std.Commutative [u]) α op)
    | trace[kraken.sepAC] "no Commutative instance for {op}"; return none
  let c : Ctx := { α, u, op, head, emp, assocInst, commInst }
  let go : M (Option Expr) := do
    let (nl, pl) ← norm lhs none
    let (nr, pr) ← norm rhs none
    unless nl.leaves.length == nr.leaves.length do throwError "sepAC: leaf counts differ"
    let pp ← if permCost nr.leaves nl.leaves < permCost nl.leaves nr.leaves then
        pure (symm c nr.e nl.e (← perm nr nl))
      else perm nl nr
    let p := trans c lhs nl.e rhs pl (trans c nl.e nr.e rhs pp (symm c rhs nr.e pr))
    return some (p.getD (mkApp2 (mkConst ``Eq.refl [c.u]) α lhs))
  try
    let (p, _) ← (go.run c).run {}
    trace[kraken.sepAC] "proved"
    return p
  catch e =>
    trace[kraken.sepAC] "failed: {e.toMessageData}"
    if rethrow then throw e else return none

end Kraken.Tactic.SepAC

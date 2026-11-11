/-
`kfold`: fold a verification condition along its state chain in one pass, and
the rewrite set `vcgen simplifying_assumptions` normalizes each state literal
with as it is produced.

The specs of `Kraken/Specs.lean` leave a program's state chain as nested record
literals. Since `Sym.preprocessMVar` makes every term pointer-canonical, the
`let`-declarations and equations the goal carries form a substitution keyed by
pointer, and looking one up is a single hash probe. `Sym.Simp` then expands each
state exactly once as it traverses the goal bottom-up, caching by pointer, and
collapses the value on the spot.
-/
import Lean
import Kraken.Specs
import Kraken.StateSimp
import KrakenTactics.ClearDead
import Std.Tactic.BVDecide

open Lean Meta Elab Tactic Sym Sym.Simp

namespace Kraken.Fold

/-- Reassociate a literal-prefixed sum so the two literals become adjacent.

A simproc rather than a rewrite rule because reassociation is an
AC-permutation, which the rewriter only applies when it decreases the term
order; here it always pays, since `evalGround` collapses the pair at once. -/
def collapseAdd : Simproc := fun e => do
  let_expr HAdd.hAdd _ _ _ _ a rest := e | return .rfl
  let_expr HAdd.hAdd _ _ _ _ b c := rest | return .rfl
  let some _ ← getBitVecValue? a | return .rfl
  let some _ ← getBitVecValue? b | return .rfl
  let proof ← mkAppM ``add_assoc_rev #[a, b, c]
  let e' ← Sym.share (← mkAdd (← mkAdd a b) c)
  return .step e' proof

/-- Decide an equality between two constructors, so that `Sym`'s own
`simpIte` sees a condition that became `True`/`False` and rewrites the
conditional with its `ite_cond_eq_true`/`ite_cond_eq_false` proof term. -/
def reduceCtorEq : Simproc := fun e => do
  let_expr Eq _ l r := e | return .rfl
  unless l.isConst && r.isConst do return .rfl
  unless (← isConstructorApp l) && (← isConstructorApp r) do return .rfl
  -- Return the shared `True`/`False`: `simpIte` tests them with pointer
  -- equality, so a freshly built constant leaves the conditional standing.
  if l == r then
    return .step (← getTrueExpr) (← mkAppM ``eq_self #[l])
  else
    -- `noConfusion` derives the disequality structurally. Deciding it instead
    -- would make the kernel evaluate the `Decidable` instance to check the
    -- proof, which is the work this is meant to avoid.
    let hne ← withLocalDeclD `h e fun h => do
      mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h)
    return .step (← getFalseExpr) (← mkAppM ``eq_false #[hne])

/-- Substitution built from the goal's `let`-declarations and equations, keyed
by pointer. -/
abbrev SubstEnv := Lean.PHashMap ExprPtr (Expr × Expr)

/-- Rewrite a state or state component to its defining value in one hash probe. -/
def substSimproc (env : SubstEnv) : Simproc := fun e => do
  match env.find? { expr := e } with
  | some (rhs, h) => return .step rhs h
  | none => return .rfl

/-- Collect the substitution sources in declaration order: a `let`-declaration
contributes its variable and value, an equation hypothesis its two sides. -/
def collectDefs (mvarId : MVarId) : SymM (Array (Expr × Expr × Expr)) := mvarId.withContext do
  let mut defs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some v := d.value? then
      defs := defs.push (d.toExpr, v, ← Sym.mkEqRefl d.toExpr)
    else if let some (_, lhs, rhs) := d.type.eq? then
      defs := defs.push (lhs, rhs, d.toExpr)
  return defs

/--
Fold the chain component by component, asserting each folded equation as a
hypothesis.

Each step's right-hand side mentions the previous state twice (as the record it
updates and under the read it performs), so inlining the derived proof at its
use sites doubles the proof tree per instruction: the certificate's DAG stays
linear while its tree is 2^n, and the kernel pays in between because its
instantiations produce fresh, unshared copies. Asserting `s_k.regs = v_k` into
the context makes every later use an atomic fvar reference: each proof appears
once, and sharing goes through the local context, which the kernel respects.
-/
def foldGoal (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let mut mvarId ← preprocessMVar mvarId
  let defs ← collectDefs mvarId
  let mut thms : Theorems := {}
  for n in lemmaNames do
    thms := thms.insert (← mkTheoremFromDecl n)
  let mkMethods (env : SubstEnv) : Methods :=
    { pre := simpControl
      post := substSimproc env >> collapseAdd >> reduceCtorEq >> evalGround >> thms.rewrite }
  let mut values : SubstEnv := {}
  let mut state : Sym.Simp.State := {}
  let mut nStep := 0
  for (lhs, rhs, h) in defs do
    let (r, state') ← SimpM.run (Sym.Simp.simp rhs) (mkMethods values) { maxSteps := 100000 } state
    state := state'
    match r with
    | .rfl .. =>
      -- The definition is already in folded form; its fvar is the shared proof.
      values := values.insert { expr := lhs } (rhs, h)
    | .step rhs' hr .. =>
      nStep := nStep + 1
      let prf ← Sym.Simp.mkEqTrans lhs rhs h rhs' hr
      let ty ← Sym.share (← mkEq lhs rhs')
      -- `define`, not `assert`: an asserted hypothesis becomes `?goal prf`, and
      -- instantiating that metavariable beta-reduces, splicing `prf` back into
      -- every use site. A `let` survives instantiation, so the proof appears
      -- once and uses stay atomic.
      let mvarId' ← mvarId.define ((`hfold).appendIndexAfter nStep) ty prf
      let (fvar, mvarId'') ← mvarId'.intro1P
      mvarId := mvarId''
      values := values.insert { expr := lhs } (rhs', .fvar fvar)
  let target ← mvarId.withContext do instantiateMVars (← mvarId.getType)
  let (result, _) ← SimpM.run (Sym.Simp.simp target) (mkMethods values) { maxSteps := 1000000 } state
  match ← result.toSimpGoalResult mvarId with
  | .closed => return none
  | .goal mvarId' => return some mvarId'
  | .noProgress => return some mvarId

end Kraken.Fold

/-- Fold a verification condition along its state chain. -/
elab "kfold" : tactic => liftMetaTactic1 Kraken.Fold.foldGoal

/-- Fold a verification condition, drop what it consumed, and decide what is
left. -/
macro "kfold_discharge" : tactic => `(tactic| (kfold <;> clear_dead <;> bv_decide))

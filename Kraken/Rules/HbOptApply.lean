import Kraken.Rules.SepStep

/-!
# Goal-shape guards for generated block proofs

The `ff_aac_sbr_apply` block proofs (`Sbr/Apply/*.lean`) run closers under
`all_goals try (…)` over every verification goal of a block. A step such as
`revert ld; sep_mem hm` does its work (normalising the ~150-cell memory fact) even in goals
where it cannot matter. The guard fails fast in such goals. It only fails or succeeds: it
never changes a goal.
-/

namespace Kraken.HbOpt

open Lean Elab Tactic Meta

/-- `hb_used h` for `h : lhs = rhs`: succeed iff some free variable of `rhs` occurs in the
goal or in another hypothesis, i.e. rewriting with `h` can matter. A load hypothesis
`ld : loadInt m a n = some v` whose `v` occurs nowhere else needs no `sep_mem` step. -/
elab "hb_used " h:ident : tactic => withMainContext do
  let fv ← getFVarId h
  let ty ← instantiateMVars (← fv.getType)
  let some (_, _, rhs) := ty.consumeMData.eq? | return
  let vs := (collectFVars {} rhs).fvarIds
  if vs.isEmpty then return
  let used (e : Expr) : Bool := (e.find? fun x => x.isFVar && vs.contains x.fvarId!).isSome
  if used (← instantiateMVars (← getMainTarget)) then return
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.fvarId == fv || vs.contains d.fvarId then continue
    if used (← instantiateMVars d.type) then return
    if let some v := d.value? then
      if used (← instantiateMVars v) then return
  throwError "hb_used: {h.getId} is not used"

end Kraken.HbOpt

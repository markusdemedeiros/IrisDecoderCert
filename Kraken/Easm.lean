/-
The `easm` grind-mode tactic: discharge a `Mem.loadInt … = some ?i` side goal by
reading the value off the internalized local context.

`vcgen` applies the memory primitive specs with an undetermined witness `?i`,
emitting a side goal `lhs = some ?i` (an equality with an assignable metavariable
on one side). Two discharge paths run in order:

* simp path: read-over-write projections plus the local equations reduce the load
  term to `some V` in `MetaM`, off the session, and assign `?i := V`. A
  bitvector-computed address (a stack slot `rsp - 8`) reduces here.
* E-graph path: the load term is shared and canonicalized into the session's
  E-graph state (`Grind.preprocessLight`) and internalized; congruence closure
  over the internalized `h_load` facts and state equations puts a
  constructor-headed member `some V` into its equivalence class. `?i := V` by
  definitional unification; the goal closes by the E-graph proof (`mkEqProof`).
  An indexed address whose base a preceding `lea` overwrote canonicalizes here.

The simp path runs first because it leaves the session untouched, so its result
survives the metacontext `sym` restores; internalizing a bitvector address into
the E-graph instead drives the session inconsistent and leaves it so. The
assignment is visible to the sibling continuation VC, which shares the
metavariable. The `Kraken.easm` trace class reports which path closed each goal.
-/
import Kraken.X64.OmniSemantics
import Kraken.Specs

open Lean Meta
open Lean.Meta.Grind
open Lean.Elab.Tactic.Grind

initialize Lean.registerTraceClass `Kraken.easm

namespace Kraken

/-- Read-over-write projections and the address/data-memory reductions that
`easm` uses to expose the `Mem.loadInt`/`Mem.storeInt` skeleton of the queried
side before the `h_load` facts fire. -/
private def projLemmas : List Name :=
  [``MachineData.dmem_setReg, ``MachineData.regs_setReg,
   ``MachineData.status_setReg, ``MachineData.zmms_setReg, ``MachineData.dmem_mk,
   ``MachineData.regs_mk, ``MachineData.status_mk, ``MachineData.zmms_mk,
   ``Sys.machine_mk, ``Sys.device_mk]

/-- Effective-address canonicalization used in the simp path's second pass:
unfold `AddrExpr.interp` to its base/index/displacement arithmetic, resolve
register reads over writes, and push the `UInt64`/`BitVec`/`Int64` coercions, so
an indexed load address (whose base register a preceding `lea` overwrote) matches
the separation-derived address. -/
private def addrUnfolds : List Name :=
  [``AddrExpr.interp64, ``AddrExpr.interp, ``BitVec.toAddressSize, ``ConstExpr.interp, ``BitVec.take, ``Width.bytes]

/-- Add a hypothesis to a simp set, splitting a conjunction into its conjuncts so
each atomic equality becomes its own rewrite rule (a state precondition like
`env = env₀ ∧ rip = 0 ∧ sd = s₀` reaches `easm` as one hypothesis otherwise). -/
private partial def addHypSplit (thms : SimpTheorems) (proof ty : Expr) : MetaM SimpTheorems := do
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let thms ← addHypSplit thms (← mkAppM ``And.left #[proof]) a
    addHypSplit thms (← mkAppM ``And.right #[proof]) b
  else
    let fresh ← mkFreshId
    let origin := match proof with | .fvar fid => .fvar fid | _ => .other fresh
    try thms.add origin #[] proof catch _ => pure thms
private def addrLemmas : List Name :=
  [``Reg64s.get64_set64, ``Reg64s.get_low64, ``Reg64s.set_low64,
   -- Per-field reads over `set64`, so an address that unfolds `get64` to a named
   -- field (`.rsp`, `.rbx`, …) still resolves the read over intervening writes.
   ``Reg64s.rax_set64, ``Reg64s.rbx_set64, ``Reg64s.rcx_set64, ``Reg64s.rdx_set64,
   ``Reg64s.rsi_set64, ``Reg64s.rdi_set64, ``Reg64s.rsp_set64, ``Reg64s.rbp_set64,
   ``Reg64s.r8_set64, ``Reg64s.r9_set64, ``Reg64s.r10_set64, ``Reg64s.r11_set64,
   ``Reg64s.r12_set64, ``Reg64s.r13_set64, ``Reg64s.r14_set64, ``Reg64s.r15_set64,
   ``BitVec.signed_eq,
   ``Int64.toBitVec_lit, ``BitVec.ofInt_add, ``BitVec.ofInt_mul, ``BitVec.ofInt_toInt,
   ``BitVec.ofInt_toInt_int64, ``BitVec.add_zero,
   ``BitVec.ofInt_neg, ``BitVec.ofInt_ofNat, ``UInt64.toBitVec_sub, ``UInt64.toBitVec_ofNat,
   ``UInt64.ofBitVec_toBitVec, ``UInt64.ofBitVec_add, ``UInt64.ofBitVec_sub,
   ``UInt64.ofBitVec_ofNat]

/-- Whether `e` is headed by a constructor or is a literal. -/
private def isCtorHeaded (e : Expr) : MetaM Bool := do
  if e.isLit then return true
  let .const declName _ := e.getAppFn | return false
  return (← getEnv).find? declName |>.any fun
    | .ctorInfo _ => true
    | _ => false

/-- Splits an `lhs = rhs` target into the metavariable-free side (`known`), the
side carrying the assignable metavariable (`query`), and the orientation. -/
private def splitEqTarget? (mvarId : MVarId) : MetaM (Option (Expr × Expr × Bool)) := do
  let target ← instantiateMVars (← mvarId.getType)
  let some (_, lhs, rhs) := target.eq? | return none
  if rhs.hasExprMVar && !lhs.hasExprMVar then return some (lhs, rhs, true)
  else if lhs.hasExprMVar && !rhs.hasExprMVar then return some (rhs, lhs, false)
  else return none

/-- E-graph discharge: share and canonicalize the load term into the session
state, internalize it, and read `some V` off its equivalence class. Returns
`true` on success, having assigned `?i` and closed `mvarId` with the E-graph
congruence proof. -/
private def easmEgraphCore (mvarId : MVarId) : GrindTacticM Bool := mvarId.withContext do
  let some (known, query, knownIsLhs) ← splitEqTarget? mvarId | return false
  unless query.isMVar || (← isCtorHeaded query) do return false
  liftGoalM do
    -- `preprocessLight` runs the entry-point sharing chain (`canon` followed by
    -- `shareCommon`) against the session state, so the term internalized below
    -- is pointer-canonical with every node already in the E-graph.
    let known' ← preprocessLight known
    if (← isTracingEnabledFor `Kraken.easm) then
      let twin? := (← get).getEqcs.flatMap id |>.find? (· == known)
      trace[Kraken.easm] "mechanism: raw internalized={← alreadyInternalized known}, structural twin in egraph={twin?.isSome}, twin pointer-eq raw={(twin?.map (isSameExpr · known)).getD false}, shared pointer-eq raw={isSameExpr known' known}"
    unless (← alreadyInternalized known') do
      internalize known' 0
      processNewFacts
    if (← isInconsistent) then return false
    let cls ← getEqc known'
    let some v ← cls.findM? (fun e =>
      if e.hasExprMVar then pure false else isCtorHeaded e) | return false
    unless ← withAssignableSyntheticOpaque (isDefEq query v) do return false
    let h ← mkEqProof known' v
    let h ← if knownIsLhs then pure h else mkEqSymm h
    -- `known'` is definitionally equal to `known`; the hint retypes the proof at
    -- the goal as stated.
    mvarId.assign (← mkExpectedTypeHint h (← instantiateMVars (← mvarId.getType)))
    trace[Kraken.easm] "egraph: {known'} = {v}"
    return true

/-- simp discharge: reduce the `known` side to a constructor-headed value using
the read-over-write projections and every closed propositional hypothesis.
Returns `true` on success, having assigned `?i` and closed `mvarId`. -/
private def easmCore (mvarId : MVarId) : MetaM Bool := mvarId.withContext do
  let some (known, query, knownIsLhs) ← splitEqTarget? mvarId | return false
  -- Fire only when the metavariable side is constructor-headed (e.g. `some ?i`)
  -- or a bare metavariable. A goal like `<projection with ?i> = 99` is left to the
  -- continuation discharge.
  unless query.isMVar || (← isCtorHeaded query) do return false
  -- Simp set: the read-over-write projections plus every closed propositional
  -- hypothesis. The `h_load` facts rewrite `Mem.loadInt … → some V`; the state
  -- equalities and address bridges align the load's memory and address with them.
  -- The first pass keeps `AddrExpr.interp` folded (matching a folded `h_load`); if
  -- the queried side does not reduce to a value, a second pass canonicalizes the
  -- address so an indexed load matches its separation-derived form.
  let mkThms (thmExtra unfoldExtra : List Name) : MetaM SimpTheorems := do
    let mut thms : SimpTheorems := {}
    for n in projLemmas ++ thmExtra do thms ← thms.addConst n
    for n in unfoldExtra do thms ← thms.addDeclToUnfold n
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        if (← isProp decl.type) && !decl.type.hasExprMVar then
          -- Some hypotheses (e.g. inequalities) are not orientable as simp lemmas;
          -- a conjunction is split so each atomic equality is its own rule.
          thms ← addHypSplit thms (mkFVar decl.fvarId) decl.type
    return thms
  -- `decide := true` settles the `Reg64` equality guards a per-field read over
  -- `set64` leaves behind; the default simprocs (`reduceIte`) then collapse the
  -- resulting `if True/False then …`.
  let cfg : Simp.Config := { decide := true }
  let sprocs ← Simp.getSimprocs
  let ctx1 ← Simp.mkContext cfg (simpTheorems := #[← mkThms [] []]) (congrTheorems := ← getSimpCongrTheorems)
  let mut res := (← Meta.simp known ctx1 (simprocs := #[sprocs])).1
  unless ← isCtorHeaded res.expr do
    let ctx2 ← Simp.mkContext cfg (simpTheorems := #[← mkThms addrLemmas addrUnfolds])
      (congrTheorems := ← getSimpCongrTheorems)
    res := (← Meta.simp known ctx2 (simprocs := #[sprocs])).1
  let knownV := res.expr  -- expected `some V`
  unless ← isCtorHeaded knownV do return false
  -- `hKnown : known = knownV`; `knownV` is constructor-headed, so unifying it with
  -- the query pins the metavariable (`some ?i` ↦ `some V`).
  let hKnown ← res.proof?.getDM (mkEqRefl known)
  unless ← withAssignableSyntheticOpaque (isDefEq query knownV) do return false
  mvarId.assign (← if knownIsLhs then pure hKnown else mkEqSymm hKnown)
  return true

syntax (name := easmStx) "easm" : grind

@[grind_tactic easmStx]
def evalEasm : GrindTactic := fun _stx => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.mvarId.getType)
  -- The simp path is a pure `MetaM` reduction: it never touches the session, so
  -- trying it first is free. The E-graph path internalizes the queried access into
  -- the session to read its class; for a bitvector-computed address (a stack slot
  -- `rsp - 8`) that internalization drives the session inconsistent and leaves it
  -- so, which is why it runs only once simp has not already produced the value.
  let discharge (mv : MVarId) : GrindTacticM Bool := do
    if (← liftMetaM (easmCore mv)) then
      trace[Kraken.easm] "path=simp"
      return true
    if (← easmEgraphCore mv) then
      trace[Kraken.easm] "path=egraph"
      return true
    return false
  -- The store VC may arrive as `(Mem.loadInt … = some ?i) ∧ <continuation>`: split
  -- off the equation, discharge it, and hand the continuation to `finish`.
  if target.isAppOfArity ``And 2 then
    let [gEq, gCont] ← goal.mvarId.apply (mkConst ``And.intro)
      | throwError "easm: unexpected arity splitting the memory conjunction"
    unless ← discharge gEq do
      throwError "easm: could not read the memory value from the local context"
    -- Re-read the main goal: the E-graph path updates the session state.
    let goal ← getMainGoal
    replaceMainGoal [{ goal with mvarId := gCont }]
  else
    unless ← discharge goal.mvarId do
      throwError "easm: goal is not an assignable `_ = some ?i` reducible from the context"
    replaceMainGoal []

end Kraken

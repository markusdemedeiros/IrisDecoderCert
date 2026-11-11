import Kraken.Rules.GenericMem

/-!
# Indirect calls: `call *%r` and `call *d(%b,%i,s)`

Compiled C calls through function pointers: a register (`call *%rax`), a
struct field (`call *0x18(%rdi)`, `call *(%rax)`) or a table slot
(`call *8(%rax,%rcx,8)`). The memory rule here is stated once over the operand
`⟨some (.reg b), idx, .int64 d⟩`, as in `Kraken.Rules.GenericMem`, so it covers
all of these shapes.

The callee is whatever the pointer holds. A direct call has its callee's
`ProcSpec` passed in by the caller (`call_proc_spec_at`). For an indirect call,
the target is known only at run time, so the rule asks of the state that the
target be a procedure with a spec. That is `CallsTo f K s`: some `ProcSpecK`
holds at `f`, and its precondition holds of the pushed state for every return
address with the caller's tail `K` as the continuation. The memory rule also
asks that the 8 bytes of the pointer be readable (they are loaded before the
push), and both rules ask that the stack slot below `rsp` be writable.

The hypothesis-free rules `call_reg_spec` and `call_mem_spec` are `@[spec low]`.
A caller that knows the target's `ProcSpec` passes the `_proc_spec_at` form to
`vcgen [hc]` instead, as for a direct call. Its precondition says the pointer
*is* `f` (`(load a).map toAddr = some f`, the `fnPtr` form of
`IndirectTailCall`) and then reads like `call_proc_spec_at`.
-/

open Kraken MachineWP Std.WP Lean.Order

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

/-- A call to `f` from `s` continues in `K`: `f` is a procedure with a spec
(a `ProcSpecK`), and the spec's precondition holds of the state with the return
address pushed, for any return address, with `K` as the continuation. -/
def MachineWP.CallsTo (f : Int64) (K : MachineData → Prop) (s : MachineData) : Prop :=
  ∃ Spec : Int64 → (MachineData → Prop) → MachineData → Prop,
    cenv.ProcSpecK f Spec ∧ ∀ ra : Int64, Spec ra K (s.pushRa ra)

/-- A call to a procedure by its `ProcSpecK`. -/
theorem MachineWP.CallsTo.of_procSpecK {f : Int64}
    {Spec : Int64 → (MachineData → Prop) → MachineData → Prop} {K : MachineData → Prop}
    {s : MachineData} (hproc : cenv.ProcSpecK f Spec)
    (h : ∀ ra : Int64, Spec ra K (s.pushRa ra)) : MachineWP.CallsTo f K s :=
  ⟨Spec, hproc, h⟩

/-- A call to a procedure by its `ProcSpec`, at the logical variable `x`. -/
theorem MachineWP.CallsTo.of_procSpec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} {f : Int64} (x : α)
    {K : MachineData → Prop} {s : MachineData} (hproc : cenv.ProcSpec f Pre Post)
    (h : ∀ ra : Int64, Pre x ra (s.pushRa ra) ∧ ∀ s', Post x ra (s.pushRa ra) s' → K s') :
    MachineWP.CallsTo f K s :=
  ⟨_, hproc.toK, fun ra => ⟨x, h ra⟩⟩

/-- `call *%r`: a call to the address the register holds. The stack slot below
`rsp` must be writable, and the target must be a procedure whose spec returns
into the tail. -/
@[spec low] theorem MachineWP.call_reg_spec (asz osz : Width) (r : Reg64) :
    ⦃ fun s =>
        ((Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
            Width.W64.bytes).isSome = true)
          ⊓ MachineWP.CallsTo (Int64.ofBitVec (s.regs.get64 r)) (WP.wp p Q E) s ⦄
      (Directive.instr (.regular asz osz (.call (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hmapped, Spec, hproc, hpre⟩ := h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hmapped
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
    simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      Reg64s.get_low64, MachineData.store, hw, Effects.All]
    refine eventually_trans _ _ _ _
      (hproc (pc + Int64.ofNat z) _ (s.pushRa (pc + Int64.ofNat z)) (hpre _)) ?_
    rintro ⟨s', a⟩ ⟨rfl, hpost⟩
    rw [after_instr hseg]
    exact hpost _ hpl'

/-- `call *d(%b,%i,s)` (any index or none, any displacement including `0`): a
call to the address stored at the operand. The 8 bytes must be readable, the
stack slot below `rsp` writable, and the address they hold a procedure whose
spec returns into the tail. -/
@[spec low] theorem MachineWP.call_mem_spec (osz : Width) (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
              Width.W64.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
              MachineWP.CallsTo (Int64.ofBitVec (BitVec.ofInt 64 v)) (WP.wp p Q E) s) ⦄
      (Directive.instr (.regular .W64 osz
          (.call (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hsome, hmapped⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hmapped
    obtain ⟨Spec, hproc, hpre⟩ := hk v hv
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
    simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      MachineData.load, AddrExpr.zeroExtend_interp_base_idx_disp, Width.bytes, hv,
      Effects.All]
    simp only [MachineData.store, hw, Effects.All]
    refine eventually_trans _ _ _ _
      (hproc (pc + Int64.ofNat z) _ (s.pushRa (pc + Int64.ofNat z)) (hpre _)) ?_
    rintro ⟨s', a⟩ ⟨rfl, hpost⟩
    rw [after_instr hseg]
    exact hpost _ hpl'

/-- `call_reg_spec` at a target `f` with a `ProcSpec`, in the form `vcgen [hc]`
steps a call with (compare `call_proc_spec_at`): the register holds `f`. -/
theorem MachineWP.call_reg_proc_spec_at {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (f : Int64)
    (hproc : cenv.ProcSpec f Pre Post) :
    ∀ ⦃asz osz : Width⦄ ⦃r : Reg64⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          Int64.ofBitVec (s.regs.get64 r) = f
          ∧ (∀ ra : Int64, Pre x ra (s.pushRa ra)
            ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz (.call (.reg (.low r .W64)))) :: p)
      ⦃ Q; E ⦄ := by
  intro asz osz r p Q E
  refine Triple.intro fun s h => ?_
  obtain ⟨hf, hP, hmapped⟩ := h
  refine (MachineWP.call_reg_spec asz osz r).le_wp s ?_
  simp only [meet_prop_eq_and]
  exact ⟨hmapped, hf ▸ MachineWP.CallsTo.of_procSpec x hproc hP⟩

/-- `call_mem_spec` at a target `f` with a `ProcSpec`, in the form `vcgen [hc]`
steps a call with (compare `call_proc_spec_at`): the 8 bytes at the operand,
read as an address, are `f`. -/
theorem MachineWP.call_mem_proc_spec_at {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (f : Int64)
    (hproc : cenv.ProcSpec f Pre Post) :
    ∀ ⦃osz : Width⦄ ⦃b : Reg64⦄ ⦃idx : Option AddrIndex⦄ ⦃d : Int64⦄ ⦃p : Program⦄
      ⦃Q : Unit → MachineData → Prop⦄ ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          (Mem.loadInt s.dmem (s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec)
              8).map (fun v => Int64.ofBitVec (BitVec.ofInt 64 v)) = some f
          ∧ (∀ ra : Int64, Pre x ra (s.pushRa ra)
            ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular .W64 osz
            (.call (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
      ⦃ Q; E ⦄ := by
  intro osz b idx d p Q E
  refine Triple.intro fun s h => ?_
  obtain ⟨hf, hP, hmapped⟩ := h
  obtain ⟨v, hv, hvf⟩ := Option.map_eq_some_iff.mp hf
  refine (MachineWP.call_mem_spec osz b idx d).le_wp s ?_
  simp only [meet_prop_eq_and]
  refine ⟨⟨by simp [hv], hmapped⟩, fun v' hv' => ?_⟩
  rw [hv] at hv'
  cases hv'
  exact hvf ▸ MachineWP.CallsTo.of_procSpec x hproc hP

end Specs

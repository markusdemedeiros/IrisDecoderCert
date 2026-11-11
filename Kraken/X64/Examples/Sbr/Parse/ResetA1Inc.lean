import Kraken.Rules.IntMisc

/-!
# `incw d(%rb,%idx)`

The memory form of `inc` at 16 bits (`sbr_reset.L1ec1`: `incw 0x4c1f0(%r12,%rdx,2)`), stated
like `MachineWP.dec_mem_w16_spec` of `Kraken/Rules/IntMisc.lean` and proved the same way. This
is a proved rule over the existing semantics, not a model change.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.Sbr.Parse

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

set_option linter.unusedSimpArgs false in
/-- `incw d(%rb,%idx)`: the word plus one; the carry flag is kept. -/
@[spec low] theorem inc_mem_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let v := a + 1
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := s.status.cf,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                        of := v.signed != a.signed + 1 } }) ⦄
      (Directive.instr (.regular .W64 .W16 (.inc (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    simp only [MachineData.load, MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

end Specs

end Kraken.Examples.Sbr.Parse

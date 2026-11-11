import Kraken.Rules.PackedSse

/-!
# `vmovdqu %xmm, m128` (AVX), `vpshufb sym(%rip), %src1, %dst`

Used by the `f_master` fill loops of `sbr_reset` (`L1e09` .. `L1e90`). Stated like
`MachineWP.movdqu_store_mem_spec` / `MachineWP.vpaddd_load_rip_spec` of
`Kraken/Rules/PackedSse.lean` and proved the same way. Proved rules over the existing semantics,
not model changes.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.Sbr.Parse

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

local macro "mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

set_option linter.unusedSimpArgs false in
/-- `vmovdqu %xmm, m128`: 16 owned bytes, any alignment. -/
@[spec low] theorem a1_vmovdqu_store_mem_spec (x : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
        (.vmovdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hsome, hk⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_here hseg (Or.inl ?_)
  wp_step
  mem_access hv hv
  exact hk _ hpl'

set_option linter.unusedSimpArgs false in
/-- `vpshufb sym(%rip), %src1, %dst`: 16 readable bytes, any alignment. -/
@[spec low] theorem a1_vpshufb_load_rip_spec (dst src1 : AvxReg .W128) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128 BitVec.pshufb128 (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128
        (.vpshufb dst src1 (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hsome, hk⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_here hseg (Or.inl ?_)
  wp_step
  mem_access hv hv
  exact hk v hv _ hpl'

end Specs

end Kraken.Examples.Sbr.Parse

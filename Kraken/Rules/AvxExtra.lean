import Kraken.Rules.PackedSse

/-!
# Rules for the 256-bit VEX forms of `libavutil/x86/float_dsp.asm`

`MachineWP` rules the `float_dsp` routines (`ff_vector_fmul_avx`,
`ff_vector_fmul_add_{avx,fma3}`, `ff_vector_fmul_reverse_{avx,avx2}`) need
beyond `PackedSse.lean`: the 256-bit memory forms of `vmulps` and `vaddps`.
Stated, like `PackedSse.lean`, once over the operand `⟨some (.reg b), idx, .int64 d⟩`;
the proofs are the shared `mem_load` proof of that file, repeated here because
its macros are local.
-/

open Kraken MachineWP Std.WP Lean.Order

set_option linter.unusedSimpArgs false

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

/-- After `wp_step`: unfold the one memory access and discharge its checks. -/
local macro "mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

/-- Proof of a load rule with precondition
`isSome ⊓ (∀ v, load = some v → wp …)`. -/
local macro "mem_load" : tactic =>
  `(tactic| (
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
    exact hk v hv _ hpl'))

/-- Proof of a load rule with precondition
`aligned ⊓ isSome ⊓ (∀ v, load = some v → wp …)`. -/
local macro "mem_load_al" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hal, hsome⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    mem_access hal hv
    exact hk v hv _ hpl'))

/-- Proof of a register rule: the cell computes the stated state and falls
through. -/
local macro "reg_proof" : term =>
  `(fallthrough_spec (fun _ _ _ hP => by
      wp_step
      (try simp only [Reg64s.get_low32, Reg64s.set_low32])
      exact hP))

/-- `vaddps m256, %src1, %dst`: 32 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vaddps256_load_mem_spec (dst src1 : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32add (s.zmms.get src1) (BitVec.ofInt 256 v)) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vaddps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmulps m256, %src1, %dst`: 32 readable bytes, any alignment. -/
@[spec low] theorem MachineWP.vmulps256_load_mem_spec (dst src1 : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) (BitVec.ofInt 256 v)) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmulps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vfmadd132ps m256, %src1, %dst`: 32 readable bytes, any alignment;
`dst := dst * m + src1`, each lane rounded once. -/
@[spec low] theorem MachineWP.vfmadd132ps256_load_mem_spec (dst src1 : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get dst) (BitVec.ofInt 256 v) (s.zmms.get src1)) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vfmadd132ps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpermps m256, %idx, %dst`: 32 readable bytes, any alignment; lane `i` of
`dst` is lane `idx[i] mod 8` of the memory operand. -/
@[spec low] theorem MachineWP.vpermps256_load_mem_spec (dst src1 : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32 (fun i _ => (BitVec.ofInt 256 v).extractLsb' (32 * (i.toNat % 8)) 32) (s.zmms.get src1) (s.zmms.get src1)) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vpermps dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vinsertf128 $imm, m128, %src1, %dst`: 16 readable bytes, any alignment;
`src1` with its 128-bit lane `imm[0]` replaced by the memory operand. -/
@[spec low] theorem MachineWP.vinsertf128_load_mem_spec (dst src1 : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) (imm : UInt8) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (if imm.toNat % 2 = 0 then (s.zmms.get src1).extractLsb' 128 128 ++ BitVec.ofInt 128 v else BitVec.ofInt 128 v ++ (s.zmms.get src1).extractLsb' 0 128) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vinsertf128 dst src1 (.mem ⟨some (.reg b), idx, .int64 d⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vmovaps sym(%rip), %ymm`: 32 readable bytes, 32-byte aligned (the
`pd_reverse` constant of `ff_vector_fmul_reverse_avx2`). -/
@[spec low] theorem MachineWP.vmovaps256_load_rip_spec (y : AvxReg .W256) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 32 a = true) ⊓ ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovaps (.avx y) (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load_al

end Specs

import Kraken.MachineWP
import Kraken.Specs
import Kraken.Rules.GenericMem
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat

/-!
# `sbr_reset`, shard A2: `vcgen` rules missing from `Kraken/Rules`

Rules (`@[spec low]`) for the instructions of A2 that no rule covers: `vcvtss2si`, `vcvtdq2ps`,
`vpminsd`, `vpshufd` (register forms), `vblendps` with a `sym(%rip)` operand and `vpmovsxwd`
with an `m64` operand. Stated exactly as `AvxOperation.interp` computes them and proved like the
rules of `ScalarFloat.lean`/`PackedSse.lean` (one step, reduced; the memory forms by the
`mem_load` proof of `PackedSse.lean`).
-/

open Kraken MachineWP Std.WP Lean.Order

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

local macro "reg_rule" : tactic =>
  `(tactic| exact fallthrough_spec (fun s rng P hP => by
      wp_step
      try simp only [AvxRegOrMem.interpLow, Reg64s.get_low32, Reg64s.set_low32]
      exact hP))

/-- `vcvtss2si %src, %r64`: the low float rounded (current mode) to a 64-bit integer. -/
@[spec low] theorem MachineWP.vcvtss2si_reg64_spec_A2 {w : AvxWidth} (asz : Width) (r : Reg64)
    (src : AvxReg .W128) :
    ⦃ fun s =>
        WP.wp p Q E { s with
          regs := (s.regs.set64 r (BitVec.f32toi64 ((s.zmms.get src).setWidth 32))) } ⦄
      (Directive.instr (.avx asz w (.vcvtss2si (.low r .W64) (.avx src))) :: p)
    ⦃ Q; E ⦄ := by reg_rule

local macro "reg_proof" : term =>
  `(fallthrough_spec (fun _ _ _ hP => by
      wp_step
      (try simp only [Reg64s.get_low32, Reg64s.set_low32])
      exact hP))

/-- After `wp_step`: unfold the one memory access and discharge its checks. -/
local macro "mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

/-- Proof of a load rule with precondition `isSome ⊓ (∀ v, load = some v → wp …)`. -/
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

/-- `vcvtdq2ps %src, %dst` (register form, any width): lanewise `int32 → float`. -/
@[spec low] theorem MachineWP.vcvtdq2ps_reg_spec_A2 {w : AvxWidth} (dst src : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32
        (fun x _ => BitVec.sitof32 x) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vcvtdq2ps dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpminsd %src2, %src1, %dst` (register form, any width): lanewise signed minimum. -/
@[spec low] theorem MachineWP.vpminsd_reg_spec_A2 {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32
        (fun x y => if x.slt y then x else y) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpminsd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vpshufd $imm, %src, %dst` (register form, any width). -/
@[spec low] theorem MachineWP.vpshufd_reg_spec_A2 {w : AvxWidth} (dst src : AvxReg w) (imm : UInt8)
    (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128
        (fun x _ => BitVec.pshufd128 imm x) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vpshufd dst (.avx src) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

/-- `vblendps $imm, sym(%rip), %src1, %dst`: 16 readable bytes at `sym`, any alignment. -/
@[spec low] theorem MachineWP.vblendps_load_rip_spec_A2 (dst src1 : AvxReg .W128) (l : Label)
    (imm : UInt8) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 32
              (fun i x y => if (imm.toNat >>> (i % 8)) % 2 = 1 then y else x)
              (s.zmms.get src1) (BitVec.ofInt 128 v)) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vblendps dst src1
        (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩) imm)) :: p)
    ⦃ Q; E ⦄ := by mem_load

/-- `vpmovsxwd m64, %dst`: 8 readable bytes, any alignment; four sign-extended `int16`s. -/
@[spec low] theorem MachineWP.vpmovsxwd_load_mem_spec_A2 (dst : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set dst (
              ((BitVec.ofInt 64 v).extractLsb' 48 16).signExtend 32
                ++ ((BitVec.ofInt 64 v).extractLsb' 32 16).signExtend 32
                ++ ((BitVec.ofInt 64 v).extractLsb' 16 16).signExtend 32
                ++ ((BitVec.ofInt 64 v).extractLsb' 0 16).signExtend 32) }) ⦄
      (Directive.instr (.avx .W64 .W128 (.vpmovsxwd dst (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_load

end Specs

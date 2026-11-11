import Kraken.Rules.PackedSse

/-!
# `vpinsrw`, `vpaddw` (register forms)

Used by `sbr_reset.L1ed8` (`vpinsrw $0x1,%eax,%xmm0,%xmm0`, `vpaddw %xmm0,%xmm1,%xmm0`). Stated
like `MachineWP.vpinsrd_reg_spec` / `MachineWP.vpaddd_reg_spec` of `Kraken/Rules/PackedSse.lean`
and proved the same way (`fallthrough_spec`). Proved rules over the existing semantics, not model
changes.
-/

open Kraken MachineWP Std.WP Lean.Order

namespace Kraken.Examples.Sbr.Parse

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

set_option linter.unusedSimpArgs false in
/-- `vpinsrw $imm, %r32, %src1, %dst`: word `imm % 8` of `src1` replaced by the low word of `r`. -/
@[spec low] theorem vpinsrw_reg_spec {w : AvxWidth} (dst src1 : AvxReg .W128) (r : Reg64)
    (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOpIdx 16 (fun i x _ => if i = imm.toNat % 8 then ((s.regs.get64 r).setWidth 32).setWidth 16 else x) (s.zmms.get src1) (s.zmms.get src1)) } ⦄
      (Directive.instr (.avx asz w (.vpinsrw dst src1 (.low r .W32) imm)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun _ _ _ hP => by
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32])
    exact hP)

set_option linter.unusedSimpArgs false in
/-- `vpaddw %src2, %src1, %dst` (register form, any width): lanewise 16-bit sums. -/
@[spec low] theorem vpaddw_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 16 (· + ·) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpaddw dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun _ _ _ hP => by
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    exact hP)

end Specs

end Kraken.Examples.Sbr.Parse

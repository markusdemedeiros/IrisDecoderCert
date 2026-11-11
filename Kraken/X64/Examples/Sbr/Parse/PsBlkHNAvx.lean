import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib2
import Kraken.Rules.PackedSse

/-!
# AVX register/store rules for the PS vectorized fixed-border loop (`0x69c`, `0x6d0`)

`vpshufd`, `vpcmpeqd`, `vpsrld %xmm`, `vpmovzxdq` (register forms) and `vmovdqu %xmm, m128`,
proved as in `Kraken.Rules.PackedSse` (whose proof macros are `local`).
-/

open Kraken MachineWP Std.WP Lean.Order
open Kraken.SysV Mem Kraken.X64.Parser Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option linter.unusedSimpArgs false

namespace Kraken.Examples.Sbr.Ps

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

local macro "reg_proof" : term =>
  `(fallthrough_spec (fun _ _ _ hP => by
      wp_step
      (try simp only [Reg64s.get_low32, Reg64s.set_low32])
      exact hP))

theorem hn_vpshufd_spec {w : AvxWidth} (dst src : AvxReg w) (imm : UInt8) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 128
        (fun x _ => BitVec.pshufd128 imm x) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vpshufd dst (.avx src) imm)) :: p)
    ⦃ Q; E ⦄ := reg_proof

theorem hn_vpcmpeqd_spec {w : AvxWidth} (dst src1 src2 : AvxReg w) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32
        (fun x y => if x = y then BitVec.allOnes 32 else 0#32) (s.zmms.get src1) (s.zmms.get src2)) } ⦄
      (Directive.instr (.avx asz w (.vpcmpeqd dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

theorem hn_vpsrldx_spec {w : AvxWidth} (dst src : AvxReg w) (count : AvxReg .W128) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst (BitVec.packedBinOp 32
        (fun x _ => if ((s.zmms.get count).extractLsb' 0 64).toNat > 31 then 0#32
          else x >>> ((s.zmms.get count).extractLsb' 0 64).toNat) (s.zmms.get src) (s.zmms.get src)) } ⦄
      (Directive.instr (.avx asz w (.vpsrldx dst src count)) :: p)
    ⦃ Q; E ⦄ := reg_proof

theorem hn_vpmovzxdq_spec (dst : AvxReg .W128) (src : AvxReg .W128) (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.set dst ((((s.zmms.get src).setWidth 64).dw 1).zeroExtend 64 ++ (((s.zmms.get src).setWidth 64).dw 0).zeroExtend 64) } ⦄
      (Directive.instr (.avx asz .W128 (.vpmovzxdq dst (.avx src))) :: p)
    ⦃ Q; E ⦄ := reg_proof

end Specs

section Consts
variable [CodeEnv]

theorem hn_eq_t {A X : Mem 64 → Prop} : A ⋆ X = X ⋆ A := Std.ExtHashMap.sep_comm _ _

theorem Fr_lcpi28 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (lab "LCPI0_28") 16
      = some (Int.ofBytes [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact loadInt_sep _ _ 16 _ m (focus (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r eq_h))))))) hF)
    rfl (by omega)

theorem Fr_lcpi30 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (lab "LCPI0_30") 4 = some (Int.ofBytes [4, 0, 0, 0]) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact loadInt_sep _ _ 4 _ m (focus (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r hn_eq_t))))))) hF)
    rfl (by omega)

end Consts

/-! ## Packed-lane facts -/

theorem hn_pb_diag {c : Nat} (op : BitVec c → BitVec c → BitVec c) (k : BitVec c)
    (hk : ∀ x, op x x = k) (hc : 0 < c) : ∀ (w : Nat) (_ : c ∣ w) (a b : BitVec w),
    BitVec.packedBinOp c op a a = BitVec.packedBinOp c op b b
  | w, hw, a, b => by
    rw [BitVec.packedBinOp, BitVec.packedBinOp]
    split
    · next h =>
      have : w = 0 := by
        rcases h with h | h
        · omega
        · exact Nat.eq_zero_of_dvd_of_lt hw h
      subst this
      exact Subsingleton.elim _ _
    · next h =>
      simp only [hk]
      rw [hn_pb_diag op k hk hc (w - c) (Nat.dvd_sub hw (Nat.dvd_refl c)) (a.drop c) (b.drop c)]
termination_by w => w
decreasing_by omega
/-- `vpcmpeqd %x,%x,%x` sets all ones. -/
theorem hn_cmpeq_self (a : BitVec 128) :
    BitVec.packedBinOp 32 (fun x y => if x = y then BitVec.allOnes 32 else 0#32) a a
      = BitVec.allOnes 128 := by
  rw [hn_pb_diag _ (BitVec.allOnes 32) (fun x => by simp) (by omega) 128 (by decide) a 0#128]
  simp [BitVec.packedBinOp] <;> first | rfl | decide

end Kraken.Examples.Sbr.Ps

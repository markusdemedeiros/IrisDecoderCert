import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: the reader copy and the header bit
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `bits_left` stored, the reader copy loaded, the first byte read. -/
theorem blk_L11 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L11" := by
  cfg_block
  measure_hb "L11"
    intro n
    simp only [tab_L11, var_L11, tab_L2c, var_L2c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hsp, hbp, ⟨hdi, hsi, hdx⟩, hcx, f, hf, hm⟩, hn⟩ := hs₀
    have hi : x.idx.toNat ≤ x.p8.toNat := hC.2.2.1
    have hp : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-44)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x74 := by
      rw [hbp, show Int64.toBitVec (-44) = BitVec.ofNat 64 (2 ^ 64 - 44) from rfl]
      simp only [rsp0]; bv_omega
    have hS' := Fr_f_store hm hf 0x74 4 (by omega) ((t₀.regs.get64 .rcx).setWidth 32).toInt
    have hL0 := Fr_f_load hm hf 0x74 4 (by omega)
    have hL1 := Fr_gb_idx hS'
    have hL2 := Fr_gb_buf hS'
    have hL3 := Fr_gb_p8 hS'
    simp only [arg1, ← hsi, ← hcx] at hL1 hL2 hL3 hS'
    have hB := Fr_buf_load hS' ((x.idx >>> 3).setWidth 64) 1 (by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]; have := x.idx.isLt; omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals simp only [e1] at *
    all_goals simp only [hL0, hL1, hL2, hL3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [ofInt_toBytes32, ofInt_toBytes64, BitVec.setWidth_32_64_32, AddrIndex.offset64,
      Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
    all_goals try exact hB
    all_goals refine ⟨?_, by var_step⟩
    unfold q2c
    refine ⟨hC, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, _, ?_, ?_, hS'⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
    all_goals try assumption
    all_goals try rfl
    · rw [wr_length f 116 4 _ (by omega), hf]
    · rw [rd_wr_same _ _ _ _ (by omega), ofInt_toBytes32, hcx]

end Kraken.Examples.Sbr.Ps

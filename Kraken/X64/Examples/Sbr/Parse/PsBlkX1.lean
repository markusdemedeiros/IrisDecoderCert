import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
theorem blk_cba (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lcba" := by
  cfg_block
  measure_hb "Lcba"
    simp only [tab_Lcba, tab_Lcc8, var_Lcba, var_Lcc8]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hCm, hR, hI, hS, h1c, h10, hG⟩, hn⟩ := hs₀
    have hCm' := hCm
    obtain ⟨hC, ⟨hsp, hbp, hfl, hP, hB1⟩, hm⟩ := hCm
    have hcl : c.length = 764 := hP.1
    have hps : BitVec.ofInt 64 (rd f 0x68 8) = arg2 t₀ := hS.2.2.1
    have l1 := Fr_f_load hm hfl 0x68 8 (by omega)
    have l2 := Fr_c_load hm hcl 0x20 4 (by omega)
    have e1 : s₀.regs.get64 .rbp + 0 + (-56 : Int64).toBitVec
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x68 := by
      rw [hbp, Int64.toBitVec_neg_ofNat_norm]; bv_omega
    rw [← e1] at l1
    have e2 : arg2 t₀ + (32 : Int64).toBitVec = arg2 t₀ + BitVec.ofNat 64 0x20 := rfl
    rw [← e2] at l2
    vcgen
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L1063") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L1063 _ _ _ _ _ _).mpr ?_
        rename_i v1 hv1 v2 hv2 _
        subst_vars
        simp only [AddrIndex.offset64_none] at hv1
        rw [l1, Option.some.injEq] at hv1
        subst hv1
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        exact ⟨c, f, ⟨hC, ⟨hsp, hbp, hfl, hP, hB1⟩, hm⟩, hps, hI, hS, h1c, h10, hG⟩
      · rw [var_L1063]
        subst hn
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc1 =>
      subst_vars
      simp only [AddrIndex.offset64_none, l1, Option.isSome_some]
    case vc2 =>
      rename_i v1 hv1
      subst_vars
      simp only [AddrIndex.offset64_none] at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      simp only [Reg64s.get64_set64, ite_true]
      rw [hps, l2]; rfl
    case vc4 =>
      rename_i v1 hv1 v2 hv2 _
      subst_vars
      simp only [AddrIndex.offset64_none] at hv1
      rw [l1, Option.some.injEq] at hv1
      subst hv1
      refine ⟨?_, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      simp only [qcc8, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      exact ⟨c, f, ⟨⟨hC, ⟨hsp, hbp, hfl, hP, hB1⟩, hm⟩, hR, hS, h1c, hG⟩, hI, h10, hps⟩

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps
variable [CodeEnv]
open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
theorem blk_cc8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lcc8" := by
  cfg_block
  measure_hb "Lcc8"
    simp only [tab_Lcc8, tab_Lce0, var_Lcc8, var_Lce0]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩, hI, h10, hbx⟩, hn⟩ := hs₀
    have hoff := xrd_off ((s₀.regs.get64 .r8).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm _ 4 hoff
    have hXB : XB k Ext x ra t₀ s₀ c f := ⟨⟨hC, hB, hm⟩, ⟨hr13, hr12⟩, hXI⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, ⟨?_, ?_, ?_⟩, ?_⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      all_goals xsimp
      all_goals first | rfl | assumption | exact zx_shr_lt _ 28 (by omega)

end Kraken.Examples.Sbr.Ps

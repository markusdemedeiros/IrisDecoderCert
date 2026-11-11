import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the band-loop entries `0xe4c`/`0xf5e` and the `opd` head `0xf29`/`0xf46`
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
theorem blk_e4c (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le4c" := by
  cfg_block
  measure_hb "Le4c"
    simp only [tab_Le4c, var_Le4c, tab_Le60, var_Le60]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT⟩, hn⟩ := hs₀
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    vcgen
    case vc1 =>
      subst_vars
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lf29")
        ⟨rfl, (tab_Lf29 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl rfl rfl rfl rfl, hL, hN, hJ, hP⟩, Or.inl ?_⟩
      rw [var_Lf29]
      exact lex5_lt rfl rfl rfl (by decide) (by decide)
    all_goals subst_vars
    all_goals try xsimp
    obtain hle := ‹CondCode.le.interp _ = false›
    dsimp only at hle
    have hb := test_le32 _ hP.1 hP.2.1 _ hle
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb.2
    · xsimp; simp only [BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_f5e (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf5e" := by
  cfg_block
  measure_hb "Lf5e"
    simp only [tab_Lf5e, var_Lf5e, tab_Lf70, var_Lf70]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT⟩, hn⟩ := hs₀
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    vcgen
    case vc1 =>
      subst_vars
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Le00")
        ⟨rfl, (tab_Le00 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl rfl rfl rfl rfl, hL, hN, hJ, hP⟩, Or.inl ?_⟩
      rw [var_Le00]
      exact lex5_lt rfl rfl rfl (by decide) (by decide)
    all_goals subst_vars
    all_goals try xsimp
    obtain hle := ‹CondCode.le.interp _ = false›
    dsimp only at hle
    have hb := test_le32 _ hP.1 hP.2.1 _ hle
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb.2
    · xsimp; simp only [BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_f29 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf29" := by
  cfg_block
  measure_hb "Lf29"
    simp only [tab_Lf29, var_Lf29, tab_Lf46, var_Lf46]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hr13 : s₀.regs.get64 .r13 = x.buf := hXB.2.1.1
    have hr12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hXB.2.1.2
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hI2 := hJ.2.1.2
    have hoff := xrd_off ((s₀.regs.get64 .rsi).setWidth 32) x.p8 x.L
      (by rw [BitVec.toNat_setWidth]; omega) hC.2.2.2.2.1
    have hbl := Fr_buf_load hm (BitVec.setWidth 64 ((BitVec.setWidth 32 (s₀.regs.get64 .rsi)).ushiftRight 3)) 1 (by omega)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst_vars
    all_goals try xsimp
    · simp only [hr13]; exact hbl
    · refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      all_goals try xsimp
      all_goals try first | exact hJ.1 | exact hP.1 | exact hP.2.1 | exact hP.2.2.1 | exact hP.2.2.2.1 | exact hP.2.2.2.2
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_setl x _ _ hJ.2.1 hp _ _).1
      · simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_setl x _ _ hJ.2.1 hp _ _).2
      · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)



set_option maxRecDepth 20000 in
theorem blk_f46 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf46" := by
  cfg_block
  measure_hb "Lf46"
    simp only [tab_Lf46, var_Lf46, tab_Lf5e, var_Lf5e]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    obtain ⟨j, hj, he⟩ := vsel (BitVec.setWidth 32 (s₀.regs.get64 .rax)) 64
    have lv := Fr_vptr_load hm (8 + j) (by omega)
    rw [show 8 * (8 + j) = 64 + 8 * j by omega, ← he] at lv
    have hpv : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (x.v (8 + j)).p.toInt)) = (x.v (8 + j)).p :=
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl _
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [lv]; rfl
    · rename_i v hv _ hc
      xsimp_at hv
      rw [lv, Option.some.injEq] at hv
      subst hv
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lfc0")
        ⟨rfl, (tab_Lfc0 _ _ _ _ _ _).mpr ⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, 8 + j, by omega, by omega, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hpv
      · rw [var_Lfc0]
        exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)
    · rename_i v hv _ hc
      xsimp_at hv
      rw [lv, Option.some.injEq] at hv
      subst hv
      refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, 8 + j, by omega, by omega, ?_⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hpv
      · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

end Kraken.Examples.Sbr.Ps

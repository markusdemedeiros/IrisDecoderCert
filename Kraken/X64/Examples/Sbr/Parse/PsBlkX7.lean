import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the `dt = 1` entries `0xeb0`/`0xfc0` and the previous-row setups `0xec9`/`0xfdd`
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
theorem blk_eb0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Leb0" := by
  cfg_block
  measure_hb "Leb0"
    simp only [tab_Leb0, var_Leb0, tab_Lec9, var_Lec9]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hPI := hXB.1.2.1.2.2.2.1
    have hLS := hXB.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x38 4 (by omega)
    rw [← ea 0x38 (by omega)] at l1
    have h40 : BitVec.ofInt 32 (rd f 0x38 4) = BitVec.ofInt 32 (i32 c 40) := lo4_eq f 0x38 _ hLS.1.2.2.2
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
    · rw [l1]; rfl
    obtain hle := ‹CondCode.le.interp _ = false›
    dsimp only at hle
    have hb := test_le32 _ hP.1 hP.2.1 _ hle
    rename_i v hv
    xsimp_at hv
    rw [l1, Option.some.injEq] at hv
    subst hv
    have hne := hPI.2.2.2.2.2.1
    have hno := hPI.2.2.2.2.1
    have h15 := hP.2.2.1
    simp only [ne, i32] at h15 hne
    replace h15 := Nat.lt_of_lt_of_le h15 (by omega : _ ≤ 5)
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb.1
    · xsimp; exact hb.2
    · xsimp; rw [h40]
      have H := ec_src _ _ h15 hno.1 hno.2 
      exact (ec_rng _ (H _).1 (H _).2 _ _).1
    · xsimp; rw [h40]
      have H := ec_src _ _ h15 hno.1 hno.2
      exact (ec_rng _ (H _).1 (H _).2 _ _).2
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)


set_option maxRecDepth 20000 in
theorem blk_fc0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lfc0" := by
  cfg_block
  measure_hb "Lfc0"
    simp only [tab_Lfc0, var_Lfc0, tab_Lfdd, var_Lfdd]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT⟩, hn⟩ := hs₀
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have hPI := hXB.1.2.1.2.2.2.1
    have hLS := hXB.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x38 4 (by omega)
    rw [← ea 0x38 (by omega)] at l1
    have h40 : BitVec.ofInt 32 (rd f 0x38 4) = BitVec.ofInt 32 (i32 c 40) := lo4_eq f 0x38 _ hLS.1.2.2.2
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
    · rw [l1]; rfl
    obtain hle := ‹CondCode.le.interp _ = false›
    dsimp only at hle
    have hb := test_le32 _ hP.1 hP.2.1 _ hle
    rename_i v hv
    xsimp_at hv
    rw [l1, Option.some.injEq] at hv
    subst hv
    have hne := hPI.2.2.2.2.2.1
    have hno := hPI.2.2.2.2.1
    have h15 := hP.2.2.1
    simp only [ne, i32] at h15 hne
    replace h15 := Nat.lt_of_lt_of_le h15 (by omega : _ ≤ 5)
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_regs hJ ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb.1
    · xsimp; exact hb.2
    · xsimp; rw [h40]
      have H := ec_src _ _ h15 hno.1 hno.2 
      exact (ec_rng _ (H _).1 (H _).2 _ _).1
    · xsimp; rw [h40]
      have H := ec_src _ _ h15 hno.1 hno.2
      exact (ec_rng _ (H _).1 (H _).2 _ _).2
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_ec9 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lec9" := by
  cfg_block
  measure_hb "Lec9"
    simp only [tab_Lec9, var_Lec9, tab_Lee0, var_Lee0]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hb1, hb34, hc1, hc5⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x50 8 (by omega)
    rw [← ea 0x50 (by omega)] at l1
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    rename_i v hv _
    xsimp_at hv
    rw [l1, Option.some.injEq] at hv
    subst hv
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_zx hJ hp ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ⟨?_, ?_⟩, ⟨_, hc1, hc5, ?_⟩⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb34
    · xsimp; simp only [BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · xsimp; rw [offs2]; xsimp; rw [hL.1.1]; exact rowq _ _ _
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)


set_option maxRecDepth 20000 in
theorem blk_fdd (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lfdd" := by
  cfg_block
  measure_hb "Lfdd"
    simp only [tab_Lfdd, var_Lfdd, tab_L1000, var_L1000]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hb1, hb34, hc1, hc5⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hfl : f.length = 0x78 := hXB.1.2.1.2.2.1
    have ea : ∀ o : Nat, o ≤ 0xa0 → s₀.regs.get64 .rbp + BitVec.ofNat 64 (18446744073709551616 - (0xa0 - o))
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o := by
      intro o ho; rw [hbp]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have l1 := Fr_f_load hm hfl 0x28 8 (by omega)
    rw [← ea 0x28 (by omega)] at l1
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [l1]; rfl
    rename_i v hv _
    xsimp_at hv
    rw [l1, Option.some.injEq] at hv
    subst hv
    refine ⟨⟨c, f, XB_regs hXB rfl ?_ ?_ ?_ ?_, hL, hN, XJ_zx hJ hp ?_, XP_regs hP ?_ ?_ ?_ ?_, ?_, ⟨?_, ?_⟩, ⟨_, hc1, hc5, ?_⟩⟩, Nat.le_of_lt ?_⟩
    all_goals try (xsimp; done)
    · xsimp; exact hT
    · xsimp; exact hb34
    · xsimp; simp only [BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · xsimp; rw [offs2]; xsimp; rw [hL.1.2]; exact rowq _ _ _
    · exact lex5_lt rfl (vq1 hbp rfl (by xsimp)) (vq2 hbp rfl (by xsimp)) (by decide) (by decide)

end Kraken.Examples.Sbr.Ps

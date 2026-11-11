import Kraken.X64.Examples.Sbr.Parse.PsBlkXLib

/-!
# `ff_ps_read_data`, the extension: the band-loop stores `0xe80`/`0xf90`/`0xf06`/`0x1026` (one `ipd`/`opd` byte per band)
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
theorem blk_e80 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Le80" := by
  cfg_block
  measure_hb "Le80"
    simp only [tab_Le80, var_Le80]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hdi⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    obtain ⟨kk, hk6, hk10, hpk⟩ := hT
    have hv := vlc1 hC.2.1 hk6 hk10 hdi
    have hPI := hXB.1.2.1.2.2.2.1
    have hne := hPI.2.2.2.2.2.1
    have h15 : (s₀.regs.get64 .r15).toNat < 5 := by
      have := hP.2.2.1; simp only [ne] at this hne; omega
    have h14 : (s₀.regs.get64 .r14).toNat < 34 := by have := hBd.1; have := hBd.2; omega
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have l2 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdi).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdi).toNat) 1 (by omega)
    have hpa := par_addr hP.2.2.2.1 h15 h14 (by omega)
    have lc := Fr_c_load hm hcl (416 + 34 * (s₀.regs.get64 .r15).toNat + (s₀.regs.get64 .r14).toNat) 1 (by omega)
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [offs4]; xsimp; rw [hpk, tab_addr2 _ _ hdi, l2]; rfl
    · rw [offs4]; xsimp; rw [hpk, tab_addr0 _ _ hdi, l0]; rfl
    · rw [hpa, lc]; rfl
    all_goals rw [hpa]
    all_goals rename_i s0 v1 hv1 v0 hv0 _ hz
    all_goals xsimp_at hv1; rw [offs4] at hv1; (try xsimp_at hv1)
    all_goals rw [hpk, tab_addr2 _ _ hdi, l2, Option.some.injEq] at hv1; subst hv1
    all_goals xsimp_at hv0; rw [offs4] at hv0; (try xsimp_at hv0)
    all_goals rw [hpk, tab_addr0 _ _ hdi, l0, Option.some.injEq] at hv0; subst hv0
    all_goals have hS := sx_add _ hv.2.2 (s0.regs.get64 .rsi) (by have := hJ.2.1.2; omega)
    all_goals have hr12 := hXB.2.1.2
    · xsimp_at hz; rw [nz_sub] at hz
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Le60")
        ⟨rfl, (tab_Le60 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega)), ?_, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · xsimp; exact ⟨kk, hk6, hk10, hpk⟩
      · simp only [XBd]; xsimp; exact ⟨hBd.1, band_next _ _ hBd.2 (fun h => hz h.symm)⟩
      · rw [var_Le60]
        xsimp
        exact lex6_lt (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (BitVec.isLt _) (band_dec _ _ hBd.2)
    · left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lf29")
        ⟨rfl, (tab_Lf29 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega))⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · rw [var_Lf29]
        xsimp
        exact lex5_lt rfl (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_f90 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf90" := by
  cfg_block
  measure_hb "Lf90"
    simp only [tab_Lf90, var_Lf90]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hdi⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    obtain ⟨kk, hk6, hk10, hpk⟩ := hT
    have hv := vlc1 hC.2.1 hk6 hk10 hdi
    have hPI := hXB.1.2.1.2.2.2.1
    have hne := hPI.2.2.2.2.2.1
    have h15 : (s₀.regs.get64 .r15).toNat < 5 := by
      have := hP.2.2.1; simp only [ne] at this hne; omega
    have h14 : (s₀.regs.get64 .r14).toNat < 34 := by have := hBd.1; have := hBd.2; omega
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have l2 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdi).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdi).toNat) 1 (by omega)
    have hpa := par_addr hP.2.2.2.2 h15 h14 (by omega)
    have lc := Fr_c_load hm hcl (586 + 34 * (s₀.regs.get64 .r15).toNat + (s₀.regs.get64 .r14).toNat) 1 (by omega)
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [offs4]; xsimp; rw [hpk, tab_addr2 _ _ hdi, l2]; rfl
    · rw [offs4]; xsimp; rw [hpk, tab_addr0 _ _ hdi, l0]; rfl
    · rw [hpa, lc]; rfl
    all_goals rw [hpa]
    all_goals rename_i s0 v1 hv1 v0 hv0 _ hz
    all_goals xsimp_at hv1; rw [offs4] at hv1; (try xsimp_at hv1)
    all_goals rw [hpk, tab_addr2 _ _ hdi, l2, Option.some.injEq] at hv1; subst hv1
    all_goals xsimp_at hv0; rw [offs4] at hv0; (try xsimp_at hv0)
    all_goals rw [hpk, tab_addr0 _ _ hdi, l0, Option.some.injEq] at hv0; subst hv0
    all_goals have hS := sx_add _ hv.2.2 (s0.regs.get64 .rdx) (by have := hJ.2.1.2; omega)
    all_goals have hr12 := hXB.2.1.2
    · xsimp_at hz; rw [nz_sub] at hz
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lf70")
        ⟨rfl, (tab_Lf70 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega)), ?_, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · xsimp; exact ⟨kk, hk6, hk10, hpk⟩
      · simp only [XBd]; xsimp; exact ⟨hBd.1, band_next _ _ hBd.2 (fun h => hz h.symm)⟩
      · rw [var_Lf70]
        xsimp
        exact lex6_lt (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (BitVec.isLt _) (band_dec _ _ hBd.2)
    · left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Le00")
        ⟨rfl, (tab_Le00 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega))⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · rw [var_Le00]
        xsimp
        exact lex5_lt rfl (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_f06 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lf06" := by
  cfg_block
  measure_hb "Lf06"
    simp only [tab_Lf06, var_Lf06, tab_Lf29, var_Lf29]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hQ, hdi⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    obtain ⟨kk, hk6, hk10, hpk⟩ := hT
    have hv := vlc1 hC.2.1 hk6 hk10 hdi
    have hPI := hXB.1.2.1.2.2.2.1
    have hne := hPI.2.2.2.2.2.1
    have h15 : (s₀.regs.get64 .r15).toNat < 5 := by
      have := hP.2.2.1; simp only [ne] at this hne; omega
    have h14 : (s₀.regs.get64 .r10).toNat < 34 := by have := hBd.1; have := hBd.2; omega
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have l2 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rsi).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rsi).toNat) 1 (by omega)
    have hpa := par_addr hP.2.2.2.1 h15 h14 (by omega)
    have lc := Fr_c_load hm hcl (416 + 34 * (s₀.regs.get64 .r15).toNat + (s₀.regs.get64 .r10).toNat) 1 (by omega)
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [offs4]; xsimp; rw [hpk, tab_addr2 _ _ hdi, l2]; rfl
    · rw [offs4]; xsimp; rw [hpk, tab_addr0 _ _ hdi, l0]; rfl
    · rw [hpa, lc]; rfl
    all_goals rw [hpa]
    all_goals rename_i s0 v1 hv1 v0 hv0 _ hz
    all_goals xsimp_at hv1; rw [offs4] at hv1; (try xsimp_at hv1)
    all_goals rw [hpk, tab_addr2 _ _ hdi, l2, Option.some.injEq] at hv1; subst hv1
    all_goals xsimp_at hv0; rw [offs4] at hv0; (try xsimp_at hv0)
    all_goals rw [hpk, tab_addr0 _ _ hdi, l0, Option.some.injEq] at hv0; subst hv0
    all_goals have hS := sx_add2 _ hv.2.2 (s0.regs.get64 .rdi) (by have := hJ.2.1.2; omega)
    all_goals have hr12 := hXB.2.1.2
    · xsimp_at hz; rw [nz_sub] at hz
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lee0")
        ⟨rfl, (tab_Lee0 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega)), ?_, ?_, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · xsimp; exact ⟨kk, hk6, hk10, hpk⟩
      · simp only [XBd]; xsimp; exact ⟨hBd.1, band_next _ _ hBd.2 (fun h => hz h.symm)⟩
      · simp only [XQ]; xsimp; exact hQ
      · rw [var_Lee0]
        xsimp
        exact lex6_lt (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (BitVec.isLt _) (band_dec _ _ hBd.2)
    · refine ⟨⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega))⟩, Nat.le_of_lt ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · try xsimp
        exact lex5_lt rfl (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (by decide) (by decide)

set_option maxRecDepth 20000 in
theorem blk_1026 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.L1026" := by
  cfg_block
  measure_hb "L1026"
    simp only [tab_L1026, var_L1026]
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hXB, hL, hN, hJ, hP, hT, hBd, hQ, hdi⟩, hn⟩ := hs₀
    have hC := hXB.1.1
    have hm := hXB.1.2.2
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hXB.1.2.1.2.1
    have hcl : c.length = 764 := hXB.1.2.1.2.2.2.1.1
    obtain ⟨kk, hk6, hk10, hpk⟩ := hT
    have hv := vlc1 hC.2.1 hk6 hk10 hdi
    have hPI := hXB.1.2.1.2.2.2.1
    have hne := hPI.2.2.2.2.2.1
    have h15 : (s₀.regs.get64 .r15).toNat < 5 := by
      have := hP.2.2.1; simp only [ne] at this hne; omega
    have h14 : (s₀.regs.get64 .r10).toNat < 34 := by have := hBd.1; have := hBd.2; omega
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have l2 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdx).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm kk hk10 hv.2.1 (4 * (s₀.regs.get64 .rdx).toNat) 1 (by omega)
    have hpa := par_addr hP.2.2.2.2 h15 h14 (by omega)
    have lc := Fr_c_load hm hcl (586 + 34 * (s₀.regs.get64 .r15).toNat + (s₀.regs.get64 .r10).toNat) 1 (by omega)
    vcgen
    all_goals subst_vars
    all_goals try xsimp
    · rw [offs4]; xsimp; rw [hpk, tab_addr2 _ _ hdi, l2]; rfl
    · rw [offs4]; xsimp; rw [hpk, tab_addr0 _ _ hdi, l0]; rfl
    · rw [hpa, lc]; rfl
    all_goals rw [hpa]
    all_goals rename_i s0 v1 hv1 v0 hv0 _ hz
    all_goals xsimp_at hv1; rw [offs4] at hv1; (try xsimp_at hv1)
    all_goals rw [hpk, tab_addr2 _ _ hdi, l2, Option.some.injEq] at hv1; subst hv1
    all_goals xsimp_at hv0; rw [offs4] at hv0; (try xsimp_at hv0)
    all_goals rw [hpk, tab_addr0 _ _ hdi, l0, Option.some.injEq] at hv0; subst hv0
    all_goals have hS := sx_add2 _ hv.2.2 (s0.regs.get64 .rdi) (by have := hJ.2.1.2; omega)
    all_goals have hr12 := hXB.2.1.2
    · xsimp_at hz; rw [nz_sub] at hz
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L1000")
        ⟨rfl, (tab_L1000 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega)), ?_, ?_, ?_⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · xsimp; exact ⟨kk, hk6, hk10, hpk⟩
      · simp only [XBd]; xsimp; exact ⟨hBd.1, band_next _ _ hBd.2 (fun h => hz h.symm)⟩
      · simp only [XQ]; xsimp; exact hQ
      · rw [var_L1000]
        xsimp
        exact lex6_lt (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (BitVec.isLt _) (band_dec _ _ hBd.2)
    · left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Le00")
        ⟨rfl, (tab_Le00 _ _ _ _ _ _).mpr ⟨_, f, XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl ?_ ?_ ?_ ?_,
          XL_ne hL (ne_wrpar _ _ _ hcl (by omega) (by omega)), hN, ⟨?_, ?_, ?_⟩,
          XP_ne (XP_regs hP ?_ ?_ ?_ ?_) (ne_wrpar _ _ _ hcl (by omega) (by omega))⟩, Or.inl ?_⟩
      all_goals try (xsimp; done)
      · xsimp; exact hJ.1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).1
      · xsimp; simp only [hr12, BitVec.setWidth_32_64_32]; exact Nat.le_trans hJ.2.2 (ix_clampS' x _ _ hJ.2.1 (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_eq hS.symm)) _ _).2
      · rw [var_Le00]
        xsimp
        exact lex5_lt rfl (vqF1 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (vqF2 hXB (XB_wrpar hXB _ (by omega) (by omega) _ (b8_lt _ _) rfl (by xsimp) (by xsimp) (by xsimp) (by xsimp)))
          (by decide) (by decide)

end Kraken.Examples.Sbr.Ps

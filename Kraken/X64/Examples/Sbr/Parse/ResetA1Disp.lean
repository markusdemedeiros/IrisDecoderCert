import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib

/-!
# `sbr_reset`: the sample-rate dispatch (shard A1)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L10b8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L10b8" ⟨"sbr_reset.L10b8", B.L10b8, some "sbr_reset.L10d9"⟩ := by
  info_off
  measure_hb "L10b8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hlo, hne⟩ := T.L10b8.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L10b8]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L1814, T.L1814.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1820, T.L1820.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      rename_i h1 h2
      have := toInt_ne_of_ne32 h1 (by decide); have := toInt_ne_of_ne32 h2 (by decide)
      rate_none
    · refine Or.inl (Table.ofLabels_at ⟨S.L114a, T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 2, ?_, rfl⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
theorem blk_L10d9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L10d9" ⟨"sbr_reset.L10d9", B.L10d9, some "sbr_reset.L10fe"⟩ := by
  info_off
  measure_hb "L10d9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hlo⟩ := T.L10d9.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L10d9]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L1127, T.L1127.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp only [srI]; omega
    · refine Or.inl (Table.ofLabels_at ⟨S.L111e, T.L111e.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1143, T.L1143.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1143, T.L1143.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1820, T.L1820.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      rename_i h0 h1 h2 h3
      have := toInt_ne_of_ne32 h1 (by decide); have := toInt_ne_of_ne32 h2 (by decide)
      have := toInt_ne_of_ne32 h3 (by decide)
      rate_none
theorem blk_L10fe (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L10fe" ⟨"sbr_reset.L10fe", B.L10fe, some "sbr_reset.L111e"⟩ := by
  info_off
  measure_hb "L10fe"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hlo, hhi⟩ := T.L10fe.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L10fe]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L1808, T.L1808.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L111e, T.L111e.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1820, T.L1820.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      rename_i h1 h2 h3
      have := toInt_ne_of_ne32 h1 (by decide); have := toInt_ne_of_ne32 h2 (by decide)
      have := toInt_ne_of_ne32 h3 (by decide)
      rate_none
    · refine ⟨T.L111e.mpr ⟨hRD, ?_⟩, by var_step⟩
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
theorem blk_L1127 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1127" ⟨"sbr_reset.L1127", B.L1127, some "sbr_reset.L1143"⟩ := by
  info_off
  measure_hb "L1127"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hlo⟩ := T.L1127.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L1127]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L1143, T.L1143.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1143, T.L1143.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
    · refine Or.inl (Table.ofLabels_at ⟨S.L1820, T.L1820.mpr ⟨hRD, ?_⟩, by edge_step⟩)
      rename_i h1 h2 h3
      have := toInt_ne_of_ne32 h1 (by decide); have := toInt_ne_of_ne32 h2 (by decide)
      have := toInt_ne_of_ne32 h3 (by decide)
      rate_none
    · refine ⟨T.L1143.mpr ⟨hRD, ?_⟩, by var_step⟩
      simp [rateRow, srI, toInt_of_eq32 (by assumption) (by decide)]
theorem blk_L111e (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L111e" ⟨"sbr_reset.L111e", B.L111e, some "sbr_reset.L1127"⟩ := by
  info_off
  measure_hb "L111e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hr⟩ := T.L111e.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L111e]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L114a, T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 4, hr, rfl⟩, by edge_step⟩)
theorem blk_L17fc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L17fc" ⟨"sbr_reset.L17fc", B.L17fc, some "sbr_reset.L1808"⟩ := by
  info_off
  measure_hb "L17fc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hr⟩ := T.L17fc.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L17fc]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L114a, T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 0, hr, rfl⟩, by edge_step⟩)
theorem blk_L1808 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1808" ⟨"sbr_reset.L1808", B.L1808, some "sbr_reset.L1814"⟩ := by
  info_off
  measure_hb "L1808"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hr⟩ := T.L1808.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L1808]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L114a, T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 3, hr, rfl⟩, by edge_step⟩)
theorem blk_L1814 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1814" ⟨"sbr_reset.L1814", B.L1814, some "sbr_reset.L1820"⟩ := by
  info_off
  measure_hb "L1814"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hr⟩ := T.L1814.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L1814]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · refine Or.inl (Table.ofLabels_at ⟨S.L114a, T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 1, hr, rfl⟩, by edge_step⟩)
theorem blk_L1143 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1143" ⟨"sbr_reset.L1143", B.L1143, some "sbr_reset.L114a"⟩ := by
  info_off
  measure_hb "L1143"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hRD, hr⟩ := T.L1143.mp hs
    clear hs
    have hcx := hRD.2.2.2
    simp only [B.L1143]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [hcx] at *
    all_goals try disp_simp
    · exact ⟨T.L114a.mpr ⟨RD.congr (by simp) (by simp) rfl (by simp) (by simp) (by simp) hRD, 5, hr, rfl⟩, by var_step⟩
end Kraken.Examples.Sbr.Reset

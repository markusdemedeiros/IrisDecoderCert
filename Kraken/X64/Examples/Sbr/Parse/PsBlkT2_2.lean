import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `nr_iid_par == 1`: row `N` of `icc` checked. -/
theorem blk_L14ec (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L14ec" := by
  cfg_block
  measure_hb "L14ec"
    intro n
    simp only [tab_L14ec, var_L14ec, tab_L14f1, var_L14f1]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hm0 : 0 < m := by omega
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    · rename_i e1
      have := t2_ne hcx (by omega) e1
      have h1m : 1 < m := by omega
      t1_jump "ff_ps_read_data.L14fd"
      show q14fd _ _ _ _ _ _
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl rfl rfl rfl rfl, hW⟩, ⟨hne, h12⟩, hbx,
        t2_lt hm 1 h1m, t2_rcx hm hcx, hdx⟩
    · exact ⟨⟨c, f, N, ⟨t1_B_eq hB rfl rfl rfl rfl rfl, hW⟩, ⟨hne, h12⟩, hbx⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `1`–`3`. -/
theorem blk_L14fd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L14fd" := by
  cfg_block
  measure_hb "L14fd"
    intro n
    simp only [tab_L14fd, var_L14fd, tab_L152a, var_L152a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 1 < m := by omega
    vcgen
    all_goals try subst_vars
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm at *; t1cc at *; t2_ft 1 2 3 4

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `4`–`6`. -/
theorem blk_L152a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L152a" := by
  cfg_block
  measure_hb "L152a"
    intro n
    simp only [tab_L152a, var_L152a, tab_L1557, var_L1557]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 4 < m := by omega
    vcgen
    all_goals try subst_vars
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm at *; t1cc at *; t2_ft 4 5 6 7

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `7`–`9`. -/
theorem blk_L1557 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1557" := by
  cfg_block
  measure_hb "L1557"
    intro n
    simp only [tab_L1557, var_L1557, tab_L158c, var_L158c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 7 < m := by omega
    vcgen
    all_goals try subst_vars
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm at *; t1cc at *; t2_ft 7 8 9 10

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `10`–`12`. -/
theorem blk_L158c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L158c" := by
  cfg_block
  measure_hb "L158c"
    intro n
    simp only [tab_L158c, var_L158c, tab_L15c5, var_L15c5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 10 < m := by omega
    vcgen
    all_goals try subst_vars
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm at *; t1cc at *; t2_ft 10 11 12 13

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `13`–`15`. -/
theorem blk_L15c5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L15c5" := by
  cfg_block
  measure_hb "L15c5"
    intro n
    simp only [tab_L15c5, var_L15c5, tab_L15fe, var_L15fe]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 13 < m := by omega
    vcgen
    all_goals try subst_vars
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm; t2_ld
    · t2_ja
    · t2_je
    · t1norm at *; t1cc at *; t2_ft 13 14 15 16

end Kraken.Examples.Sbr.Ps

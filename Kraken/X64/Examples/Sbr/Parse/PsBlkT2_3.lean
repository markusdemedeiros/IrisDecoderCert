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
/-- The `icc` check, bands `16`–`18`. -/
theorem blk_L15fe (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L15fe" := by
  cfg_block
  measure_hb "L15fe"
    intro n
    simp only [tab_L15fe, var_L15fe, tab_L1637, var_L1637]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 16 < m := by omega
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
    · t1norm at *; t1cc at *; t2_ft 16 17 18 19

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `19`–`21`. -/
theorem blk_L1637 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1637" := by
  cfg_block
  measure_hb "L1637"
    intro n
    simp only [tab_L1637, var_L1637, tab_L1670, var_L1670]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 19 < m := by omega
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
    · t1norm at *; t1cc at *; t2_ft 19 20 21 22

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `22`–`24`. -/
theorem blk_L1670 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1670" := by
  cfg_block
  measure_hb "L1670"
    intro n
    simp only [tab_L1670, var_L1670, tab_L16a9, var_L16a9]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 22 < m := by omega
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
    · t1norm at *; t1cc at *; t2_ft 22 23 24 25

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `25`–`27`. -/
theorem blk_L16a9 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L16a9" := by
  cfg_block
  measure_hb "L16a9"
    intro n
    simp only [tab_L16a9, var_L16a9, tab_L16e2, var_L16e2]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 25 < m := by omega
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
    · t1norm at *; t1cc at *; t2_ft 25 26 27 28

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `28`–`30`. -/
theorem blk_L16e2 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L16e2" := by
  cfg_block
  measure_hb "L16e2"
    intro n
    simp only [tab_L16e2, var_L16e2, tab_L171b, var_L171b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 28 < m := by omega
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
    · t1norm at *; t1cc at *; t2_ft 28 29 30 31

set_option maxRecDepth 20000 in
/-- The `icc` check, bands `31`–`33` (then the trap: `nr_iid_par ≤ 34`). -/
theorem blk_L171b (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L171b" := by
  cfg_block
  measure_hb "L171b"
    intro n
    simp only [tab_L171b, var_L171b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx, hnr, hcx, hdx⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have h34 : i32 c 12 ≤ 34 := (t1_B_inv hB).2.1
    obtain ⟨m, hm⟩ : ∃ m : Nat, i32 c 12 = m := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm] at hnr h34
    rw [hm, Int.toNat_natCast] at hcx
    have hm34 : m ≤ 34 := by omega
    have hmb : 31 < m := by omega
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
    · t1norm at *; t1cc at *
      have a1 := t2_ne (j := 32) hcx (by omega)
        ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 32) = 0#32› (by omega)
      have a2 := t2_ne (j := 33) hcx (by omega)
        ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 33) = 0#32› (by omega)
      have a3 := t2_ne (j := 34) hcx (by omega)
        ‹¬BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.ofNat 64 34) = 0#32› (by omega)
      have hlt := t2_lt3 (b := 31) hmb a1 a2 a3
      exact absurd hlt (by omega)

end Kraken.Examples.Sbr.Ps

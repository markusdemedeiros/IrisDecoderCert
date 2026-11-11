import Kraken.X64.Examples.Sbr.Parse.PsBlkT1Lib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `if (!enable_icc) skip`. -/
theorem blk_L1380 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1380" := by
  cfg_block
  measure_hb "L1380"
    intro n
    simp only [tab_L1380, var_L1380, tab_L1385, var_L1385]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hD, hn⟩ := hs₀
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    · t1_jump "ff_ps_read_data.L1395"
      exact hD
    · exact ⟨hD, by var_step⟩

set_option maxRecDepth 20000 in
/-- `is34bands = (nr_icc_par == 34)`. -/
theorem blk_L1385 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1385" := by
  cfg_block
  measure_hb "L1385"
    intro n
    simp only [tab_L1385, var_L1385, tab_L138c, var_L138c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, hbx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try simp only [hbx]
    all_goals try t1_some hB
    exact ⟨⟨⟨c, f, N, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), by t1r; exact hbx, hW⟩,
      by t1r; exact t1_setcc_le1 _ _⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Store `is34bands`. -/
theorem blk_L138c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L138c" := by
  cfg_block
  measure_hb "L138c"
    intro n
    simp only [tab_L138c, var_L138c, tab_L1395, var_L1395]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨c, f, N, hB, hbx, hW⟩, hcl⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try simp only [hbx]
    all_goals try t1_some hB
    refine ⟨⟨wr c 756 4 _, f, N, t1_B_st hB 756 4 _ (by omega) (by omega) rfl (by t1r) (by t1r) (by t1r) (by t1r),
      by t1r; exact hbx, fun hp => t1_W2_756 (hW hp) hl _ (t1_zext_le1 _ hcl)⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `if (!enable_ipdopd)` clear: the first two stores. -/
theorem blk_L1395 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1395" := by
  cfg_block
  measure_hb "L1395"
    intro n
    simp only [tab_L1395, var_L1395, tab_L13ad, var_L13ad]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, hbx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try simp only [hbx]
    all_goals try t1_some hB
    · t1_jump "ff_ps_read_data.L13f5"
      exact ⟨c, f, N, t1_B_eq hB rfl rfl rfl rfl rfl, hbx, hW⟩
    · simp only [t1_vpxor_ymm, BitVec.toInt_zero]
      exact ⟨⟨⟨wr (wr c 724 32 0) 704 32 0, f, N,
        t1_B_st2 hB 724 32 0 704 32 0 (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl,
        hbx, fun hp => t1_W2_zero2 (hW hp) hl 724 704 (by omega) (by omega) (by omega) (by omega)⟩,
        by simp only [t1_vpxor_ymm]; rfl⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Clear `ipd`/`opd`: the stores at `672`, `640`. -/
theorem blk_L13ad (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13ad" := by
  cfg_block
  measure_hb "L13ad"
    intro n
    simp only [tab_L13ad, var_L13ad, tab_L13bd, var_L13bd]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨c, f, N, hB, hbx, hW⟩, hy⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try simp only [hbx]
    all_goals try t1_some hB
    simp only [t1_ymm_toInt hy]
    exact ⟨⟨⟨wr (wr c 672 32 0) 640 32 0, f, N,
      t1_B_st2 hB 672 32 0 640 32 0 (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl,
      hbx, fun hp => t1_W2_zero2 (hW hp) hl 672 640 (by omega) (by omega) (by omega) (by omega)⟩,
      hy⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Clear `ipd`/`opd`: the stores at `608`, `576`. -/
theorem blk_L13bd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13bd" := by
  cfg_block
  measure_hb "L13bd"
    intro n
    simp only [tab_L13bd, var_L13bd, tab_L13cd, var_L13cd]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨c, f, N, hB, hbx, hW⟩, hy⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try simp only [hbx]
    all_goals try t1_some hB
    simp only [t1_ymm_toInt hy]
    exact ⟨⟨⟨wr (wr c 608 32 0) 576 32 0, f, N,
      t1_B_st2 hB 608 32 0 576 32 0 (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl,
      hbx, fun hp => t1_W2_zero2 (hW hp) hl 608 576 (by omega) (by omega) (by omega) (by omega)⟩,
      hy⟩, by var_step⟩

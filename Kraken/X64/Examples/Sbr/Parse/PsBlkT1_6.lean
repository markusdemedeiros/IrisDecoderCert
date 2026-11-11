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
/-- Clear `ipd`/`opd`: the stores at `544`, `512`. -/
theorem blk_L13cd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13cd" := by
  cfg_block
  measure_hb "L13cd"
    intro n
    simp only [tab_L13cd, var_L13cd, tab_L13dd, var_L13dd]
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
    exact ⟨⟨⟨wr (wr c 544 32 0) 512 32 0, f, N,
      t1_B_st2 hB 544 32 0 512 32 0 (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl,
      hbx, fun hp => t1_W2_zero2 (hW hp) hl 544 512 (by omega) (by omega) (by omega) (by omega)⟩,
      hy⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Clear `ipd`/`opd`: the stores at `480`, `448`. -/
theorem blk_L13dd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13dd" := by
  cfg_block
  measure_hb "L13dd"
    intro n
    simp only [tab_L13dd, var_L13dd, tab_L13ed, var_L13ed]
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
    exact ⟨⟨⟨wr (wr c 480 32 0) 448 32 0, f, N,
      t1_B_st2 hB 480 32 0 448 32 0 (by omega) (by omega) (by omega) (by omega) rfl rfl rfl rfl rfl,
      hbx, fun hp => t1_W2_zero2 (hW hp) hl 480 448 (by omega) (by omega) (by omega) (by omega)⟩,
      hy⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Clear `ipd`/`opd`: the last store, at `416`. -/
theorem blk_L13ed (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L13ed" := by
  cfg_block
  measure_hb "L13ed"
    intro n
    simp only [tab_L13ed, var_L13ed, tab_L13f5, var_L13f5]
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
    exact ⟨⟨wr c 416 32 0, f, N, t1_B_st hB 416 32 0 (by omega) (by omega) rfl rfl rfl rfl rfl,
      hbx, fun hp => t1_W2_zero _ _ (hW hp) hl (by omega) (by omega)⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps

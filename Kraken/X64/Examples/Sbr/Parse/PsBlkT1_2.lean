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
/-- Copy row `S` of `iid` to row `N`. -/
theorem blk_L1119 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1119" := by
  cfg_block
  measure_hb "L1119"
    intro n
    simp only [tab_L1119, var_L1119, tab_L1148, var_L1148]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, ⟨hB, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, h4⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hS5 : S < 5 := hS.2.1
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr]
    rotate_right
    · rename_i hv2 hv32
      simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr, t1_get_set_ymm_same] at hv2 hv32 ⊢
      simp only [show 34 * S + 108 = 76 + 34 * S + 32 by omega, show 34 * S + 76 = 76 + 34 * S by omega,
        show 34 * N + 108 = 76 + 34 * N + 32 by omega, show 34 * N + 76 = 76 + 34 * N by omega]
        at hv2 hv32 ⊢
      refine ⟨⟨T1Cp c (76 + 34 * S) (76 + 34 * N), f, N, S,
        ⟨t1_copy hB _ _ (by omega) (by omega) (by omega) hv2 hv32 rfl (by t1r) (by t1r) (by t1r) (by t1r),
          ⟨?_, by t1r; exact h12⟩, by t1r; exact hbx, ?_, ?_, by t1r; exact hcx,
          fun hp => t1_W0_iid (hW hp) hl hN4 hS5 h4⟩⟩, by var_step⟩
      · rw [ne, t1_i32_Cp hl _ _ _ (by omega) (by omega)]; exact hne
      · simp only [T1I]; t1r; rw [t1_i32_Cp hl _ _ 4 (by omega) (by omega)]; exact hI
      · simp only [T1S] at hS ⊢; t1r; exact hS
    all_goals first
      | (rw [t1_B_load hB _ _ (by omega)]; rfl)
      | (rw [Fr_c_load (Fr_c_store hB.1.2.2 hl _ 2 (by omega) _)
            (by rw [wr_length _ _ _ _ (by omega), hl]) _ 32 (by omega)]; rfl)

set_option maxRecDepth 20000 in
/-- Copy row `S` of `icc` to row `N`. -/
theorem blk_L1157 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1157" := by
  cfg_block
  measure_hb "L1157"
    intro n
    simp only [tab_L1157, var_L1157, tab_L1192, var_L1192]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hS5 : S < 5 := hS.2.1
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr]
    rotate_right
    · rename_i hv2 hv32
      simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr, t1_get_set_ymm_same] at hv2 hv32 ⊢
      simp only [show 34 * S + 278 = 246 + 34 * S + 32 by omega, show 34 * S + 246 = 246 + 34 * S by omega,
        show 34 * N + 278 = 246 + 34 * N + 32 by omega, show 34 * N + 246 = 246 + 34 * N by omega]
        at hv2 hv32 ⊢
      refine ⟨⟨T1Cp c (246 + 34 * S) (246 + 34 * N), f, N, S,
        ⟨t1_copy hB _ _ (by omega) (by omega) (by omega) hv2 hv32 rfl (by t1r) (by t1r) (by t1r) (by t1r),
          ⟨?_, by t1r; exact h12⟩, by t1r; exact hbx, ?_, ?_, by t1r; exact hcx,
          fun hp => t1_W0_rng (hW hp) hl hN4 hS5 246 (by omega)⟩⟩, by var_step⟩
      · rw [ne, t1_i32_Cp hl _ _ _ (by omega) (by omega)]; exact hne
      · simp only [T1I]; t1r; rw [t1_i32_Cp hl _ _ 4 (by omega) (by omega)]; exact hI
      · simp only [T1S] at hS ⊢; t1r; exact hS
    all_goals first
      | (rw [t1_B_load hB _ _ (by omega)]; rfl)
      | (rw [Fr_c_load (Fr_c_store hB.1.2.2 hl _ 2 (by omega) _)
            (by rw [wr_length _ _ _ _ (by omega), hl]) _ 32 (by omega)]; rfl)

set_option maxRecDepth 20000 in
/-- Copy row `S` of `ipd` to row `N`. -/
theorem blk_L11a0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L11a0" := by
  cfg_block
  measure_hb "L11a0"
    intro n
    simp only [tab_L11a0, var_L11a0, tab_L11db, var_L11db]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hS5 : S < 5 := hS.2.1
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr]
    rotate_right
    · rename_i hv2 hv32
      simp only [h12, hcx, hbx, t1_sw N (by omega), t1_r34, t1_addr, t1_get_set_ymm_same] at hv2 hv32 ⊢
      simp only [show 34 * S + 448 = 416 + 34 * S + 32 by omega, show 34 * S + 416 = 416 + 34 * S by omega,
        show 34 * N + 448 = 416 + 34 * N + 32 by omega, show 34 * N + 416 = 416 + 34 * N by omega]
        at hv2 hv32 ⊢
      refine ⟨⟨T1Cp c (416 + 34 * S) (416 + 34 * N), f, N, S,
        t1_copy hB _ _ (by omega) (by omega) (by omega) hv2 hv32 rfl (by t1r) (by t1r) (by t1r) (by t1r),
          ⟨?_, by t1r; exact h12⟩, by t1r; exact hbx, ?_, hS5, hS.2.2, by t1r, by t1r,
          fun hp => t1_W0_rng (hW hp) hl hN4 hS5 416 (by omega)⟩, by var_step⟩
      · rw [ne, t1_i32_Cp hl _ _ _ (by omega) (by omega)]; exact hne
      · simp only [T1I]; t1r; rw [t1_i32_Cp hl _ _ 4 (by omega) (by omega)]; exact hI
    all_goals first
      | (rw [t1_B_load hB _ _ (by omega)]; rfl)
      | (rw [Fr_c_load (Fr_c_store hB.1.2.2 hl _ 2 (by omega) _)
            (by rw [wr_length _ _ _ _ (by omega), hl]) _ 32 (by omega)]; rfl)

set_option maxRecDepth 20000 in
/-- Copy row `S` of `opd` to row `N`. -/
theorem blk_L11db (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L11db" := by
  cfg_block
  measure_hb "L11db"
    intro n
    simp only [tab_L11db, var_L11db, tab_L11fd, var_L11fd]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS5, hSN, hcx, hdx, hW⟩, hn⟩ := hs₀
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hl := t1_B_len hB
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals simp only [hdx, hcx, hbx, t1_addr]
    rotate_right
    · rename_i hv2 hv32
      simp only [hdx, hcx, hbx, t1_addr, t1_get_set_ymm_same] at hv2 hv32 ⊢
      simp only [show 34 * S + 618 = 586 + 34 * S + 32 by omega, show 34 * S + 586 = 586 + 34 * S by omega,
        show 34 * N + 618 = 586 + 34 * N + 32 by omega, show 34 * N + 586 = 586 + 34 * N by omega]
        at hv2 hv32 ⊢
      refine ⟨⟨T1Cp c (586 + 34 * S) (586 + 34 * N), f, N,
        t1_copy hB _ _ (by omega) (by omega) (by omega) hv2 hv32 rfl (by t1r) (by t1r) (by t1r) (by t1r),
          ⟨?_, by t1r; exact h12⟩, ?_,
          fun hp => t1_W0_rng (hW hp) hl hN4 hS5 586 (by omega)⟩, by var_step⟩
      · rw [ne, t1_i32_Cp hl _ _ _ (by omega) (by omega)]; exact hne
      · simp only [T1I]; t1r; rw [t1_i32_Cp hl _ _ 4 (by omega) (by omega)]; exact hI
    all_goals first
      | (rw [t1_B_load hB _ _ (by omega)]; rfl)
      | (rw [Fr_c_load (Fr_c_store hB.1.2.2 hl _ 2 (by omega) _)
            (by rw [wr_length _ _ _ _ (by omega), hl]) _ 32 (by omega)]; rfl)

end Kraken.Examples.Sbr.Ps

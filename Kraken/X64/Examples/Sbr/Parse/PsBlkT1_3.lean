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
/-- `if (enable_icc)` copy (trap: `S + 1 < 7`). -/
theorem blk_L1148 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1148" := by
  cfg_block
  measure_hb "L1148"
    intro n
    simp only [tab_L1148, var_L1148, tab_L1157, var_L1157]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have ⟨h9, hS5, hSN⟩ := hS
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try (exfalso; simp only [h9, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *; omega)
    · t1_jump "ff_ps_read_data.L1192"
      exact ⟨c, f, N, S, t1_B_eq hB rfl rfl rfl rfl rfl, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩
    · exact ⟨⟨c, f, N, S, t1_B_eq hB rfl rfl rfl rfl rfl, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `if (enable_ipdopd)` copy (trap: `S + 1 < 7`). -/
theorem blk_L1192 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1192" := by
  cfg_block
  measure_hb "L1192"
    intro n
    simp only [tab_L1192, var_L1192, tab_L11a0, var_L11a0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have ⟨h9, hS5, hSN⟩ := hS
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try (exfalso; simp only [h9, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *; omega)
    · t1_jump "ff_ps_read_data.L11fd"
      exact ⟨c, f, N, t1_B_eq hB rfl rfl rfl rfl rfl, ⟨hne, h12⟩, hI, hW⟩
    · exact ⟨⟨c, f, N, S, t1_B_eq hB rfl rfl rfl rfl rfl, ⟨hne, h12⟩, hbx, hI, hS, hcx, hW⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `rcx = S = r9 - 1`; `if (enable_iid)` copy (trap: `S + 1 < 7`). -/
theorem blk_L1104 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1104" := by
  cfg_block
  measure_hb "L1104"
    intro n
    simp only [tab_L1104, var_L1104, tab_L1119, var_L1119]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, S, hB, ⟨hne, h12⟩, hbx, hI, hS, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have ⟨h9, hS5, hSN⟩ := hS
    have h4 : ¬ (BitVec.setWidth 32 (s₀.regs.get64 .r10) &&& BitVec.setWidth 32 (s₀.regs.get64 .r10)
        = 0#32) → i32 c 4 ≠ 0 := fun hz h0 => hz (by rw [BitVec.and_self, hI, h0]; rfl)

    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try (exfalso; simp only [h9, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *; omega)
    · t1_jump "ff_ps_read_data.L1148"
      exact ⟨c, f, N, S, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hne, by t1r; exact h12⟩,
        by t1r; exact hbx, by simp only [T1I]; t1r; exact hI, by simp only [T1S]; t1r; exact ⟨h9, hS5, hSN⟩,
        by t1r; bv_omega, hW⟩
    · exact ⟨⟨c, f, N, S, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hne, by t1r; exact h12⟩,
        by t1r; exact hbx, by simp only [T1I]; t1r; exact hI, by simp only [T1S]; t1r; exact ⟨h9, hS5, hSN⟩,
        by t1r; bv_omega, hW⟩, by solve_by_elim⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `num_env = 0`: `if (num_env_old > 1)` a fake envelope from `num_env_old - 1`; `r10d = enable_iid`. -/
theorem blk_L10f6 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L10f6" := by
  cfg_block
  measure_hb "L10f6"
    intro n
    simp only [tab_L10f6, var_L10f6, tab_L1104, var_L1104]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hB, ⟨hne, h12⟩, hbx, h9, h34, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hm := (t1_B_inv hB).2.2.2.2.1
    have e9 : BitVec.setWidth 32 (s₀.regs.get64 .r9) = BitVec.ofNat 32 (i32 c 40).toNat := by
      rw [h9]; exact t1_sw_ofInt _ hm.1 (by omega)
    have e9' : (BitVec.setWidth 32 (s₀.regs.get64 .r9)).toInt = i32 c 40 := by
      rw [e9, t1_toInt_ofNat32 _ (by omega)]; omega
    have L := t1_B_fload hB (18446744073709551508#64) 108 4 rfl (by omega) (by omega) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [L, Option.some.injEq, Option.isSome_some, e9',
      show (BitVec.setWidth 32 2#64).toInt = 2 from rfl] at *
    all_goals try subst_vars
    · t1_jump "ff_ps_read_data.L11fd"
      exact ⟨c, f, 0, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hne, by t1r; exact h12⟩,
        by simp only [T1I]; t1r; rw [BitVec.setWidth_32_64_32]; exact h34, hW⟩
    · exact ⟨⟨c, f, 0, (i32 c 40).toNat - 1, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r),
        ⟨hne, by t1r; exact h12⟩, by t1r; exact hbx,
        by simp only [T1I]; t1r; rw [BitVec.setWidth_32_64_32]; exact h34,
        ⟨by t1r; rw [e9]; congr 1; simp only [i32] at *; omega, by simp only [i32] at *; omega,
          by simp only [i32] at *; omega⟩, hW⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `if (enable_iid && nr_iid_par > 0)` check row `N` of `iid` (trap: `N ≤ 4`). -/
theorem blk_L11fd (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L11fd" := by
  cfg_block
  measure_hb "L11fd"
    intro n
    simp only [tab_L11fd, var_L11fd, tab_L121f, var_L121f]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, ⟨hne, h12⟩, hI, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hps : BitVec.ofInt 64 (rd f 0x68 8) = t₀.regs.get64 .rdx := hB.2.2.2.2.2
    have h40 : rd f 0x40 1 = N := t1_rd1 f 0x40 N (by rw [hB.1.2.1.2.2.1]; omega) hB.2.2.2.2.1 (by omega)
    have L1 := t1_B_fload hB (18446744073709551560#64) 0x38 8 rfl (by omega) (by omega) (by omega)
    have L2 := t1_B_fload hB (18446744073709551520#64) 0x60 1 rfl (by omega) (by omega) (by omega)
    have L3 := t1_B_load hB 12 4 (by omega)
    simp only [arg2] at L3
    have hz4 : BitVec.setWidth 32 (s₀.regs.get64 .r10) &&& BitVec.setWidth 32 (s₀.regs.get64 .r10) = 0#32
        ↔ i32 c 4 = 0 := by rw [BitVec.and_self, hI, t1_i32_eq0]
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [L1, L2, Option.some.injEq, Option.isSome_some, hz4] at *
    all_goals try subst_vars
    · t1_jump "ff_ps_read_data.L12ef"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl rfl rfl rfl rfl, fun hp => t1_W1_iid0 (hW hp) hN4 (by assumption)⟩,
        ⟨hne, h12⟩⟩
    · rw [hps, L3]; rfl
    · rename_i v _ hle h4 hv
      rw [hps, L3, Option.some.injEq] at hv; subst hv
      rw [BitVec.setWidth_32_64_32, t1_rd_i32, t1_toInt_i32] at hle
      t1_jump "ff_ps_read_data.L12ef"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r),
        fun hp => t1_W1_nr0 (hW hp) hN4 h4 hle⟩, ⟨hne, by t1r; exact h12⟩⟩
    · exfalso; rename_i htr; rw [h40] at htr
      simp only [BitVec.ofInt_natCast, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htr; omega
    · rename_i v _ hle h4 hv _
      rw [hps, L3, Option.some.injEq] at hv; subst hv
      rw [BitVec.setWidth_32_64_32, t1_rd_i32, t1_toInt_i32] at hle
      exact ⟨⟨c, f, N, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hne, by t1r; exact h12⟩, h4,
        by omega, by t1r; rw [t1_rd_i32]; exact t1_zx_i32 c 12 (by omega), hW⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps

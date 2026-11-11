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
/-- `rbx = ps`; `if (enable_icc && nr_iid_par > 0)` check `icc_par[N][0]`. -/
theorem blk_L12ef (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L12ef" := by
  cfg_block
  measure_hb "L12ef"
    intro n
    simp only [tab_L12ef, var_L12ef, tab_L12ff, var_L12ff]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hps : BitVec.ofInt 64 (rd f 0x68 8) = t₀.regs.get64 .rdx := hB.2.2.2.2.2
    have L1 := t1_B_fload hB (18446744073709551560#64) 0x38 8 rfl (by omega) (by omega) (by omega)
    have L3 := t1_B_load hB 12 4 (by omega)
    simp only [arg2] at L3
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [L1, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    · t1_jump "ff_ps_read_data.L1349"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), hW⟩, ⟨hne, by t1r; exact h12⟩, by t1r; exact hps⟩
    · rw [hps, L3]; rfl
    · rename_i v _ hle hv
      rw [hps, L3, Option.some.injEq] at hv; subst hv
      t1_jump "ff_ps_read_data.L1349"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), hW⟩, ⟨hne, by t1r; exact h12⟩, by t1r; exact hps⟩
    · rename_i v _ hle hv
      rw [hps, L3, Option.some.injEq] at hv; subst hv
      rw [BitVec.setWidth_32_64_32, t1_rd_i32, t1_toInt_i32] at hle
      exact ⟨⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), hW⟩, ⟨hne, by t1r; exact h12⟩,
        by t1r; exact hps, by omega, by t1r; rw [t1_rd_i32]; exact t1_zx_i32 c 12 (by omega)⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `num_env = N + 1` (trap: `N < 5`). -/
theorem blk_L1349 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1349" := by
  cfg_block
  measure_hb "L1349"
    intro n
    simp only [tab_L1349, var_L1349, tab_L135c, var_L135c]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, ⟨hne, h12⟩, hbx⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hb : BitVec.setWidth 32 (BitVec.ofNat 64 N) + 1#32 = BitVec.ofNat 32 (N + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hbi : (BitVec.ofNat 32 (N + 1)).toInt = (N : Int) + 1 := by
      rw [t1_toInt_ofNat32 _ (by omega)]; omega
    have L3 := t1_B_load hB 44 4 (by omega)
    simp only [arg2] at L3
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    · rw [hbx, L3]; rfl
    · exfalso; rename_i htr
      rw [h12] at htr
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htr; omega
    · simp only [h12, hb, BitVec.setWidth_32_64_32]
      refine ⟨⟨wr c 44 4 (BitVec.ofNat 32 (N + 1)).toInt, f, N,
        ⟨t1_B_st44 hB (BitVec.ofNat 32 (N + 1)) (by rw [t1_toInt_ofNat32 _ (by omega)]; omega)
          (by rw [t1_toInt_ofNat32 _ (by omega)]; omega) (by simp only [hbx])
          (by t1r) (by t1r) (by t1r) (by t1r), fun hp => t1_W1_wr44 (hW hp) hl hN4 _⟩,
        by show i32 _ 44 = _; rw [i32_wr_same _ _ _ (by omega), hbi],
        by t1r; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega,
        by t1r; exact hbx⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `border_position[N + 1] = 31`, `is34bands_old = is34bands`, `r10d = enable_iid`. -/
theorem blk_L135c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L135c" := by
  cfg_block
  measure_hb "L135c"
    intro n
    simp only [tab_L135c, var_L135c, tab_L1380, var_L1380]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, ⟨hB, hW⟩, hne, h12, hbx⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hW2 := fun hp v => t1_W2_of135 (hW hp) hl hN4 hne v
    have hA : ∀ a : BitVec 64,
        a + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) * 4#64 + 52#64
          = a + BitVec.ofNat 64 (52 + 4 * (N + 1)) := fun a => t1_a135 a _ N h12 hN4
    clear hne
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [hA, hbx]
    all_goals first
      | t1_some hB
      | (t1_jump "ff_ps_read_data.L10b4"
         exact ⟨_, f, N, t1_B_st2 hB (52 + 4 * (N + 1)) 4 31 760 4 _ (by omega) (by omega)
           (by omega) (by omega) rfl (by t1r) (by t1r) (by t1r) (by t1r), by t1r; exact hbx,
           fun hp => hW2 hp _⟩)
      | exact ⟨⟨_, f, N, t1_B_st2 hB (52 + 4 * (N + 1)) 4 31 760 4 _ (by omega) (by omega)
           (by omega) (by omega) rfl (by t1r) (by t1r) (by t1r) (by t1r), by t1r; exact hbx,
           fun hp => hW2 hp _⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `is34bands = (nr_iid_par == 34)` (`cl`); `0x1385` recomputes it from `nr_icc_par` if
`enable_icc`. -/
theorem blk_L10b4 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L10b4" := by
  cfg_block
  measure_hb "L10b4"
    intro n
    simp only [tab_L10b4, var_L10b4]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, hbx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have L3 := t1_B_load hB 12 4 (by omega)
    simp only [arg2] at L3
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [hbx]
    all_goals first
      | (rw [L3]; rfl)
      | (t1_jump "ff_ps_read_data.L138c"
         exact ⟨⟨c, f, N, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), by t1r; exact hbx,
           hW⟩, by t1r; exact t1_setcc_le1 _ _⟩)
      | (t1_jump "ff_ps_read_data.L1385"
         exact ⟨c, f, N, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), by t1r; exact hbx, hW⟩)

set_option maxRecDepth 20000 in
/-- `r10d = enable_iid`; `border_position[N] < 31`: a fake envelope (`0x1104`); else no fix-up. -/
theorem blk_L1084 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1084" := by
  cfg_block
  measure_hb "L1084"
    intro n
    simp only [tab_L1084, var_L1084, tab_L10b4, var_L10b4]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, ⟨hne, h12⟩, hN1, hbx, hI, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have L1 := t1_B_fload hB (18446744073709551508#64) 0x6c 4 rfl (by omega) (by omega) (by omega)
    have hA : ∀ a : BitVec 64,
        a + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12)) * 4#64 + 52#64
          = a + BitVec.ofNat 64 (52 + 4 * N) := fun a => t1_aB a _ N (by rw [h12]; exact t1_sw32 N) (by omega)
    have LB := t1_B_load hB (52 + 4 * N) 4 (by omega)
    have L756 := t1_B_load hB 756 4 (by omega)
    simp only [arg2] at LB L756
    have L760 := t1_B_load hB 760 4 (by omega)
    simp only [arg2] at LB L756 L760
    rw [← (show s₀.regs.get64 .rbx = t₀.regs.get64 .rdx from hbx)] at LB L756 L760
    have hW2 := fun hp v h31 => t1_W2_ofW0 (hW hp) hl hne hN1 hN4 h31 v
    have e2 : (BitVec.setWidth 32 31#64).toInt = 31 := by decide
    have e1 : (BitVec.ofInt 32 (rd c (52 + 4 * N) 4)).toInt = i32 c (52 + 4 * N) := by
      rw [t1_rd_i32, t1_toInt_i32]
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [hA] at *
    all_goals try simp only [L1, LB, L756, L760, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try (exfalso; rename_i htr; rw [h12] at htr
                   simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at htr; omega)
    case vc4 =>
      t1_jump "ff_ps_read_data.L1104"
      exact ⟨c, f, N, N - 1, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r),
        ⟨hne, by t1r; exact h12⟩, by t1r; exact hbx,
        by simp only [T1I]; t1r; first | exact hI | (simp only [BitVec.setWidth_32_64_32]; exact hI),
        ⟨by t1r; rw [h12, BitVec.setWidth_32_64_32, t1_sw32, Nat.sub_add_cancel hN1], by omega,
          by omega⟩, hW⟩
    case vc7 =>
      rename_i _ hlt
      have h31 : 31 ≤ i32 c (52 + 4 * N) := by
        change ¬ (BitVec.ofInt 32 (rd c (52 + 4 * N) 4)).toInt < (BitVec.setWidth 32 31#64).toInt at hlt
        have e1' : (BitVec.ofInt 32 (rd c (52 + 4 * N) 4)).toInt = i32 c (52 + 4 * N) := by
          rw [t1_rd_i32, t1_toInt_i32]
        omega
      t1_jump "ff_ps_read_data.L1380"
      exact ⟨_, f, N, t1_B_st hB 760 4 _ (by omega) (by omega) (by simp only [hbx]; rfl) (by t1r)
        (by t1r) (by t1r) (by t1r), by t1r; exact hbx, fun hp => hW2 hp _ h31⟩
    case vc8 =>
      rename_i hlt
      have h31 : 31 ≤ i32 c (52 + 4 * N) := by
        change ¬ (BitVec.ofInt 32 (rd c (52 + 4 * N) 4)).toInt < (BitVec.setWidth 32 31#64).toInt at hlt
        have e1' : (BitVec.ofInt 32 (rd c (52 + 4 * N) 4)).toInt = i32 c (52 + 4 * N) := by
          rw [t1_rd_i32, t1_toInt_i32]
        omega
      exact ⟨⟨_, f, N, t1_B_st hB 760 4 _ (by omega) (by omega) (by simp only [hbx]; rfl) (by t1r)
        (by t1r) (by t1r) (by t1r), by t1r; exact hbx, fun hp => hW2 hp _ h31⟩, by var_step⟩

end Kraken.Examples.Sbr.Ps

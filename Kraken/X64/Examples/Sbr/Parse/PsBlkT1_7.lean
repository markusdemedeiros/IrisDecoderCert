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
/-- `rdi = N`, `r10 = ps`, `edx = 7 + 8 iid_quant`, `rsi = rcx - 3`. -/
theorem blk_L121f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L121f" := by
  cfg_block
  measure_hb "L121f"
    intro n
    simp only [tab_L121f, var_L121f, tab_L1238, var_L1238]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, ⟨hne, h12⟩, h4, hc0, hcx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hps : BitVec.ofInt 64 (rd f 0x68 8) = t₀.regs.get64 .rdx := hB.2.2.2.2.2
    have L1 := t1_B_fload hB (18446744073709551560#64) 0x38 8 rfl (by omega) (by omega) (by omega)
    have L3 := t1_B_load hB 8 4 (by omega)
    simp only [arg2] at L3
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [L1, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    · rw [hps, L3]; rfl
    · rename_i v hv
      rw [hps, L3, Option.some.injEq] at hv; subst hv
      exact ⟨⟨c, f, N, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hne, by t1r; exact h12⟩,
        h4, hc0, by t1r; exact hcx, by t1r; rw [h12, t1_sw N (by omega)],
        by t1r; rw [h12, t1_sw N (by omega)], by t1r; exact hps, by t1r; bv_omega,
        by t1r; rw [t1_edx, t1_rd_i32, t1_toInt_i32], hW⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- `rdi = &iid_par[N][3]`, `r9`/`r10` = `rcx - 2`/`- 1`, `r11 = 0`. -/
theorem blk_L1238 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1238" := by
  cfg_block
  measure_hb "L1238"
    intro n
    simp only [tab_L1238, var_L1238, tab_L1252, var_L1252]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, hB, hN, h4, hc0, hcx, hdi, h9, h10, hsi, hdx, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    exact ⟨⟨c, f, N, 0, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r),
      ⟨hN.1, by t1r; exact hN.2⟩, h4, hc0, by t1r; exact hcx,
      by t1r; rw [h10, h9, hdi]; exact t1_rdi _ N, by t1r; exact hsi, by t1r; bv_omega,
      by t1r; bv_omega, by t1r; exact hdx, by t1r; simp, by omega, by push_cast; exact hc0,
      fun hp => ⟨hW hp, fun b hb => absurd hb (by omega)⟩⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Band `b` of row `N` of `iid`: `|iid| ≤ 7 + 8 iid_quant`, else the error (`0x14cc`). -/
theorem blk_L1252 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1252" := by
  cfg_block
  measure_hb "L1252"
    intro n
    simp only [tab_L1252, var_L1252, tab_L1275, var_L1275]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, b, hB, hN, h4, hc0, hcx, hdi, hsi, h9, h10, hdx, h11, hb4, hbc, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hP := t1_B_inv hB
    have hc34 : i32 c 12 ≤ 34 := hP.2.1
    have hq : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hb34 : b < 34 := by omega
    have hA : s₀.regs.get64 .rdi + s₀.regs.get64 .r11 + 18446744073709551613#64
        = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * N + (b + 0)) := by
      rw [hdi, h11]; exact t1_aI _ N b 0
    have LB := t1_B_load hB (76 + 34 * N + (b + 0)) 1 (by omega)
    rw [← hA] at LB
    have hy := t1_i8_rd c (76 + 34 * N + (b + 0)) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [LB, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    case vc2 =>
      t1_jump "ff_ps_read_data.L14cc"
      exact ⟨⟨c, f, (t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r)).1, hB.2.2.2.2.2,
        fun hp => ⟨(hW hp).1.1.1, (hW hp).1.1.2.1⟩⟩, by t1r; exact hB.2.2.1⟩
    case vc3 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [h10, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      t1_jump "ff_ps_read_data.L12ef"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), fun hp => t1_W1_row (hW hp).1 hN4
        (t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)) (by simp only [i32] at *; omega)⟩,
        ⟨hN.1, by t1r; exact hN.2⟩⟩
    case vc4 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [h10, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      exact ⟨⟨c, f, N, b, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hN.1, by t1r; exact hN.2⟩,
        h4, hc0, by t1r; exact hcx, by t1r; exact hdi, by t1r; exact hsi, by t1r; exact h9,
        by t1r; exact h10, by t1r; exact hdx, by t1r; exact h11, hb4,
        by have hbc' : (b : Int) + 0 < i32 c 12 := hbc
           have heq' : ¬ ((i32 c 12).toNat = 1 + b) := heq
           omega,
        fun hp => ⟨(hW hp).1, t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)⟩⟩, by var_step⟩

set_option maxRecDepth 20000 in
/-- Band `b + 1` of row `N` of `iid`: `|iid| ≤ 7 + 8 iid_quant`, else the error (`0x14cc`). -/
theorem blk_L1275 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1275" := by
  cfg_block
  measure_hb "L1275"
    intro n
    simp only [tab_L1275, var_L1275, tab_L1298, var_L1298]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, b, hB, hN, h4, hc0, hcx, hdi, hsi, h9, h10, hdx, h11, hb4, hbc, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hP := t1_B_inv hB
    have hc34 : i32 c 12 ≤ 34 := hP.2.1
    have hq : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hb34 : b < 34 := by omega
    have hA : s₀.regs.get64 .rdi + s₀.regs.get64 .r11 + 18446744073709551614#64
        = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * N + (b + 1)) := by
      rw [hdi, h11]; exact t1_aI _ N b 1
    have LB := t1_B_load hB (76 + 34 * N + (b + 1)) 1 (by omega)
    rw [← hA] at LB
    have hy := t1_i8_rd c (76 + 34 * N + (b + 1)) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [LB, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    case vc2 =>
      t1_jump "ff_ps_read_data.L14cc"
      exact ⟨⟨c, f, (t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r)).1, hB.2.2.2.2.2,
        fun hp => ⟨(hW hp).1.1.1, (hW hp).1.1.2.1⟩⟩, by t1r; exact hB.2.2.1⟩
    case vc3 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [h9, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      t1_jump "ff_ps_read_data.L12ef"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), fun hp => t1_W1_row (hW hp).1 hN4
        (t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)) (by simp only [i32] at *; omega)⟩,
        ⟨hN.1, by t1r; exact hN.2⟩⟩
    case vc4 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [h9, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      exact ⟨⟨c, f, N, b, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hN.1, by t1r; exact hN.2⟩,
        h4, hc0, by t1r; exact hcx, by t1r; exact hdi, by t1r; exact hsi, by t1r; exact h9,
        by t1r; exact h10, by t1r; exact hdx, by t1r; exact h11, hb4,
        by have hbc' : (b : Int) + 1 < i32 c 12 := hbc
           have heq' : ¬ ((i32 c 12).toNat = 2 + b) := heq
           omega,
        fun hp => ⟨(hW hp).1, t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)⟩⟩, by var_step⟩

theorem t1_b32 (b : Nat) (hb : b < 34) (h : BitVec.ofNat 64 b - BitVec.setWidth 64 32#64 = 0#64) :
    b = 32 := by
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  simp only [BitVec.toNat_ofNat] at h2
  omega

set_option maxRecDepth 20000 in
/-- Trap `b = 32`; band `b + 2` of row `N` of `iid`: `|iid| ≤ 7 + 8 iid_quant`, else the error (`0x14cc`). -/
theorem blk_L1298 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1298" := by
  cfg_block
  measure_hb "L1298"
    intro n
    simp only [tab_L1298, var_L1298, tab_L12c5, var_L12c5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, b, hB, hN, h4, hc0, hcx, hdi, hsi, h9, h10, hdx, h11, hb4, hbc, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hP := t1_B_inv hB
    have hc34 : i32 c 12 ≤ 34 := hP.2.1
    have hq : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hb34 : b < 34 := by omega
    have hA : s₀.regs.get64 .rdi + s₀.regs.get64 .r11 + 18446744073709551615#64
        = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * N + (b + 2)) := by
      rw [hdi, h11]; exact t1_aI _ N b 2
    have LB := t1_B_load hB (76 + 34 * N + (b + 2)) 1 (by omega)
    rw [← hA] at LB
    have hy := t1_i8_rd c (76 + 34 * N + (b + 2)) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [LB, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    case vc1 =>
      exfalso; rename_i htr; rw [h11] at htr
      have h3 := t1_b32 b hb34 htr
      have hbc' : (b : Int) + 2 < i32 c 12 := hbc
      have hc34' : i32 c 12 ≤ 34 := hc34
      omega
    case vc3 =>
      t1_jump "ff_ps_read_data.L14cc"
      exact ⟨⟨c, f, (t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r)).1, hB.2.2.2.2.2,
        fun hp => ⟨(hW hp).1.1.1, (hW hp).1.1.2.1⟩⟩, by t1r; exact hB.2.2.1⟩
    case vc4 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [hsi, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      t1_jump "ff_ps_read_data.L12ef"
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), fun hp => t1_W1_row (hW hp).1 hN4
        (t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)) (by simp only [i32] at *; omega)⟩,
        ⟨hN.1, by t1r; exact hN.2⟩⟩
    case vc5 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [hsi, hcx, h11, t1_d0 _ _ _ (by omega) (by omega) (by omega)] at heq
      exact ⟨⟨c, f, N, b, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hN.1, by t1r; exact hN.2⟩,
        h4, hc0, by t1r; exact hcx, by t1r; exact hdi, by t1r; exact hsi, by t1r; exact h9,
        by t1r; exact h10, by t1r; exact hdx, by t1r; exact h11, hb4,
        by have hbc' : (b : Int) + 2 < i32 c 12 := hbc
           have heq' : ¬ ((i32 c 12).toNat = 3 + b) := heq
           omega,
        fun hp => ⟨(hW hp).1, t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)⟩⟩, by var_step⟩

theorem t1_aJ (a : BitVec 64) (N b : Nat) :
    a + BitVec.ofNat 64 (34 * N + 0x4f) + BitVec.ofNat 64 b
      = a + BitVec.ofNat 64 (76 + 34 * N + (b + 3)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem t1_e4 (b : Nat) : BitVec.setWidth 64 4#64 + BitVec.ofNat 64 b = BitVec.ofNat 64 (b + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem t1_d4 (M b : Nat) (hM : M < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 M - (BitVec.setWidth 64 4#64 + BitVec.ofNat 64 b) = 0#64) ↔ M = 4 + b := by
  rw [t1_e4]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

theorem t1_v4 (M b : Nat) (hM : M < 2 ^ 32) (hbM : b + 4 ≤ M) :
    (BitVec.ofNat 64 M - (BitVec.setWidth 64 4#64 + BitVec.ofNat 64 b)).toNat
      < (BitVec.ofNat 64 M - BitVec.ofNat 64 b).toNat := by
  rw [t1_e4]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
/-- Band `b + 3` of row `N` of `iid`; then `b + 4` (`0x1252`) or row done (`0x12ef`). -/
theorem blk_L12c5 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L12c5" := by
  cfg_block
  measure_hb "L12c5"
    intro n
    simp only [tab_L12c5, var_L12c5, tab_L1252, var_L1252]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, N, b, hB, hN, h4, hc0, hcx, hdi, hsi, h9, h10, hdx, h11, hb4, hbc, hW⟩, hn⟩ := hs₀
    have hl := t1_B_len hB
    have hN4 : N ≤ 4 := hB.2.2.2.1
    have hP := t1_B_inv hB
    have hc34 : i32 c 12 ≤ 34 := hP.2.1
    have hq : i32 c 8 = 0 ∨ i32 c 8 = 1 := hP.2.2.2.2.2.2
    have hb34 : b < 34 := by omega
    have hA : s₀.regs.get64 .rdi + s₀.regs.get64 .r11
        = arg2 t₀ + BitVec.ofNat 64 (76 + 34 * N + (b + 3)) := by
      rw [hdi, h11]; exact t1_aJ _ N b
    have LB := t1_B_load hB (76 + 34 * N + (b + 3)) 1 (by omega)
    rw [← hA] at LB
    have hy := t1_i8_rd c (76 + 34 * N + (b + 3)) (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals t1norm at *
    all_goals try t1cc at *
    all_goals try simp only [LB, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    case vc2 =>
      t1_jump "ff_ps_read_data.L14cc"
      exact ⟨⟨c, f, (t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r)).1, hB.2.2.2.2.2,
        fun hp => ⟨(hW hp).1.1.1, (hW hp).1.1.2.1⟩⟩, by t1r; exact hB.2.2.1⟩
    case vc4 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [hcx, h11, t1_d4 _ _ (by omega) (by omega)] at heq
      rw [tg_L12ef]
      refine ⟨?_, by var_step⟩
      exact ⟨c, f, N, ⟨t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), fun hp => t1_W1_row (hW hp).1 hN4
        (t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)) (by simp only [i32] at *; omega)⟩,
        ⟨hN.1, by t1r; exact hN.2⟩⟩
    case vc3 =>
      rename_i heq hlt
      try simp only [BitVec.setWidth_replaceLow8, t1_sw8, t1_sw8b, BitVec.setWidth_32_64_32] at hlt
      rw [hcx, h11, t1_d4 _ _ (by omega) (by omega)] at heq
      have hM4 : b + 4 < (i32 c 12).toNat := by
        have hbc' : (b : Int) + 3 < i32 c 12 := hbc
        have heq' : ¬ ((i32 c 12).toNat = 4 + b) := heq
        omega
      left; refine Table.ofLabels_at (l := "ff_ps_read_data.L1252") ⟨rfl, ?_, Or.inl ?_⟩
      · exact ⟨c, f, N, b + 4, t1_B_eq hB rfl (by t1r) (by t1r) (by t1r) (by t1r), ⟨hN.1, by t1r; exact hN.2⟩,
          h4, hc0, by t1r; exact hcx, by t1r; exact hdi, by t1r; exact hsi, by t1r; exact h9,
          by t1r; exact h10, by t1r; exact hdx, by t1r; rw [h11, t1_e4], by omega,
          by have hbc' : (b : Int) + 3 < i32 c 12 := hbc
             have heq' : ¬ ((i32 c 12).toNat = 4 + b) := heq
             push_cast; omega,
          fun hp => ⟨(hW hp).1, t1_row_succ (hW hp).2 (t1_band c _ _ _ hdx hq hlt hy)⟩⟩
      · simp only [lex_var]
        try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        refine Kraken.lex_cons_lt_cons (by lex_len) ?_
        refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
        rw [hcx, h11]
        rw [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
        exact t1_v4 (i32 c 12).toNat b (by have hc34' : i32 c 12 ≤ 34 := hc34; omega) (by omega)

end Kraken.Examples.Sbr.Ps

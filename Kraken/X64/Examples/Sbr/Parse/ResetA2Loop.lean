import Kraken.X64.Examples.Sbr.Parse.ResetA2Mk2
import Kraken.X64.Examples.Sbr.Parse.ResetA2Pfx

/-!
# `sbr_reset`, shard A2: the 8-wide loop of the first `make_bands` (`L1850` .. `L18ca`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]


omit [CodeEnv] in
theorem a2_sw16_ofInt32 (c : Int) : (BitVec.ofInt 32 c).setWidth 16 = BitVec.ofInt 16 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem a2_sw32_toInt (X : BitVec 64) : X.setWidth 32 = BitVec.ofInt 32 X.toInt := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_bmod]
  simp only [Int.bmod_def]
  have := X.isLt
  split <;> omega

omit [CodeEnv] in
theorem a2_toInt16 (c : Int) (h1 : -32768 ≤ c) (h2 : c < 32768) : (BitVec.ofInt 16 c).toInt = c := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod_def]; split <;> omega

omit [CodeEnv] in
theorem a2_sub16 (X : BitVec 64) (b : Int) :
    ((X.setWidth 32 - BitVec.ofInt 32 b).setWidth 64).setWidth 16 = BitVec.ofInt 16 (X.toInt - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_bmod,
    Int.bmod_def]
  have := X.isLt
  split <;> omega

omit [CodeEnv] in
theorem a2_pv_pos {b : BitVec 32} {s i : Nat} (h : i ≠ 0) :
    A2.pv b s i = (BitVec.f32toi64 (chain b (A2.fl s) i)).toInt := by
  simp only [A2.pv, h, ↓reduceIte]

omit [CodeEnv] in
theorem a2_mb_lt {b : BitVec 32} {s t nb i : Nat} (h : i < nb) :
    A2.mb b s t nb i = A2.pv b s i - A2.pv b s (i - 1) := by
  simp only [A2.mb, h, ↓reduceIte]

omit [CodeEnv] in
theorem a2_pv_range {pw : BitVec 32 → BitVec 32 → BitVec 32} {s t nb i : Nat}
    (hBA : BandsAt pw s t nb) (hs : s ≤ 64) (h : i < nb) :
    0 ≤ A2.pv (A2.bOf pw s t nb) s i ∧ A2.pv (A2.bOf pw s t nb) s i ≤ 64 := by
  by_cases h0 : i = 0
  · subst h0; simp only [A2.pv, ↓reduceIte]; omega
  · rw [a2_pv_pos h0]; exact hBA i (by omega) h

omit [CodeEnv] in
theorem a2_MB_wr {fr : List UInt8} {o : Nat} {b : BitVec 32} {s t nb j : Nat} (v : Int)
    (hlen : o + 2 * (j + 1) + 2 ≤ fr.length) (hMB : A2.MB fr o b s t nb j)
    (hv : (BitVec.ofInt 16 v).toInt = A2.mb b s t nb (j + 1)) :
    A2.MB (wr fr (o + 2 * (j + 1)) (Int.toBytes 2 v)) o b s t nb (j + 1) := by
  intro i h1 hi
  rw [a2_fv_wr fr o (j + 1) i v hlen]
  split
  · subst_vars; exact hv
  · exact hMB i h1 (by omega)

omit [CodeEnv] in
theorem a2_reg16 (X Y : BitVec 64) :
    ((X.setWidth 32 - Y.setWidth 32).setWidth 64).setWidth 16 = BitVec.ofInt 16 (X.toInt - Y.toInt) := by
  rw [a2_sw32_toInt Y]; exact a2_sub16 X _

omit [CodeEnv] in
theorem a2_mb_eq {b : BitVec 32} {s t nb i : Nat} (h1 : 2 ≤ i) (h : i < nb) :
    A2.mb b s t nb i = (BitVec.f32toi64 (chain b (A2.fl s) i)).toInt
      - (BitVec.f32toi64 (chain b (A2.fl s) (i - 1))).toInt := by
  rw [a2_mb_lt h, a2_pv_pos (by omega), a2_pv_pos (by omega)]

omit [CodeEnv] in
theorem a2_mb_rng {pw : BitVec 32 → BitVec 32 → BitVec 32} {s t nb i : Nat}
    (hBA : BandsAt pw s t nb) (hs : s ≤ 64) (h1 : 1 ≤ i) (h : i < nb) :
    -32768 ≤ A2.mb (A2.bOf pw s t nb) s t nb i ∧ A2.mb (A2.bOf pw s t nb) s t nb i < 32768 := by
  rw [a2_mb_lt h]
  have := a2_pv_range hBA hs h
  have := a2_pv_range (i := i - 1) hBA hs (by omega)
  omega

omit [CodeEnv] in
/-- The value check of a 2-byte store of `mb`. -/
theorem a2_st16 {pw : BitVec 32 → BitVec 32 → BitVec 32} {s t nb i : Nat}
    (hBA : BandsAt pw s t nb) (hs : s ≤ 64) (h1 : 1 ≤ i) (h : i < nb) (R : BitVec 16)
    (hR : R = BitVec.ofInt 16 (A2.mb (A2.bOf pw s t nb) s t nb i)) :
    (BitVec.ofInt 16 R.toInt).toInt = A2.mb (A2.bOf pw s t nb) s t nb i := by
  have := a2_mb_rng hBA hs h1 h
  rw [BitVec.ofInt_toInt, hR, a2_toInt16 _ this.1 this.2]

omit [CodeEnv] in
theorem a2_SF_wr2 {fr : List UInt8} {e : REnv} {a : RArgs} {t₀ : MachineData} {k0 k2 : Nat}
    (p : Nat) (v : Int) (h : p + 2 ≤ fr.length) (hd : p + 2 ≤ rb 0x100) (hS : A2.SF fr e a t₀ k0 k2) :
    A2.SF (wr fr p (Int.toBytes 2 v)) e a t₀ k0 k2 := by
  obtain ⟨⟨⟨⟨⟨⟨h80, h88⟩, h38⟩, h50, h40⟩, h30⟩, h100⟩, h48⟩ := hS
  simp only [rb] at hd
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h80
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h88
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h38
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h50
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb]; omega)]; exact h40
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb]; omega)]; exact h30
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h100
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb]; omega)]; exact h48

omit [CodeEnv] in
theorem a2_mul2 (d : Nat) : BitVec.ofNat 64 d * 2#64 = BitVec.ofNat 64 (2 * d) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem a2_arr_addr_366 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 366 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 1)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_364 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 364 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 2)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_362 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 362 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 3)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_360 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 360 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 4)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_358 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 358 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 5)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_356 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 356 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 6)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_354 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 354 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 7)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr_addr_352 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 352 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 8)) := by
  rw [a2_mul2]; bv_omega

set_option maxRecDepth 100000 in
theorem blk_L1850 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1850" ⟨"sbr_reset.L1850", B.L1850, some "sbr_reset.L1886"⟩ := by
  info_off
  measure_hb "L1850"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, h14, hax, hcx, hsi, hlo0, d, hdx, hd8, hdle, h13, hlo1, hMB⟩, hm⟩⟩ :=
      T.L1850.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    simp only [B.L1850]
    vcgen
    all_goals rename_i s1 hs1
    all_goals subst hs1
    all_goals simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
    refine ⟨T.L1886.mpr ?_, ?_⟩
    rotate_left
    · rw [← hn]; simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact Nat.le_refl _
    refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, ?_, ?_, ?_, ?_, ?_, d, ?_, hd8, hdle, ?_, ?_, hMB, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, lo32, RegZmms.get_set_xmm_same,
      RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true, a2_lo_app]
    all_goals first | assumption | rfl

set_option maxRecDepth 100000 in
theorem blk_L1886 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1886" ⟨"sbr_reset.L1886", B.L1886, some "sbr_reset.L18b8"⟩ := by
  info_off
  measure_hb "L1886"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, h14, hax, hcx, hsi, hlo0, d, hdx, hd8, hdle, h13, hlo1, hMB,
        hdi, hr8, hr9, hr10, hr11, hbx⟩, hm⟩⟩ := T.L1886.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
    have hk0 : k0N a row ≤ 64 := by omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 366 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 1)) :=
      a2_arr_addr_366 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 364 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 2)) :=
      a2_arr_addr_364 _ d
    have hl1 := a2_vk_load hm hF (o := 1024) (i := d + 1) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1024) (i := d + 1) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1024 + 2 * (d + 1)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1024) (i := d + 2) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1024) (i := d + 2) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1024 + 2 * (d + 2)) (n := 2) (by omega) w
    have c7 : chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) (d + 7)
        = BitVec.f32mul (A2.b0 e a (k0N a row) k2) (chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) (d + 6)) :=
      rfl
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1886]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl1]; rfl
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl2]; rfl
    case vc3 =>
      rename_i s1 hs1
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      have hdb' : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
      refine ⟨T.L18b8.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L18b8, VD.L1886, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, h9, ?_, ?_, ?_, ?_, ?_,
          d, ?_, hd8, hdle, ?_, ?_,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB ?_) ?_,
          ?_, ?_, ?_, ?_, ?_⟩, st2 _ _⟩⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h14
      · exact hax
      · exact hcx
      · exact hsi
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hdx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 7) (by omega), c7]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c7]
      · rw [h13]; apply a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 1) hBA hk0 (by omega) (by omega)
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 1) (by omega), hdi, Nat.add_sub_cancel]
      · rw [a2_reg16]; apply a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 2) hBA hk0 (by omega) (by omega)
        rw [hr8, hdi, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 2) (by omega) (by omega), show d + 2 - 1 = d + 1 by omega]
      · rw [a2_reg16, hr9, hr8, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 3) (by omega) (by omega), show d + 3 - 1 = d + 2 by omega]
      · rw [a2_reg16, hr10, hr9, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 4) (by omega) (by omega), show d + 4 - 1 = d + 3 by omega]
      · rw [a2_reg16, hr11, hr10, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 5) (by omega) (by omega), show d + 5 - 1 = d + 4 by omega]
      · rw [a2_reg16, hbx, hr11, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 6) (by omega) (by omega), show d + 6 - 1 = d + 5 by omega]
      · simp only [sw32_64, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_reg16, ← c7, hbx, a2_mb_eq (nb := A2.n0N e a (k0N a row) k2) (i := d + 7) (by omega) (by omega), show d + 7 - 1 = d + 6 by omega]

set_option maxRecDepth 100000 in
theorem blk_L18b8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L18b8" ⟨"sbr_reset.L18b8", B.L18b8, some "sbr_reset.L18ca"⟩ := by
  info_off
  measure_hb "L18b8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, h14, hax, hcx, hsi, hlo0, d, hdx, hd8, hdle, h12, hlo1, hMB,
        hr9, hr10, hr11, hbx, hr15⟩, hm⟩⟩ := T.L18b8.mp hs
    clear hs
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
    have hk0 : k0N a row ≤ 64 := by omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 362 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 3)) := a2_arr_addr_362 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 360 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 4)) := a2_arr_addr_360 _ d
    have hl1 := a2_vk_load hm hF (o := 1024) (i := d + 3) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1024) (i := d + 3) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1024 + 2 * (d + 3)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1024) (i := d + 4) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1024) (i := d + 4) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1024 + 2 * (d + 4)) (n := 2) (by omega) w
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L18b8]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl1]; rfl
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl2]; rfl
    case vc3 =>
      rename_i s1 hs1
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      have hdb' : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
      refine ⟨T.L18ca.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L18ca, VD.L18b8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, h9, h14, hax, hcx, hsi, hlo0,
          d, hdx, hd8, hdle, h12, hlo1,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 3) hBA hk0 (by omega) (by omega) _ hr9))
            (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 4) hBA hk0 (by omega) (by omega) _ hr10),
          hr11, hbx, hr15⟩, st2 _ _⟩⟩

set_option maxRecDepth 100000 in
theorem blk_L18ca (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L18ca" ⟨"sbr_reset.L18ca", B.L18ca, some "sbr_reset.L18db"⟩ := by
  info_off
  measure_hb "L18ca"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, h14, hax, hcx, hsi, hlo0, d, hdx, hd8, hdle, h12, hlo1, hMB,
        hr11, hbx, hr15⟩, hm⟩⟩ := T.L18ca.mp hs
    clear hs
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
    have hk0 : k0N a row ≤ 64 := by omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 358 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 5)) := a2_arr_addr_358 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 356 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 6)) := a2_arr_addr_356 _ d
    have hl1 := a2_vk_load hm hF (o := 1024) (i := d + 5) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1024) (i := d + 5) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1024 + 2 * (d + 5)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1024) (i := d + 6) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1024) (i := d + 6) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1024 + 2 * (d + 6)) (n := 2) (by omega) w
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L18ca]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl1]; rfl
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      rw [hl2]; rfl
    case vc3 =>
      rename_i s1 hs1
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, Option.isSome_some, ea1, ea2]
      have hdb' : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
      refine ⟨T.L18db.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L18db, VD.L18ca, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, h9, h14, hax, hcx, hsi, hlo0,
          d, hdx, hd8, hdle, h12, hlo1,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 5) hBA hk0 (by omega) (by omega) _ hr11))
            (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 6) hBA hk0 (by omega) (by omega) _ hbx),
          hr15⟩, st2 _ _⟩⟩

end Kraken.Examples.Sbr.Reset

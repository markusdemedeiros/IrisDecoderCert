import Kraken.X64.Examples.Sbr.Parse.ResetA2Loop

/-!
# `sbr_reset`, shard A2: the 8-wide loop of the second `make_bands` (`L2130` .. `L21a9`)
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
theorem a2_TB_wr2 {fr : List UInt8} {t₀ : MachineData} {k1 n0 n1 : Nat} {vm : Int} (p : Nat) (v : Int)
    (h : p + 2 ≤ fr.length) (hd : p + 2 ≤ rb 0x88) (hd' : rb 0x100 + 8 ≤ p) (hT : A2.TB fr t₀ k1 n0 n1 vm) :
    A2.TB (wr fr p (Int.toBytes 2 v)) t₀ k1 n0 n1 vm := by
  obtain ⟨hA, h80, h38, h100⟩ := hT
  simp only [rb] at hd hd'
  refine ⟨a2_ta_wr p v h (by simp only [rb]; omega) hA, ?_, ?_, ?_⟩
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb]; omega)]; exact h80
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb]; omega)]; exact h38
  · unfold frSlot64; rw [a2_slice_wr2 fr p _ _ v h (Or.inl (by simp only [rb]; omega))]; exact h100

omit [CodeEnv] in
theorem a2_arr2_addr_238 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 238 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 1)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_236 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 236 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 2)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_234 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 234 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 3)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_232 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 232 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 4)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_230 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 230 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 5)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_228 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 228 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 6)) := by
  rw [a2_mul2]; bv_omega

set_option maxRecDepth 100000 in
theorem blk_L2130 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2130" ⟨"sbr_reset.L2130", B.L2130, some "sbr_reset.L2166"⟩ := by
  info_off
  measure_hb "L2130"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm', hTB, h30, d, hdx, hd8, hdle, h13, hlo1, hMB⟩, hm⟩⟩ := T.L2130.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    simp only [B.L2130]
    vcgen
    all_goals rename_i s1 hs1
    all_goals subst hs1
    all_goals simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
    refine ⟨T.L2166.mpr ?_, ?_⟩
    rotate_left
    · rw [← hn]; simp only [lex_var, VD.L2166, VD.L2130, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact Nat.le_refl _
    refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, ?_, ?_, h9, ?_, ?_, vm, hvm, hvm', hTB, h30, d, ?_, hd8, hdle, ?_, ?_,
        hMB, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩⟩
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, lo32, RegZmms.get_set_xmm_same,
      RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true, a2_lo_app]
    all_goals first | assumption | rfl

set_option maxRecDepth 100000 in
theorem blk_L2166 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2166" ⟨"sbr_reset.L2166", B.L2166, some "sbr_reset.L2197"⟩ := by
  info_off
  measure_hb "L2166"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm', hTB, h30, d, hdx, hd8, hdle,
        h13, hlo1, hMB, hdi, hr8, hr9, hr10, hr11, hbx⟩, hm⟩⟩ := T.L2166.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt).2.2
    have hn0 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
    have hk0 : A2.k1Of (k0N a row) k2 ≤ 64 := by simp only [A2.k1Of]; split <;> omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 238 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 1)) :=
      a2_arr2_addr_238 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 236 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 2)) :=
      a2_arr2_addr_236 _ d
    have hl1 := a2_vk_load hm hF (o := 1152) (i := d + 1) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1152) (i := d + 1) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1152 + 2 * (d + 1)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1152) (i := d + 2) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1152) (i := d + 2) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1152 + 2 * (d + 2)) (n := 2) (by omega) w
    have c7 : chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) (d + 7)
        = BitVec.f32mul (A2.b1 e a (k0N a row) k2) (chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) (d + 6)) :=
      rfl
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2166]
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
      have hdb' : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      refine ⟨T.L2197.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L2197, VD.L2166, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc),
          hN0, hN1, ?_, ?_, ?_, h9, ?_, ?_, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          d, ?_, hd8, hdle, ?_, ?_,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB ?_) ?_,
          ?_, ?_, ?_, ?_, ?_⟩, st2 _ _⟩⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hsi
      · exact hcx
      · exact hdx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 7) (by omega), c7]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c7]
      · rw [h13]; apply a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 1) hBA hk0 (by omega) (by omega)
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 1) (by omega), hdi, Nat.add_sub_cancel]
      · rw [a2_reg16]; apply a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 2) hBA hk0 (by omega) (by omega)
        rw [hr8, hdi, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 2) (by omega) (by omega), show d + 2 - 1 = d + 1 by omega]
      · rw [a2_reg16, hr9, hr8, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 3) (by omega) (by omega), show d + 3 - 1 = d + 2 by omega]
      · rw [a2_reg16, hr10, hr9, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 4) (by omega) (by omega), show d + 4 - 1 = d + 3 by omega]
      · rw [a2_reg16, hr11, hr10, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 5) (by omega) (by omega), show d + 5 - 1 = d + 4 by omega]
      · rw [a2_reg16, hbx, hr11, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 6) (by omega) (by omega), show d + 6 - 1 = d + 5 by omega]
      · simp only [sw32_64, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_reg16, ← c7, hbx, a2_mb_eq (nb := A2.n1N e a (k0N a row) k2) (i := d + 7) (by omega) (by omega), show d + 7 - 1 = d + 6 by omega]

set_option maxRecDepth 100000 in
theorem blk_L2197 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2197" ⟨"sbr_reset.L2197", B.L2197, some "sbr_reset.L21a9"⟩ := by
  info_off
  measure_hb "L2197"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm', hTB, h30, d, hdx, hd8, hdle, h12, hlo1, hMB, hr9, hr10, hr11, hbx, hax⟩, hm⟩⟩ := T.L2197.mp hs
    clear hs
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt).2.2
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
    have hk0 : A2.k1Of (k0N a row) k2 ≤ 64 := by simp only [A2.k1Of]; split <;> omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 234 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 3)) := a2_arr2_addr_234 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 232 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 4)) := a2_arr2_addr_232 _ d
    have hl1 := a2_vk_load hm hF (o := 1152) (i := d + 3) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1152) (i := d + 3) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1152 + 2 * (d + 3)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1152) (i := d + 4) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1152) (i := d + 4) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1152 + 2 * (d + 4)) (n := 2) (by omega) w
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2197]
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
      have hdb' : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      refine ⟨T.L21a9.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L21a9, VD.L2197, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc),
          hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          d, hdx, hd8, hdle, h12, hlo1,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 3) hBA hk0 (by omega) (by omega) _ hr9))
            (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 4) hBA hk0 (by omega) (by omega) _ hr10),
          hr11, hbx, hax⟩, st2 _ _⟩⟩

set_option maxRecDepth 100000 in
theorem blk_L21a9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L21a9" ⟨"sbr_reset.L21a9", B.L21a9, some "sbr_reset.L21ba"⟩ := by
  info_off
  measure_hb "L21a9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm', hTB, h30, d, hdx, hd8, hdle, h12, hlo1, hMB, hr11, hbx, hax⟩, hm⟩⟩ := T.L21a9.mp hs
    clear hs
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt).2.2
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
    have hk0 : A2.k1Of (k0N a row) k2 ≤ 64 := by simp only [A2.k1Of]; split <;> omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 230 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 5)) := a2_arr2_addr_230 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 228 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 6)) := a2_arr2_addr_228 _ d
    have hl1 := a2_vk_load hm hF (o := 1152) (i := d + 5) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1152) (i := d + 5) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1152 + 2 * (d + 5)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1152) (i := d + 6) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1152) (i := d + 6) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1152 + 2 * (d + 6)) (n := 2) (by omega) w
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L21a9]
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
      have hdb' : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      refine ⟨T.L21ba.mpr ?_, ?_⟩
      rotate_left
      · rw [← hn]; simp only [lex_var, VD.L21ba, VD.L21a9, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _
      refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc),
          hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          d, hdx, hd8, hdle, h12, hlo1,
          a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 5) hBA hk0 (by omega) (by omega) _ hr11))
            (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 6) hBA hk0 (by omega) (by omega) _ hbx),
          hax⟩, st2 _ _⟩⟩

end Kraken.Examples.Sbr.Reset

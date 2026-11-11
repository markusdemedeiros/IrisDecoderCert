import Kraken.X64.Examples.Sbr.Parse.ResetA2Loop2

/-!
# `sbr_reset`, shard A2: the back edges of the two 8-wide `make_bands` loops (`L18db`, `L21ba`)
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
theorem a2_inc8 (d : Nat) : BitVec.setWidth 64 8#64 + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + 8) := by
  rw [BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.ofNat_add d 8).symm

omit [CodeEnv] in
theorem a2_zx32 (Y : BitVec 64) : ((Y.setWidth 32).setWidth 64).setWidth 32 = Y.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

set_option maxRecDepth 100000 in
theorem blk_L18db (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L18db" ⟨"sbr_reset.L18db", B.L18db, some "sbr_reset.L1908"⟩ := by
  info_off
  measure_hb "L18db"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h9, h14, hax, hcx, hsi, hlo0, d, hdx, hd8, hdle, h12, hlo1, hMB,
        hr15⟩, hm⟩⟩ := T.L18db.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hdb : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
    have hk0 : k0N a row ≤ 64 := by omega
    have hD64 : (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 < 2 ^ 64 := by omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 354 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 7)) := a2_arr_addr_354 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 352 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (d + 8)) := a2_arr_addr_352 _ d
    have hl1 := a2_vk_load hm hF (o := 1024) (i := d + 7) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1024) (i := d + 7) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1024 + 2 * (d + 7)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1024) (i := d + 8) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1024) (i := d + 8) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1024 + 2 * (d + 8)) (n := 2) (by omega) w
    have c8 : chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) (d + 8)
        = BitVec.f32mul (A2.b0 e a (k0N a row) k2) (chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) (d + 7)) :=
      rfl
    have hinc := a2_inc8 d
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L18db]
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
      rename_i s1 hs1 hc
      subst hs1 hP
      have hdb' : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, hinc, Option.isSome_some, ea1, ea2,
        CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hne : ¬ ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8) := by
        intro h
        first
          | (have hd : decide ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8) = true := decide_eq_true h
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
          | (have hd : decide (d + 8 = (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8) = true := decide_eq_true h.symm
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1850.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, h9, ?_, ?_, ?_, ?_, ?_,
          d + 8, ?_, by omega, by show d + 8 + 8 ≤ (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8; omega, ?_, ?_,
          (a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 7) hBA hk0 (by omega) (by omega) _ hr15)) ?_)⟩, st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h14
      · exact hax
      · exact hcx
      · exact hsi
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 8) (by omega), c8]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c8]
      · rw [h12]; apply a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 8) hBA hk0 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32]
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 8) (by omega), c8, show d + 8 - 1 = d + 7 by omega]
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L1850, VD.L18db, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, hinc]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (d + 8) % 2 ^ 64 = d + 8 := Nat.mod_eq_of_lt (by omega)
        have h2 : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
        have h3 : (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 % 2 ^ 64
            = (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 := Nat.mod_eq_of_lt hD64
        rw [h1, h2, h3]
        omega
    case vc4 =>
      rename_i s1 hs1 hc
      subst hs1 hP
      have hdb' : d + 8 ≤ A2.n0N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, hinc, Option.isSome_some, ea1, ea2,
        CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hDe : (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8 := by
        first
          | (simpa using hc)
          | (simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at hc; omega)
      refine ⟨T.L1908.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_⟩, st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h14
      · exact hax
      · exact hcx
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · rw [hDe]
      · rw [hDe]; simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 8) (by omega), c8]
      · rw [hDe]; simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c8]
      · rw [hDe]; refine a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
          (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 7) hBA hk0 (by omega) (by omega) _ hr15)) ?_
        rw [h12]; apply a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := d + 8) hBA hk0 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32]
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 8) (by omega), c8, show d + 8 - 1 = d + 7 by omega]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
theorem a2_arr2_addr_226 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 226 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 7)) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_arr2_addr_224 (r : BitVec 64) (d : Nat) :
    r - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 224 % 2 ^ 64)
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 8)) := by
  rw [a2_mul2]; bv_omega

set_option maxRecDepth 100000 in
theorem blk_L21ba (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L21ba" ⟨"sbr_reset.L21ba", B.L21ba, some "sbr_reset.L21e6"⟩ := by
  info_off
  measure_hb "L21ba"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h9, hsi, hcx, vm, hvm, hvm', hTB, h30, d, hdx, hd8, hdle,
        h12, hlo1, hMB, hrax⟩, hm⟩⟩ := T.L21ba.mp hs
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
    have hD64 : (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 < 2 ^ 64 := by omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 226 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 7)) := a2_arr2_addr_226 _ d
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 d * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 224 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (d + 8)) := a2_arr2_addr_224 _ d
    have hl1 := a2_vk_load hm hF (o := 1152) (i := d + 7) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1152) (i := d + 7) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1152 + 2 * (d + 7)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1152) (i := d + 8) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1152) (i := d + 8) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1152 + 2 * (d + 8)) (n := 2) (by omega) w
    have c8 : chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) (d + 8)
        = BitVec.f32mul (A2.b1 e a (k0N a row) k2) (chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) (d + 7)) :=
      rfl
    have hinc := a2_inc8 d
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L21ba]
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
      rename_i s1 hs1 hc
      subst hs1 hP
      have hdb' : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n1N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
        show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hm0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, hinc, Option.isSome_some, ea1, ea2,
        CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hne : ¬ ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8) := by
        intro h
        first
          | (have hd : decide ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8) = true := decide_eq_true h
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
          | (have hd : decide (d + 8 = (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8) = true := decide_eq_true h.symm
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2130.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc),
          hN0, hN1, ?_, ?_, ?_, h9, ?_, ?_, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          d + 8, ?_, by omega, by show d + 8 + 8 ≤ (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8; omega, ?_, ?_,
          (a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
            (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 7) hBA hk0 (by omega) (by omega) _ hrax)) ?_)⟩, st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hsi
      · exact hcx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 8) (by omega), c8]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c8]
      · rw [h12]; apply a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 8) hBA hk0 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32]
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 8) (by omega), c8, show d + 8 - 1 = d + 7 by omega]
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L2130, VD.L21ba, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi, hinc]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (d + 8) % 2 ^ 64 = d + 8 := Nat.mod_eq_of_lt (by omega)
        have h2 : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
        have h3 : (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 % 2 ^ 64
            = (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 := Nat.mod_eq_of_lt hD64
        rw [h1, h2, h3]
        omega
    case vc4 =>
      rename_i s1 hs1 hc
      subst hs1 hP
      have hdb' : d + 8 ≤ A2.n1N e a (k0N a row) k2 - 1 := by omega
      have hn0' : A2.n1N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
        show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hm0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, hinc, Option.isSome_some, ea1, ea2,
        CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hDe : (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 = d + 8 := by
        first
          | (simpa using hc)
          | (simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at hc; omega)
      refine ⟨T.L21e6.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt,
          a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc),
          hN0, hN1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          ?_⟩, st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hcx
      · rw [hDe]
      · rw [hDe]; simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := d + 8) (by omega), c8]
      · rw [hDe]; simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [c8]
      · rw [hDe]; refine a2_MB_wr _ (by rw [hF1 _]; omega) (a2_MB_wr _ (by rw [hF]; omega) hMB
          (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 7) hBA hk0 (by omega) (by omega) _ hrax)) ?_
        rw [h12]; apply a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := d + 8) hBA hk0 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32]
        rw [a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := d + 8) (by omega), c8, show d + 8 - 1 = d + 7 by omega]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset

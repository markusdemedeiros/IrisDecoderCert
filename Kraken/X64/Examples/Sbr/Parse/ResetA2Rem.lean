import Kraken.X64.Examples.Sbr.Parse.ResetA2Loop3

/-!
# `sbr_reset`, shard A2: the remainder loops of `make_bands` (`L1920`, `L2200`)
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
theorem a2_rem_addr (r : BitVec 64) (D i : Nat) (_hD : D < 1000) (_hi : i < 1000) :
    r - 8#64 - 366#64 + BitVec.ofNat 64 (2 * D) + BitVec.ofNat 64 i * 2#64
      = r - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (D + (i + 1))) := by
  rw [a2_mul2]; bv_omega

omit [CodeEnv] in
theorem a2_MB_idx {fr : List UInt8} {o : Nat} {b : BitVec 32} {s t nb j j' : Nat} (h : j = j')
    (hM : A2.MB fr o b s t nb j) : A2.MB fr o b s t nb j' := h ▸ hM

omit [CodeEnv] in
theorem a2_MB_wr2 {fr : List UInt8} {o : Nat} {b : BitVec 32} {s t nb j j' : Nat} (hj : j' = j + 1) (v : Int)
    (hlen : o + 2 * j' + 2 ≤ fr.length) (hMB : A2.MB fr o b s t nb j)
    (hv : (BitVec.ofInt 16 v).toInt = A2.mb b s t nb j') :
    A2.MB (wr fr (o + 2 * j') (Int.toBytes 2 v)) o b s t nb j' := by
  subst hj; exact a2_MB_wr v hlen hMB hv

omit [CodeEnv] in
theorem a2_st16_last {pw : BitVec 32 → BitVec 32 → BitVec 32} {s t nb : Nat}
    (hBA : BandsAt pw s t nb) (hs : s ≤ 64) (ht : t ≤ 64) (h1 : 1 ≤ nb) (R : BitVec 16)
    (hR : R = BitVec.ofInt 16 (A2.mb (A2.bOf pw s t nb) s t nb nb)) :
    (BitVec.ofInt 16 R.toInt).toInt = A2.mb (A2.bOf pw s t nb) s t nb nb := by
  have := a2_pv_range (i := nb - 1) hBA hs (by omega)
  have hm : A2.mb (A2.bOf pw s t nb) s t nb nb = t - A2.pv (A2.bOf pw s t nb) s (nb - 1) := by
    simp only [A2.mb, Nat.lt_irrefl, ↓reduceIte]
  rw [BitVec.ofInt_toInt, hR, a2_toInt16 _ (by omega) (by omega)]

set_option maxRecDepth 100000 in
theorem blk_L1920 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1920" ⟨"sbr_reset.L1920", B.L1920, some "sbr_reset.L194b"⟩ := by
  info_off
  measure_hb "L1920"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h14, hax, hcx, hlo0, hsi, hdx, i, hdi, hi, h13, hlo1, hMB⟩, hm⟩⟩ := T.L1920.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).1 hN0.1).2
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hi' : i < (A2.n0N e a (k0N a row) k2 - 1) % 8 := hi
    have hk0 : k0N a row ≤ 64 := by omega
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 64 := by simp only [A2.k1Of]; split <;> omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 - 366#64 + BitVec.ofNat 64 (2 * ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8)) + BitVec.ofNat 64 i * 2#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1))) :=
      a2_rem_addr _ _ _ (by omega) (by omega)
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2 - 1) * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 366 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1024 + 2 * (A2.n0N e a (k0N a row) k2 - 1 + 1)) := a2_arr_addr_366 _ _
    have hl1 := a2_vk_load hm hF (o := 1024) (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1024) (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1024 + 2 * ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1))) (n := 2) (by omega) v
    have hF1' := fun v => fr_wr_len hF (o := 1024 + 2 * ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i + 1)) (n := 2) (by omega) v
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1024) (i := A2.n0N e a (k0N a row) k2 - 1 + 1) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1024) (i := A2.n0N e a (k0N a row) k2 - 1 + 1) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1024 + 2 * (A2.n0N e a (k0N a row) k2 - 1 + 1)) (n := 2) (by omega) w
    have cI : chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) = BitVec.f32mul (A2.b0 e a (k0N a row) k2) (chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i)) := rfl
    have hinc1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1920]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hdi, hax, Option.isSome_some, ea1, ea2]
      rw [hl1]; rfl
    case vc3 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hdi, hax, Option.isSome_some, ea1, ea2]
      rw [hl2]; rfl
    case vc2 =>
      rename_i s1 hs1 hc
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hdi, hax, Option.isSome_some, ea1, ea2, hinc1, hcx, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hi' : i < (A2.n0N e a (k0N a row) k2 - 1) % 8 := hi
      have hne : ¬ ((A2.n0N e a (k0N a row) k2 - 1) % 8 = i + 1) := by
        intro h
        first
          | (have hd : decide ((A2.n0N e a (k0N a row) k2 - 1) % 8 = i + 1) = true := decide_eq_true h
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
          | (have hd : decide (i + 1 = (A2.n0N e a (k0N a row) k2 - 1) % 8) = true := decide_eq_true h.symm
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1920.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF, hN0, ?_, ?_, ?_, ?_, ?_, ?_,
          i + 1, ?_, by show i + 1 < (A2.n0N e a (k0N a row) k2 - 1) % 8; omega, ?_, ?_,
          a2_MB_wr (j := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i) _ (by rw [hF]; omega) hMB (a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) hBA hk0 (by omega) (by omega) _ (by
            simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
            rw [h13, a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI,
              show (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) - 1 = (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i by omega]))⟩, st1 _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h14
      · exact hax
      · exact hcx
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hsi
      · exact hdx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [cI]
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L1920, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdi, hcx, hinc1]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (i + 1) % 2 ^ 64 = i + 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
        have h3 : (A2.n0N e a (k0N a row) k2 - 1) % 8 % 2 ^ 64 = (A2.n0N e a (k0N a row) k2 - 1) % 8 := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2, h3]
        omega
    case vc4 =>
      rename_i s1 hs1 hc
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hdi, hax, Option.isSome_some, ea1, ea2, hinc1, hcx, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hi' : i < (A2.n0N e a (k0N a row) k2 - 1) % 8 := hi
      have hDe : (A2.n0N e a (k0N a row) k2 - 1) % 8 = i + 1 := by
        first
          | (simpa using hc)
          | (simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at hc; omega)
      have hDe' : (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) = A2.n0N e a (k0N a row) k2 - 1 := by omega
      have cL : chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) (A2.n0N e a (k0N a row) k2 - 1) = BitVec.f32mul (A2.b0 e a (k0N a row) k2) (chain (A2.b0 e a (k0N a row) k2) (A2.fl (k0N a row)) ((A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i)) := by
        rw [← cI, hDe']
      refine ⟨T.L194b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, a2_SF_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega)
          (a2_SF_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) hSF), hN0, ?_, ?_,
          a2_MB_idx (show A2.n0N e a (k0N a row) k2 - 1 + 1 = A2.n0N e a (k0N a row) k2 by omega) <| a2_MB_wr (j := A2.n0N e a (k0N a row) k2 - 1) _ (by rw [hF1 _]; omega) (a2_MB_idx hDe' (a2_MB_wr2 (j := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i) (j' := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) _ (by rw [hF]; omega) hMB ?_)) ?_⟩,
          st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact hax
      · exact hsi
      · apply a2_st16 (nb := A2.n0N e a (k0N a row) k2) (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) hBA hk0 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
        rw [h13, a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI,
          show (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) - 1 = (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 + i by omega]
      · try rw [show A2.n0N e a (k0N a row) k2 - 1 + 1 = A2.n0N e a (k0N a row) k2 by omega]
        apply a2_st16_last hBA hk0 hk1 (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
        rw [a2_reg16, h14, a2_toInt_ofNat64 (by omega), A2.mb]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rw [a2_pv_pos (i := A2.n0N e a (k0N a row) k2 - 1) (by omega), cL]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
theorem a2_rem_addr2 (r : BitVec 64) (D i : Nat) (_hD : D < 1000) (_hi : i < 1000) :
    r - 8#64 - 238#64 + BitVec.ofNat 64 (2 * D) + BitVec.ofNat 64 i * 2#64
      = r - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (D + (i + 1))) := by
  rw [a2_mul2]; bv_omega

set_option maxRecDepth 100000 in
theorem blk_L2200 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2200" ⟨"sbr_reset.L2200", B.L2200, some "sbr_reset.L2230"⟩ := by
  info_off
  measure_hb "L2200"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, hcx, hdx, i, hsi, hi, h13, hlo1, vm, hvm, hvm', hTB, h30, hMB⟩, hm⟩⟩ := T.L2200.mp hs
    clear hs
    simp only [lo32] at hlo0 hlo1
    have hBA := ((a2_bands_of hB hC hrow hk2 hk02 hkq hu).2 hlt).2.2
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hi' : i < (A2.n1N e a (k0N a row) k2 - 1) % 8 := hi
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 64 := by simp only [A2.k1Of]; split <;> omega
    have ea1 : t₀.regs.get64 .rsp - 8#64 - 238#64 + BitVec.ofNat 64 (2 * ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8)) + BitVec.ofNat 64 i * 2#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1))) :=
      a2_rem_addr2 _ _ _ (by omega) (by omega)
    have e100a : t₀.regs.get64 .rsp - 8#64 + 18446744073709551360#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    have e100b : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 (2 ^ 64 - 256 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    have ea2 : t₀.regs.get64 .rsp - 8#64 + BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2 - 1) * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 238 % 2 ^ 64)
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (1152 + 2 * (A2.n1N e a (k0N a row) k2 - 1 + 1)) := a2_arr2_addr_238 _ _
    have hl1 := a2_vk_load hm hF (o := 1152) (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) rfl
    have st1 := a2_vk_store hm hF (o := 1152) (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) rfl
    have hF1 := fun v => fr_wr_len hF (o := 1152 + 2 * ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1))) (n := 2) (by omega) v
    have hl100 := fun v => fr_load (st1 v) (hF1 v) (d := 0x100) (n := 8) (by omega) (by omega)
    have h100 : ∀ v, BitVec.ofInt 64 (Int.ofBytes (slice (wr fr (1152 + 2 * ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1))) (Int.toBytes 2 v)) (rb 0x100) 8))
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2 - 1) := fun v => by
      rw [a2_slice_wr2 fr _ _ _ v (by rw [hF]; omega) (Or.inl (by simp only [rb]; omega))]; exact hTB.2.2.2
    have hl2 := fun v => a2_vk_load (st1 v) (hF1 v) (o := 1152) (i := A2.n1N e a (k0N a row) k2 - 1 + 1) (by omega) rfl
    have st2 := fun v => a2_vk_store (st1 v) (hF1 v) (o := 1152) (i := A2.n1N e a (k0N a row) k2 - 1 + 1) (by omega) rfl
    have hF2 := fun v w => fr_wr_len (hF1 v) (o := 1152 + 2 * (A2.n1N e a (k0N a row) k2 - 1 + 1)) (n := 2) (by omega) w
    have cI : chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) = BitVec.f32mul (A2.b1 e a (k0N a row) k2) (chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i)) := rfl
    have hinc1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2200]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, Option.isSome_some, ea1, e100a, e100b]
      rw [hl1]; rfl
    case vc3 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, Option.isSome_some, ea1, e100a, e100b, hl100]
    case vc4 =>
      rename_i s1 hs1 hc v hv
      subst hs1
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, Option.isSome_some, ea1, e100a, e100b, hl100] at hv ⊢
      obtain rfl := Option.some.inj hv
      simp only [h100, ea2]
      rw [hl2]; rfl
    case vc2 =>
      rename_i s1 hs1 hc
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, Option.isSome_some, ea1, e100a, e100b, hinc1, hcx, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hn1' : A2.n1N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
        show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hi' : i < (A2.n1N e a (k0N a row) k2 - 1) % 8 := hi
      have hne : ¬ ((A2.n1N e a (k0N a row) k2 - 1) % 8 = i + 1) := by
        intro h
        first
          | (have hd : decide ((A2.n1N e a (k0N a row) k2 - 1) % 8 = i + 1) = true := decide_eq_true h
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
          | (have hd : decide (i + 1 = (A2.n1N e a (k0N a row) k2 - 1) % 8) = true := decide_eq_true h.symm
             simp only [hd, Bool.not_true, Bool.false_eq_true] at hc)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2200.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        ⟨hk2v, hk1v, hlt, a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc, hN0, hN1, ?_, ?_, ?_, ?_, ?_,
          i + 1, ?_, by show i + 1 < (A2.n1N e a (k0N a row) k2 - 1) % 8; omega, ?_, ?_, vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB,
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30,
          a2_MB_wr (j := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i) _ (by rw [hF]; omega) hMB (a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) hBA hk1 (by omega) (by omega) _ (by
            simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
            rw [h13, a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI,
              show (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) - 1 = (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i by omega]))⟩, st1 _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
      · exact hcx
      · exact hdx
      · simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [a2_sw32_toInt, a2_pv_pos (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI]
      · simp only [lo32, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1]
        rw [cI]
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L2200, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsi, hcx, hinc1]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (i + 1) % 2 ^ 64 = i + 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
        have h3 : (A2.n1N e a (k0N a row) k2 - 1) % 8 % 2 ^ 64 = (A2.n1N e a (k0N a row) k2 - 1) % 8 := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2, h3]
        omega
    case vc5 =>
      rename_i s1 hs1 hc v hv
      subst hs1 hP
      simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, reduceCtorEq,
        ↓reduceIte, Reg64s.get64_set64, hdx, hsi, Option.isSome_some, ea1, e100a, e100b, hl100, hinc1, hcx, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      simp only [h100, ea2]
      rw [a2_beq_ofNat _ _ (by omega) (by omega)] at hc
      have hn1' : A2.n1N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
        show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hn0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hi' : i < (A2.n1N e a (k0N a row) k2 - 1) % 8 := hi
      have hDe : (A2.n1N e a (k0N a row) k2 - 1) % 8 = i + 1 := by
        first
          | (simpa using hc)
          | (simp only [Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq] at hc; omega)
      have hDe' : (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) = A2.n1N e a (k0N a row) k2 - 1 := by omega
      have cL : chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) (A2.n1N e a (k0N a row) k2 - 1) = BitVec.f32mul (A2.b1 e a (k0N a row) k2) (chain (A2.b1 e a (k0N a row) k2) (A2.fl (A2.k1Of (k0N a row) k2)) ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i)) := by
        rw [← cI, hDe']
      refine ⟨T.L2230.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2 _ _,
        ⟨hk2v, hk1v, hlt, a2_inc_wr2 _ (by rw [hF1 _]; omega) (Or.inl (by omega)) (a2_inc_wr2 _ (by rw [hF]; omega) (Or.inl (by omega)) hInc), hN0, hN1, ?_,
          a2_MB_idx (show A2.n1N e a (k0N a row) k2 - 1 + 1 = A2.n1N e a (k0N a row) k2 by omega) <| a2_MB_wr (j := A2.n1N e a (k0N a row) k2 - 1) _ (by rw [hF1 _]; omega) (a2_MB_idx hDe' (a2_MB_wr2 (j := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i) (j' := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega) _ (by rw [hF]; omega) hMB ?_)) ?_,
          vm, hvm, hvm',
          a2_TB_wr2 _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega)
            (a2_TB_wr2 _ _ (by rw [hF]; omega) (by simp only [rb]; omega) (by simp only [rb]; omega) hTB),
          by rw [a2_slot64_wr _ _ _ _ (by rw [hF1 _]; omega) (by simp only [rb]; omega),
            a2_slot64_wr _ _ _ _ (by rw [hF]; omega) (by simp only [rb]; omega)]; exact h30⟩,
          st2 _ _⟩⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h15
      · apply a2_st16 (nb := A2.n1N e a (k0N a row) k2) (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) hBA hk1 (by omega) (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
        rw [h13, a2_sub16, a2_mb_lt (by omega), a2_pv_pos (i := (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1)) (by omega), cI,
          show (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + (i + 1) - 1 = (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 + i by omega]
      · try rw [show A2.n1N e a (k0N a row) k2 - 1 + 1 = A2.n1N e a (k0N a row) k2 by omega]
        apply a2_st16_last hBA hk1 hk2 (by omega)
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true, a2_lo_app, a2_ex0_eq_sw, hlo0, hlo1, a2_zx32, BitVec.setWidth_eq]
        rw [a2_reg16, h14, a2_toInt_ofNat64 (by omega), A2.mb]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        rw [a2_pv_pos (i := A2.n1N e a (k0N a row) k2 - 1) (by omega), cL]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset

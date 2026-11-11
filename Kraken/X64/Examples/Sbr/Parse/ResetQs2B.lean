import Kraken.X64.Examples.Sbr.Parse.ResetQsLib

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the interval test and the median loads (`L19b0`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option hygiene false in
/-- The two interval tests of `L19b0` (`c1`, `c2`) as facts on `lo`, `hi1`. -/
local macro "qs2_cond" : tactic => `(tactic| (
  simp only [hsi', hdx', AddrIndex.offset64_none, AddrIndex.offset64_scale1,
    AddrIndex.offset64_scale2, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
    Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, qs_sh2,
    Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at c1 c2
  rw [cc_nc_sub] at c1 c2
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, tsi, tdx, t8] at c1 c2))

theorem blk_L19b0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L19b0" ⟨"sbr_reset.L19b0", B.L19b0, some "sbr_reset.L19dd"⟩ := by
  info_off
  measure_hb "L19b0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, -⟩⟩, hm⟩⟩ := T.L19b0.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    clear hsi hdx
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hrs := rsp_ok hC
    have hW := qw_cur hQ
    simp only at hW
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have tsi := ep_toNat hR' (o := 0x400) (q := lo) (by omega)
    have tdx := epm2_toNat hR' (o := 0x400) (hi1 := hi1) (by omega)
    have hl1 := av_load hm hF (o := 0x400) (q := lo) (by omega)
    have hl2 := av_load hm hF (o := 0x400) (q := hi1 - 1) (by omega)
    have hl3 := av_load hm hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have t8 : (QS.ep t₀ 0x400 hi1 - 2#64 + 18446744073709551614#64).toNat
        = (t₀.regs.get64 .rsp).toNat - 0x578 + (0x400 + 2 * hi1) - 2 := by
      rw [sub2_toNat _ (by omega), tdx]
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L19b0]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      AddrIndex.offset64_scale2, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, qs_sh2,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hsi',
        hdx']
    · -- `start ≥ end`: pop
      rename_i c1
      simp only [hsi', hdx'] at c1
      rw [cc_nc_sub] at c1
      simp only [decide_eq_true_eq, tsi, tdx] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, hcx, hD, hR, hSR, qw_drop hQ⟩⟩, hm⟩⟩, Or.inl ?_⟩
      simp only [lex_var, VD.L1980, VD.L19b0]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [stkPhi_mk _ _ _ _ rfl, hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph]
      omega
    · -- two elements
      rename_i c1 c2
      qs2_cond
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1ba0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, by omega⟩⟩, hm⟩⟩, Or.inr
            ⟨?_, ?_⟩⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
        hax, hcx, hsi', hdx']; done)
      · simp only [lex_var, VD.L1ba0, VD.L19b0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      · simp only [lex_var]; decide
    · rw [hl1]; rfl
    · rename_i c1 c2 _ _ _ _ _
      qs2_cond
      rw [ep_sub2 _ _ _ (by omega), hl2]; rfl
    · rename_i c1 c2 _ _ _ _ _ _ _
      qs2_cond
      rw [qs_mid_addr hR' (by omega) (by omega), hl3]; rfl
    rename_i c1 c2 _ _ _ v1 h1 v2 h2 v3 h3
    qs2_cond
    simp only [hsi', hdx', AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      AddrIndex.offset64_scale2, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, qs_sh2,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat] at h1 h2 h3
    rw [hl1, Option.some.injEq] at h1
    rw [ep_sub2 _ _ _ (by omega), hl2, Option.some.injEq] at h2
    rw [qs_mid_addr hR' (by omega) (by omega), hl3, Option.some.injEq] at h3
    subst h1 h2 h3
    have e4 := ep_sub4 t₀ 0x400 hi1 (by omega)
    have em := qs_mid_addr hR' (o := 0x400) (lo := lo) (hi1 := hi1) (by omega) (by omega)
    refine ⟨T.L19dd.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, by omega, ?_, ?_, ?_, ?_,
          ?_⟩⟩, hm⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
      hax, hcx, hsi', hdx', e4, em, sw16_zx, av_bytes]; done)
    simp only [lex_var, VD.L19dd, VD.L19b0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    exact Nat.le_refl _

end Kraken.Examples.Sbr.Reset

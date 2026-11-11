import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib2

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the median of three, second half (`L1a10`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L1a10 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a10" ⟨"sbr_reset.L1a10", B.L1a10, some "sbr_reset.L1a1f"⟩ := by
  info_off
  measure_hb "L1a10"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A, A0, lo, hi1, pos, hcx, hD, hDc, hR,
        hSR, hQ, hAv, hsi, hdx, h3, h8, hdi, h9, hpos⟩⟩, hm⟩⟩ := T.L1a10.mp hs
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
    have hmid : QS.mid lo (hi1 - 1) + 1 ≤ hi1 - 1 := by unfold QS.mid; omega
    have hposN : lo ≤ pos ∧ pos < hi1 := by
      rcases hpos with h | h <;> rw [h] <;> (try unfold QS.mid) <;> omega
    have hb := hQ.2.bounds (P := fun v => -64 ≤ v ∧ v ≤ 64) (fun q hq => hR.1 q hq) pos
      (by omega)
    have hpv : (BitVec.ofInt 16 (A pos)).toInt = A pos := toInt_ofInt16 (by omega) (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have ho : 0x400 + 2 * (lo + 1) + 2 ≤ 0x470 := by omega
    have hm' := av_store hm hF (o := 0x400) (q := lo) (by omega) (BitVec.ofInt 16 (A pos)).toInt
    have hF' := fr_wr_len hF (o := 0x400 + 2 * (lo + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (A pos)).toInt
    have hSF' := (sf_wr hF ho (BitVec.ofInt 16 (A pos)).toInt).mpr hSF
    have hSR' := (stk_wr hF (o' := 0x400 + 2 * (lo + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (A pos)).toInt (t₀ := t₀) (o := 0x400) (S := S) (by omega)
      (by omega)).mpr hSR
    have hAv1 : ∀ r, QS.av (wr fr (0x400 + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (A pos)).toInt)) 0x400 r = swap A lo pos r := fun r => by
      rw [av_wr hF (by omega) _ r, hpv, ← upd_upd_swap]
      simp only [Parse.Qsort.upd, hAv]
    have hQ' : QW (A2.n0N e a _ _) (QS.av (wr fr (0x400 + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (A pos)).toInt)) 0x400) A0 (S ++ [(lo, hi1)]) :=
      ⟨hQ.1, ((qw_swap hQ (i := lo) (j := pos) (by simp only [InIv]; omega)
        (by simp only [InIv]; omega)).2).congr hAv1⟩
    have hl0 := av_load hm hF (o := 0x400) (q := lo) (by omega)
    have hl1 := av_load hm' hF' (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
    have hl2 := av_load hm' hF' (o := 0x400) (q := hi1 - 1) (by omega)
    have e2 := ep_sub2 t₀ 0x400 hi1 (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1a10]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [hsi', hdx', hdi, h9, e2, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    · rw [hl0]; rfl
    · rw [hl1]; rfl
    · rw [hl2]; rfl
    rename_i v1 h1 v2 h2 _
    simp only [hsi', hdx', hdi, h9, e2, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1 h2
    rw [hl1, Option.some.injEq] at h1
    rw [hl2, Option.some.injEq] at h2
    subst h1 h2
    refine ⟨T.L1a1f.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, _, hx, hsp, hfm, hF', ⟨hk2v, hk1v, hSF', hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR', hQ', ?_, ?_, h3, ?_, ?_, ?_, ?_⟩⟩,
        hm'⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
      hax, hcx, hsi', hdx', h8, hdi, sw16_zx, av_bytes]; done)
    simp only [lex_var, VD.L1a1f, VD.L1a10, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm' hF'
      (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
      (by omega) hSR' (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
    exact Nat.le_refl _

theorem blk_L1a1f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a1f" ⟨"sbr_reset.L1a1f", B.L1a1f,
      some "sbr_reset.L1a40"⟩ := by
  info_off
  measure_hb "L1a1f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h9, h14⟩⟩, hm⟩⟩ := T.L1a1f.mp hs
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
    have hmid : QS.mid lo (hi1 - 1) + 1 ≤ hi1 - 1 := by unfold QS.mid; omega
    have hmid0 : lo ≤ QS.mid lo (hi1 - 1) := by unfold QS.mid; omega
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have t9 := av_toInt fr 0x400 (QS.mid lo (hi1 - 1))
    have t14 := av_toInt fr 0x400 (hi1 - 1)
    -- the exchange of `mid` and `hi1 - 1`
    have ho1 : 0x400 + 2 * (hi1 - 1 + 1) + 2 ≤ 0x470 := by omega
    have ho2 : 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1) + 2 ≤ 0x470 := by omega
    have hl1 := av_load hm hF (o := 0x400) (q := hi1 - 1) (by omega)
    have hm1 := av_store hm hF (o := 0x400) (q := hi1 - 1) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt
    have hF1 := fr_wr_len hF (o := 0x400 + 2 * (hi1 - 1 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt
    have hl2 := av_load hm1 hF1 (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
    have hm2 := av_store hm1 hF1 (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt
    have hF2 := fr_wr_len hF1 (o := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt
    have hSF2 := (sf_wr hF1 ho2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt).mpr
      ((sf_wr hF ho1 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt).mpr hSF)
    have hSR2 := (stk_wr hF1 (o' := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt (t₀ := t₀) (o := 0x400) (S := S)
      (by omega) (by omega)).mpr ((stk_wr hF (o' := 0x400 + 2 * (hi1 - 1 + 1)) (n := 2)
      (by omega) (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt (t₀ := t₀)
      (o := 0x400) (S := S) (by omega) (by omega)).mpr hSR)
    have hAv2 : ∀ r, QS.av (wr (wr fr (0x400 + 2 * (hi1 - 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt))
        (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt)) 0x400 r
        = swap (QS.av fr 0x400) (QS.mid lo (hi1 - 1)) (hi1 - 1) r := fun r => by
      rw [av_wr hF1 (by omega) _ r, t14, ← upd_upd_swap]
      simp only [Parse.Qsort.upd]
      rw [av_wr hF (o := 0x400) (q := hi1 - 1) (by omega) _ r, t9]
      rfl
    have hsw : QS.av (wr (wr fr (0x400 + 2 * (hi1 - 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt))
        (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt)) 0x400
        (QS.mid lo (hi1 - 1)) = QS.av fr 0x400 (hi1 - 1) := by
      rw [hAv2, swap_eq, ite_eq_left_of_eq_true _ _ (eq_self _)]
    have hQ2 := (qw_swap hQ (i := QS.mid lo (hi1 - 1)) (j := hi1 - 1)
      (by simp only [InIv]; omega) (by simp only [InIv]; omega))
    have hQ2' : QW (A2.n0N e a _ _) (QS.av (wr (wr fr (0x400 + 2 * (hi1 - 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt))
        (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 1))).toInt)) 0x400) A0
        (S ++ [(lo, hi1)]) := ⟨hQ2.1, hQ2.2.congr hAv2⟩
    have e2 := ep_sub2 t₀ 0x400 hi1 (by omega)
    have e6' : QS.ep t₀ 0x400 (hi1 - 1) + 18446744073709551612#64 = QS.ep t₀ 0x400 (hi1 - 3) := by
      rw [← e2]; exact ep_sub6 t₀ 0x400 hi1 (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1a1f]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [hsi', hdx', hdi, h9, h14, e2, e6', AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl1]; rfl) | (rw [hl2]; rfl) | skip
    · -- `A mid ≤ A (hi1 - 1)`: in order
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a40.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h3, h8, hdi,
            h9⟩⟩, hm⟩⟩, Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      simp only [lex_var, VD.L1a40, VD.L1a1f]
      rw [stkPhi_mk _ _ _ _ rfl]
    · -- exchanged, `lo + 4 ≤ hi1`
      rename_i _ _ c2
      simp only [hsi', hdx', e2, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
        BitVec.add_zero, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        Nat.reduceMod, Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq,
        ↓reduceIte, BitVec.ofNat_eq_ofNat] at c2
      rw [e6', cc_nz_sub] at c2
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at c2
      rw [ep_inj hR' (by omega) (by omega)] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a50.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, h3, ?_, ?_, by omega,
            ?_, ?_⟩⟩, hm2⟩⟩, Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8, hdi, e6', hsw, h14]; done)
      simp only [lex_var, VD.L1a50, VD.L1a1f, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
    · -- exchanged, `lo + 3 = hi1`: done, pop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, ?_, hD, hR, hSR2, qw_drop hQ2'⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx]; done)
      simp only [lex_var, VD.L1980, VD.L1a1f, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm2 hF2
        (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
        (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)]
      omega

theorem blk_L1a40 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a40" ⟨"sbr_reset.L1a40", B.L1a40, some "sbr_reset.L1a50"⟩ := by
  info_off
  measure_hb "L1a40"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h9⟩⟩, hm⟩⟩ := T.L1a40.mp hs
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
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpl := phi_le (S := S) (fun J hJ => hQ.1 J (by simp [hJ]))
    have hwB := ep_wB hR' (o := 0x400) hW.1 (by omega)
    have hΦ : QS.stkPhi s₀ (s₀.regs.get64 .rcx).toNat
        + wBn 2 (s₀.regs.get64 .rsi).toNat (s₀.regs.get64 .rdx).toNat
        = phi S + (2 * (hi1 - lo) + 1) := by
      rw [hcx, hsi', hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph, hwB]; rfl
    have hpl' : phi S ≤ 6 * 99 := Nat.le_trans hpl (Nat.mul_le_mul hS6 (by omega))
    have e6 := ep_sub6 t₀ 0x400 hi1 (by omega)
    simp only [B.L1a40]
    vcgen
    all_goals subst s₀
    all_goals simp only [hsi', hdx', e6, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    · -- `lo + 3 = hi1`: done, pop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1980.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, hcx, hD, hR, hSR, qw_drop hQ⟩⟩, hm⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx]; done)
      simp only [lex_var, VD.L1980, VD.L1a40, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hΦ]
      refine lex_head_lt ?_ (by omega)
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]), hcx,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hph]
      omega
    · rename_i c1
      simp only [hsi', hdx', AddrIndex.offset64_none, AddrIndex.offset64_scale1,
        BitVec.add_zero, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        Nat.reduceMod, Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq,
        ↓reduceIte, BitVec.ofNat_eq_ofNat] at c1
      rw [e6, cc_z_sub] at c1
      simp only [decide_eq_false_iff_not] at c1
      rw [ep_inj hR' (by omega) (by omega)] at c1
      refine ⟨T.L1a50.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_, by omega,
            ?_, ?_⟩⟩, hm⟩⟩, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8, hdi, e6, h9, sw16_zx32]; done)
      simp only [lex_var, VD.L1a50, VD.L1a40, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      exact Nat.le_refl _

theorem blk_L1a50 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a50" ⟨"sbr_reset.L1a50", B.L1a50,
      some "sbr_reset.L1a70"⟩ := by
  info_off
  measure_hb "L1a50"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h4, h14, h9⟩⟩, hm⟩⟩ := T.L1a50.mp hs
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
    have hmid : QS.mid lo (hi1 - 1) + 1 ≤ hi1 - 1 := by unfold QS.mid; omega
    have hmid0 : lo ≤ QS.mid lo (hi1 - 1) := by unfold QS.mid; omega
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hl0 := av_load hm hF (o := 0x400) (q := hi1 - 2) (by omega)
    have hlm := av_load hm hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
    have hl2g : ∀ v : Int, loadInt (storeInt s₀.dmem (QS.ep t₀ 0x400 (QS.mid lo (hi1 - 1))) 2 v)
        (QS.ep t₀ 0x400 (hi1 - 2)) 2 = some (Int.ofBytes (slice (wr fr
          (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (Int.toBytes 2 v)) (0x400 + 2 * (hi1 - 2 + 1))
          2)) := fun v =>
      av_load (av_store hm hF (by omega) v)
        (fr_wr_len hF (o := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega) v)
        (by omega)
    have ea := ep_add2 t₀ 0x400 lo
    -- the exchange of `mid` and `hi1 - 2` (the pivot)
    have t2 := av_toInt fr 0x400 (hi1 - 2)
    have t9m := av_toInt fr 0x400 (QS.mid lo (hi1 - 1))
    have ho1 : 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1) + 2 ≤ 0x470 := by omega
    have ho2 : 0x400 + 2 * (hi1 - 2 + 1) + 2 ≤ 0x470 := by omega
    have hm1 := av_store hm hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt
    have hF1 := fr_wr_len hF (o := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt
    have hm2 := av_store hm1 hF1 (o := 0x400) (q := hi1 - 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt
    have hF2 := fr_wr_len hF1 (o := 0x400 + 2 * (hi1 - 2 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt
    have hSF2 := (sf_wr hF1 ho2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt).mpr
      ((sf_wr hF ho1 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt).mpr hSF)
    have hSR2 := (stk_wr hF1 (o' := 0x400 + 2 * (hi1 - 2 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt (t₀ := t₀) (o := 0x400)
      (S := S) (by omega) (by omega)).mpr ((stk_wr hF
      (o' := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt (t₀ := t₀)
      (o := 0x400) (S := S) (by omega) (by omega)).mpr hSR)
    have hAv2 : ∀ r, QS.av (wr (wr fr (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt))
        (0x400 + 2 * (hi1 - 2 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt)) 0x400 r
        = swap (QS.av fr 0x400) (hi1 - 2) (QS.mid lo (hi1 - 1)) r := fun r => by
      rw [av_wr hF1 (by omega) _ r, t9m, ← upd_upd_swap]
      simp only [Parse.Qsort.upd]
      rw [av_wr hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega) _ r, t2]
      rfl
    have hQ2 := (qw_swap hQ (i := hi1 - 2) (j := QS.mid lo (hi1 - 1))
      (by simp only [InIv]; omega) (by simp only [InIv]; omega))
    have hQ2' := And.intro hQ2.1 (hQ2.2.congr hAv2)
    generalize hf2 : wr (wr fr (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt))
        (0x400 + 2 * (hi1 - 2 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (QS.mid lo (hi1 - 1)))).toInt) = fr2
      at hm2 hF2 hSF2 hSR2 hAv2 hQ2'
    have hPI : QS.PInv (QS.av fr2 0x400) lo (hi1 - 1) (lo + 1) (hi1 - 3)
        (QS.av fr2 0x400 (hi1 - 2)) := by
      unfold QS.PInv
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rw [show hi1 - 1 - 1 = hi1 - 2 by omega]
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1a50]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [hsi', hdx', hdi, h8, h9, h14, ea, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl0]; rfl) | (rw [hlm]; rfl) | (rw [hl2g]; rfl) | skip
    · -- `lo + 1 ≤ hi1 - 3`: the partition loop
      rename_i v1 h1 _
      simp only [h8, AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
      rw [hl0, Option.some.injEq] at h1
      subst h1
      rw [sw16_zx, av_bytes fr 0x400 (hi1 - 2)]
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a89.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, ?_,
            lo + 1, hi1 - 3, _, hPI, ?_, ?_, by omega⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
        h15, hax, hcx, hsi', hdx', h8, h9]; done)
      simp only [lex_var, VD.L1a89, VD.L1a50, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      refine lex_phase_lt ?_ ?_
      · rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm2 hF2
          (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
          (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
      · rw [h9, ep_toNat hR' (o := 0x400) (q := hi1 - 3) (by omega),
          ep_toNat hR' (o := 0x400) (q := lo + 1) (by omega)]
        omega
    · -- `hi1 - 3 < lo + 1`: impossible
      rename_i _ _ c
      simp only [hsi', h9, ea, AddrIndex.offset64_none, BitVec.add_zero,
        Int64.toBitVec_ofNat_norm, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at c
      rw [cc_be_sub] at c
      simp only [decide_eq_false_iff_not] at c
      rw [ep_le_iff hR' (by omega) (by omega)] at c
      omega

end Kraken.Examples.Sbr.Reset

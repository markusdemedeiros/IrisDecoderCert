import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): the median of three (`L19dd`, `L1a00`, `L1a0c`, `L1a10`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

theorem blk_L19dd (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L19dd" ⟨"sbr_reset.L19dd", B.L19dd,
      some "sbr_reset.L1a00"⟩ := by
  info_off
  measure_hb "L19dd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h10, h14, h9⟩⟩, hm⟩⟩ := T.L19dd.mp hs
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
    have e2 := ep_sub2 t₀ 0x400 hi1 (by omega)
    have hl := av_load hm hF (o := 0x400) (q := hi1 - 1) (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have t10 := av_toInt fr 0x400 lo
    have t14 := av_toInt fr 0x400 (hi1 - 1)
    have t9 := av_toInt fr 0x400 (QS.mid lo (hi1 - 1))
    have hAv : ∀ r, QS.av (wr fr (0x400 + 2 * (hi1 - 1 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt)) 0x400 r
        = Parse.Qsort.upd (QS.av fr 0x400) (hi1 - 1) (QS.av fr 0x400 lo) r := fun r => by
      rw [av_wr hF (by omega) _ r, t10]
    generalize hA : QS.av fr 0x400 = A at hQ h10 h14 h9 t10 t14 t9 hAv
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L19dd]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [hsi', hdx', e2, h10, h14, h9, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    · -- `A lo ≤ A (hi1 - 1)`
      rename_i c1
      simp only [h10, h14] at c1
      rw [cc_le16, t10, t14] at c1
      simp only [decide_eq_true_eq] at c1
      subst hA
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a00.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h3, h8, hdi, h10, h14,
            h9⟩⟩, hm⟩⟩, Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      simp only [lex_var, VD.L1a00, VD.L19dd]
      rw [stkPhi_mk _ _ _ _ rfl]
    · -- `A (hi1 - 1) > A mid`
      rename_i c1 c2
      simp only [h10, h14, h9] at c1 c2
      rw [cc_le16, t10, t14] at c1
      rw [cc_g16, t14, t9] at c2
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c1 c2
      subst hA
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a0c.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax,
          ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ, hsi', hdx', h3, h8, hdi, h10,
            h9⟩⟩, hm⟩⟩, Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      simp only [lex_var, VD.L1a0c, VD.L19dd]
      rw [stkPhi_mk _ _ _ _ rfl]
    · rw [hl]; rfl
    · -- swap `lo`, `hi1 - 1` (first half)
      rename_i c1 c2
      simp only [h10, h14, h9] at c1 c2
      rw [cc_le16, t10, t14] at c1
      rw [cc_g16, t14, t9] at c2
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c1 c2
      have ho : 0x400 + 2 * (hi1 - 1 + 1) + 2 ≤ 0x470 := by omega
      have hm' := av_store hm hF (o := 0x400) (q := hi1 - 1) (by omega)
        (BitVec.ofInt 16 (A lo)).toInt
      have hF' := fr_wr_len hF (o := 0x400 + 2 * (hi1 - 1 + 1)) (n := 2) (by omega)
        (BitVec.ofInt 16 (A lo)).toInt
      have hSF' := (sf_wr hF ho (BitVec.ofInt 16 (A lo)).toInt).mpr hSF
      have hSR' := (stk_wr hF (o' := 0x400 + 2 * (hi1 - 1 + 1)) (n := 2) (by omega)
        (BitVec.ofInt 16 (A lo)).toInt (t₀ := t₀) (o := 0x400) (S := S) (by omega) (by
          omega)).mpr hSR
      subst hA
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a10.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF', ⟨hk2v, hk1v, hSF', hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, QS.av fr 0x400, A0, lo, hi1, hi1 - 1, ?_, hD, hDc, hR, hSR', hQ, hAv, ?_,
            ?_, h3, ?_, ?_, ?_, Or.inr rfl⟩⟩, hm'⟩⟩, Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
        hax, hcx, hsi', hdx', h8, hdi, sw16_zx32, h14]; done)
      simp only [lex_var, VD.L1a10, VD.L19dd, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm' hF'
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hrbp) hR' (by omega)
        hSR' (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]

theorem blk_L1a00 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a00" ⟨"sbr_reset.L1a00", B.L1a00, some "sbr_reset.L1a0c"⟩ := by
  info_off
  measure_hb "L1a00"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h10, h14, h9⟩⟩, hm⟩⟩ := T.L1a00.mp hs
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
    have t10 := av_toInt fr 0x400 lo
    have t9 := av_toInt fr 0x400 (QS.mid lo (hi1 - 1))
    simp only [B.L1a00]
    vcgen
    all_goals subst s₀
    all_goals simp only [hsi', hdx', h10, h14, h9, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    · -- `A lo ≤ A mid`: in order
      rename_i c1
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h10, h9] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1a1f.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩⟩, hm⟩⟩,
        Or.inr ⟨?_, by simp only [lex_var]; decide⟩⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
        hax, hcx, hsi', hdx', h8, hdi, h9, h14]; done)
      simp only [lex_var, VD.L1a1f, VD.L1a00, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
    · -- `A mid < A lo`
      refine ⟨T.L1a0c.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩⟩, hm⟩⟩,
        ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
        hax, hcx, hsi', hdx', h8, hdi, h9, h10]; done)
      simp only [lex_var, VD.L1a0c, VD.L1a00, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])]
      exact Nat.le_refl _

theorem blk_L1a0c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1a0c" ⟨"sbr_reset.L1a0c", B.L1a0c, some "sbr_reset.L1a10"⟩ := by
  info_off
  measure_hb "L1a0c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h3, h8, hdi, h10, h9⟩⟩, hm⟩⟩ := T.L1a0c.mp hs
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
    have hl := av_load hm hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have t10 := av_toInt fr 0x400 lo
    have hAv : ∀ r, QS.av (wr fr (0x400 + 2 * (QS.mid lo (hi1 - 1) + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt)) 0x400 r
        = Parse.Qsort.upd (QS.av fr 0x400) (QS.mid lo (hi1 - 1)) (QS.av fr 0x400 lo) r := fun r
          => by
      rw [av_wr hF (by omega) _ r, t10]
    have ho : 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1) + 2 ≤ 0x470 := by omega
    have hm' := av_store hm hF (o := 0x400) (q := QS.mid lo (hi1 - 1)) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt
    have hF' := fr_wr_len hF (o := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt
    have hSF' := (sf_wr hF ho (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt).mpr hSF
    have hSR' := (stk_wr hF (o' := 0x400 + 2 * (QS.mid lo (hi1 - 1) + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 lo)).toInt (t₀ := t₀) (o := 0x400) (S := S) (by omega)
      (by omega)).mpr hSR
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1a0c]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals simp only [hsi', hdx', hdi, h10, h9, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    · rw [hl]; rfl
    refine ⟨T.L1a10.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
      st, _, hx, hsp, hfm, hF', ⟨hk2v, hk1v, hSF', hN0, ?_, ?_, ?_,
        ⟨hN1, hN49, S, QS.av fr 0x400, A0, lo, hi1, QS.mid lo (hi1 - 1), ?_, hD, hDc, hR, hSR', hQ,
          hAv, ?_, ?_, h3, ?_, ?_, ?_, Or.inl rfl⟩⟩, hm'⟩⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12, h15,
      hax, hcx, hsi', hdx', h8, hdi, h9]; done)
    simp only [lex_var, VD.L1a10, VD.L1a0c, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), stkPhi_lit hm' hF'
      (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
      (by omega)
      hSR' (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]
    exact Nat.le_refl _

end Kraken.Examples.Sbr.Reset

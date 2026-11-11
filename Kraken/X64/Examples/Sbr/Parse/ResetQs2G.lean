import Kraken.X64.Examples.Sbr.Parse.ResetQs2Lib2

/-!
# `sbr_reset`, `AV_QSORT` copy 2 (`vk0`): placing the pivot (`L1ad4`)
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
/-- `L1ad4`: the loaded `A l` and the exchange in memory. -/
local macro "qs2_ad4_mem" : tactic => `(tactic| (
  try simp only [h10', AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
    Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat] at h1
  rw [hl, Option.some.injEq] at h1
  subst h1
  rw [sw16_zx, av_bytes fr 0x400 l]))

set_option hygiene false in
/-- `L1ad4`: the exit facts and the measure. -/
local macro "qs2_ad4_fin" : tactic => `(tactic| (
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, h12,
    h15, hax, hcx, hsi', hdx', h9', h10']; done)
  all_goals try simp only [lex_var, VD.L1b20, VD.L1af3, VD.L1ad4, Reg64s.get64_set64,
    reduceCtorEq, ↓reduceIte]
  all_goals refine lex_phase_lt ?_ ?_
  all_goals try decide
  all_goals rw [hcx, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := S.length) (by omega), stkPhi_lit hm2 hF2
    (by (try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]); exact hrbp) hR'
    (by omega) hSR2 (fun J hJ => hQ.1 J (by simp [hJ])) (by omega), hph]))

theorem blk_L1ad4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ad4" ⟨"sbr_reset.L1ad4", B.L1ad4, some "sbr_reset.L1af3"⟩ := by
  info_off
  measure_hb "L1ad4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    subst hn
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, ⟨hN1, hN49, S, A0, lo, hi1, hcx, hD, hDc, hR, hSR, hQ,
        hsi, hdx, h8, l, rt, pv, hPI, h10, h9, hlr, h14⟩⟩, hm⟩⟩ := T.L1ad4.mp hs
    clear hs
    have hsi' : s₀.regs.get64 .rsi = QS.ep t₀ 0x400 lo := hsi
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x400 hi1 - 2#64 := hdx
    have h8' : s₀.regs.get64 .r8 = QS.ep t₀ 0x400 (hi1 - 2) := h8
    have h10' : s₀.regs.get64 .r10 = QS.ep t₀ 0x400 l := h10
    have h9' : s₀.regs.get64 .r9 = QS.ep t₀ 0x400 rt := h9
    clear hsi hdx h8 h10 h9
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hW := qw_cur hQ
    simp only at hW
    have hrs := rsp_ok hC
    simp only [resetStkMin] at hrs
    have hR' : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by omega
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hph := stkPhi_eq hm hF hrbp hR' (o := 0x400) (by omega) hSR
      (fun J hJ => hQ.1 J (by simp [hJ])) (by omega)
    have hpv : QS.av fr 0x400 (hi1 - 2) = pv := by
      rw [← p5, show hi1 - 1 - 1 = hi1 - 2 by omega]
    subst hpv
    have hl := av_load hm hF (o := 0x400) (q := l) (by omega)
    have hl2g : ∀ v : Int, loadInt (storeInt s₀.dmem (QS.ep t₀ 0x400 l) 2 v)
        (QS.ep t₀ 0x400 (hi1 - 2)) 2 = some (Int.ofBytes (slice (wr fr
          (0x400 + 2 * (l + 1)) (Int.toBytes 2 v)) (0x400 + 2 * (hi1 - 2 + 1)) 2)) := fun v =>
      av_load (av_store hm hF (by omega) v)
        (fr_wr_len hF (o := 0x400 + 2 * (l + 1)) (n := 2) (by omega) v) (by omega)
    -- the exchange of `l` and `hi1 - 2`
    have tL := av_toInt fr 0x400 l
    have tP := av_toInt fr 0x400 (hi1 - 2)
    have ho1 : 0x400 + 2 * (l + 1) + 2 ≤ 0x470 := by omega
    have ho2 : 0x400 + 2 * (hi1 - 2 + 1) + 2 ≤ 0x470 := by omega
    have hm1 := av_store hm hF (o := 0x400) (q := l) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt
    have hF1 := fr_wr_len hF (o := 0x400 + 2 * (l + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt
    have hm2 := av_store hm1 hF1 (o := 0x400) (q := hi1 - 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt
    have hF2 := fr_wr_len hF1 (o := 0x400 + 2 * (hi1 - 2 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt
    have hSF2 := (sf_wr hF1 ho2 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt).mpr
      ((sf_wr hF ho1 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt).mpr hSF)
    have hSR2 := (stk_wr hF1 (o' := 0x400 + 2 * (hi1 - 2 + 1)) (n := 2) (by omega)
      (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt (t₀ := t₀) (o := 0x400)
      (S := S) (by omega) (by omega)).mpr ((stk_wr hF (o' := 0x400 + 2 * (l + 1)) (n := 2)
      (by omega) (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt (t₀ := t₀)
      (o := 0x400) (S := S) (by omega) (by omega)).mpr hSR)
    have hAv2 : ∀ r, QS.av (wr (wr fr (0x400 + 2 * (l + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt))
        (0x400 + 2 * (hi1 - 2 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt)) 0x400 r
        = swap (QS.av fr 0x400) (hi1 - 2) l r := fun r => by
      rw [av_wr hF1 (by omega) _ r, tL, ← upd_upd_swap]
      simp only [Parse.Qsort.upd]
      rw [av_wr hF (o := 0x400) (q := l) (by omega) _ r, tP]
      rfl
    have hQ2 := (qw_swap hQ (i := hi1 - 2) (j := l) (by simp only [InIv]; omega)
      (by simp only [InIv]; omega))
    have hQ2' := And.intro hQ2.1 (hQ2.2.congr hAv2)
    generalize hf2 : wr (wr fr (0x400 + 2 * (l + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 (hi1 - 2))).toInt))
        (0x400 + 2 * (hi1 - 2 + 1))
        (Int.toBytes 2 (BitVec.ofInt 16 (QS.av fr 0x400 l)).toInt) = fr2
      at hm2 hF2 hSF2 hSR2 hAv2 hQ2'
    have hPD : QS.PDone (QS.av fr2 0x400) lo (hi1 - 1) l rt := by
      unfold QS.PDone; omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1ad4]
    vcgen
    all_goals subst s₀
    all_goals subst hP
    all_goals try simp only [h9', h10', h8', h14, AddrIndex.offset64_none,
      BitVec.add_zero, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    all_goals first | (rw [hl]; rfl) | (rw [hl2g]; rfl) | skip
    · rename_i v1 h1 _ _
      qs2_ad4_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1b20.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, l, rt, hPD, ?_, ?_,
            trivial⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      qs2_ad4_fin
    · rename_i v1 h1 _ _ _
      qs2_ad4_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1af3.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, l, rt, hPD, ?_, ?_,
            trivial⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      qs2_ad4_fin
    · rename_i v1 h1 _ _ _ _
      qs2_ad4_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1b20.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, l, rt, hPD, ?_, ?_,
            trivial⟩⟩, hm2⟩⟩, Or.inl ?_⟩
      qs2_ad4_fin
    · rename_i v1 h1 _ _ _ _
      qs2_ad4_mem
      refine ⟨T.L1af3.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩,
        st, _, hx, hsp, hfm, hF2, ⟨hk2v, hk1v, hSF2, hN0, ?_, ?_, ?_,
          ⟨hN1, hN49, S, A0, lo, hi1, ?_, hD, hDc, hR, hSR2, hQ2', ?_, ?_, l, rt, hPD, ?_, ?_,
            trivial⟩⟩, hm2⟩⟩, Nat.le_of_lt ?_⟩
      qs2_ad4_fin

end Kraken.Examples.Sbr.Reset

import Kraken.X64.Examples.Sbr.Parse.ResetQs1Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): placing the pivot and the sortedness scan
(`L1424`, `L1442`, `L1450`, `L1467`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
theorem blk_L1442 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1442" ⟨"sbr_reset.L1442", B.L1442, some "sbr_reset.L1450"⟩ := by
  info_off
  measure_hb "L1442"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD,
        h9, h8, -⟩, hm⟩ := T.L1442.mp hs
    clear hs
    rw [V.L1442] at hn
    subst hn
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1442]
    vcgen
    all_goals subst s₀
    refine ⟨T.L1450.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
      hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_,
        l, rt, hPD, ?_, ?_, lo, Nat.le_refl _, by omega, ?_⟩, hmT.get⟩, ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact h9
    · regs_simp; exact h8
    · regs_simp; exact hdx
    · simp only [V.L1450, VD.L1450, VD.L1442]
      regs_simp
      exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)])
        (by decide))

set_option maxRecDepth 100000 in
theorem blk_L1450 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1450" ⟨"sbr_reset.L1450", B.L1450, some "sbr_reset.L1467"⟩ := by
  info_off
  measure_hb "L1450"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD,
        h9, h8, m, hlm, hmh, hdi⟩, hm⟩ := T.L1450.mp hs
    clear hs
    rw [V.L1450] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hrl := (t₀.regs.get64 .rsp).isLt
    have tcx := ep_m2_toNat hRs (o := 0x4fe) (q := hi1) (by omega)
    have tm := ep_toNat hRs (o := 0x4fe) (q := m) (by omega)
    have tm1 := ep_toNat hRs (o := 0x4fe) (q := m + 1) (by omega)
    have ea := q1_ep_add2 t₀ 0x4fe m
    have hl0 : (s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2).isSome = true := by
      rw [hdi, av_load hm hF (by omega)]; rfl
    have hl1 : (s₀.dmem.loadInt (s₀.regs.get64 .rdi + 2#64) 2).isSome = true := by
      rw [hdi, ea, av_load hm hF (by omega)]; rfl
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1450]
    vcgen
    all_goals subst s₀
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq]
    · -- `m ≥ hi1 - 1`: to L1467
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1467.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_,
          l, rt, hPD, ?_, ?_, m, hlm, hmh, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; exact hdi
      · simp only [V.L1467, VD.L1467, VD.L1450]
        regs_simp
        exact q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)]) (by decide)
    · exact hl0
    · exact hl1
    · -- `A m ≤ A (m + 1)`: the next element
      rename_i c1 _ _ _ _ _
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at c1
      rw [cc_nc_sub] at c1
      simp only [decide_eq_false_iff_not] at c1
      rw [hcx, hdi, tcx, tm] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1450.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_,
          l, rt, hPD, ?_, ?_, m + 1, by omega, by omega, ?_⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; rw [hdi]; exact ea
      · simp only [V.L1450, VD.L1450]
        regs_simp
        refine q1_lex_last_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)]) ?_
        rw [hcx, hdi, ea, tcx, tm, tm1]
        omega
    · -- `A m > A (m + 1)`: to L1467
      refine ⟨T.L1467.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_,
          l, rt, hPD, ?_, ?_, m, hlm, hmh, ?_⟩, hmT.get⟩, ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; exact hdi
      · simp only [V.L1467, VD.L1467, VD.L1450]
        regs_simp
        exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)])
          (by decide))

set_option maxRecDepth 100000 in
theorem blk_L1467 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1467" ⟨"sbr_reset.L1467", B.L1467, some "sbr_reset.L1470"⟩ := by
  info_off
  measure_hb "L1467"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD,
        h9, h8, -⟩, hm⟩ := T.L1467.mp hs
    clear hs
    rw [V.L1467] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hphiS := phi_le hQS.1
    have hwI := ep_wB hRs (o := 0x4fe) hW.1 (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1467]
    vcgen
    all_goals subst s₀
    · -- the interval is sorted: drop it
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L12d0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, hax, hD, hR, hSR, hQS⟩, hmT.get⟩, Or.inl ?_⟩
      simp only [V.L12d0, VD.L12d0, VD.L1467]
      rw [stkPhi_mk _ _ _ _ rfl, hax, hdx, hcx, hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · refine ⟨T.L1470.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx,
          l, rt, hPD, h9, h8, trivial⟩, hmT.get⟩, ?_⟩
      simp only [V.L1470, VD.L1470, VD.L1467]
      exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) (by decide))

set_option hygiene false in
/-- `L1424`: the loaded `A l` and the exchange in memory. -/
local macro "q1_424_mem" : tactic => `(tactic| (
  simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
    Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
  rw [hl9, Option.some.injEq] at h1
  subst h1
  rw [sw16_zx, av_bytes fr 0x4fe l]))

set_option hygiene false in
/-- `L1424`: the exit facts and the measure. -/
local macro "q1_424_fin" : tactic => `(tactic| (
  all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax | exact hdx))
  all_goals try (regs_simp; (first | exact hcx | exact h9 | exact h8))
  all_goals simp only [V.L1470, V.L1442, VD.L1470, VD.L1442, VD.L1424]
  all_goals regs_simp
  all_goals refine q1_lex_phase_lt ?_ (by decide)
  all_goals rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega),
    hphi' _ _ _ (by regs_simp), hphi]))

set_option maxRecDepth 100000 in
theorem blk_L1424 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1424" ⟨"sbr_reset.L1424", B.L1424, some "sbr_reset.L1442"⟩ := by
  info_off
  measure_hb "L1424"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv,
        hPI, h9, h8, hlr, h11⟩, hm⟩ := T.L1424.mp hs
    clear hs
    rw [V.L1424] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hpv : QS.av fr 0x4fe (hi1 - 2) = pv := by
      rw [show hi1 - 2 = hi1 - 1 - 1 by omega]; exact p5
    have hPD : QS.PDone (fun _ => (0 : Int)) lo (hi1 - 1) l rt := by
      unfold QS.PDone; omega
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hl9 : s₀.dmem.loadInt (s₀.regs.get64 .r9) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (l + 1)) 2)) := by
      rw [h9]; exact av_load hm hF (by omega)
    have hld : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 x.toInt).loadInt
        (s₀.regs.get64 .rdi) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := sd_st hm hF (o := 0x4fe) (q := l) (by omega) (by omega) x
      rw [← h9] at hm1
      rw [hdi, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, h401, h301, hSR1, hav1⟩ := sd_st hm hF (o := 0x4fe)
      (q := l) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r11))
    rw [← h9] at hm1
    obtain ⟨hm2, hF2, h402, h302, hSR2, hav2⟩ := sd_st hm1 hF1 (o := 0x4fe)
      (q := hi1 - 2) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x4fe l))
    rw [← hdi] at hm2
    have hsw := av_swap hav1 hav2 (toInt_av (h11.trans (congrArg _ hpv.symm)))
      (toInt_ofInt_av _ _ _)
    have hQ' := qw_swap hQ (i := hi1 - 2) (j := l)
      (by unfold InIv; simp only; omega) (by unfold InIv; simp only; omega)
    rw [← hsw] at hQ'
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .r9) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r11)).toInt).storeInt (s₀.regs.get64 .rdi) 2
          (BitVec.ofInt 16 (QS.av fr 0x4fe l)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hx hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L1424]
    vcgen
    all_goals subst s₀
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · rw [hl9]; rfl
    · rw [hl9]; rfl
    · exact hld _
    · -- `r10d = 0`: to L1470
      rename_i v h1 _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1470.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0,
          lo, hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩, hmT2.get⟩,
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi = r9`: to L1442
      rename_i v h1 _ _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1442.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0,
          lo, hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩, hmT2.get⟩,
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi ≠ r9 - 2`: to L1470
      rename_i v h1 _ _ _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1470.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0,
          lo, hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩, hmT2.get⟩,
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi = r9 - 2`: to L1442
      rename_i v h1 _ _ _ _
      q1_424_mem
      refine ⟨T.L1442.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0,
          lo, hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩, hmT2.get⟩,
        Nat.le_of_lt ?_⟩
      q1_424_fin

end Kraken.Examples.Sbr.Reset

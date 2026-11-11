import Kraken.X64.Examples.Sbr.Parse.ResetQs4Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 4 (`vk1`): placing the pivot and the sortedness scan
(`L2794`, `L27b2`, `L27c0`, `L27d7`)
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
theorem blk_L27b2 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L27b2" ⟨"sbr_reset.L27b2", B.L27b2, some "sbr_reset.L27c0"⟩ := by
  info_off
  measure_hb "L27b2"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, -⟩ :=
      Q4.g_iff.mp (T.L27b2.mp hs)
    clear hs
    rw [V.L27b2] at hn
    subst hn
    have ⟨p1, p2, p3, p4⟩ := hPD
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L27b2]
    vcgen
    all_goals subst s₀
    refine ⟨T.L27c0.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF, hWf,
        hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_, ?_, lo,
        Nat.le_refl _, by omega, ?_⟩), ?_⟩
    · regs_simp; exact hrsp
    · regs_simp; exact hrbp
    · regs_simp; exact hax
    · regs_simp; exact hdx
    · regs_simp; exact hcx
    · regs_simp; exact h9
    · regs_simp; exact h8
    · regs_simp; exact hdx
    · simp only [V.L27c0, VD.L27c0, VD.L27b2]
      regs_simp
      exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)])
        (by decide))

set_option maxRecDepth 100000 in
theorem blk_L27c0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L27c0" ⟨"sbr_reset.L27c0", B.L27c0, some "sbr_reset.L27d7"⟩ := by
  info_off
  measure_hb "L27c0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, m, hlm, hmh, hdi⟩ :=
      Q4.g_iff.mp (T.L27c0.mp hs)
    clear hs
    rw [V.L27c0] at hn
    subst hn
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hrl := (t₀.regs.get64 .rsp).isLt
    have tcx := ep_m2_toNat hRs (o := 0x480) (q := hi1) (by omega)
    have tm := ep_toNat hRs (o := 0x480) (q := m) (by omega)
    have tm1 := ep_toNat hRs (o := 0x480) (q := m + 1) (by omega)
    have ea := q1_ep_add2 t₀ 0x480 m
    have hl0 : (s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2).isSome = true := by
      rw [hdi, av_load hm hF (by omega)]; rfl
    have hl1 : (s₀.dmem.loadInt (s₀.regs.get64 .rdi + 2#64) 2).isSome = true := by
      rw [hdi, ea, av_load hm hF (by omega)]; rfl
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L27c0]
    vcgen
    all_goals subst s₀
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq]
    · -- `m ≥ hi1 - 1`: to L27d7
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L27d7.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_,
          ?_, l, rt, hPD, ?_, ?_, m, hlm, hmh, ?_⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; exact hdi
      · simp only [V.L27d7, VD.L27d7, VD.L27c0]
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
      refine ⟨by decide, T.L27c0.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_,
          ?_, l, rt, hPD, ?_, ?_, m + 1, by omega, by omega, ?_⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; rw [hdi]; exact ea
      · simp only [V.L27c0, VD.L27c0]
        regs_simp
        refine q1_lex_last_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)]) ?_
        rw [hcx, hdi, ea, tcx, tm, tm1]
        omega
    · -- `A m > A (m + 1)`: to L27d7
      refine ⟨T.L27d7.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF,
          hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, l, rt, hPD, ?_,
          ?_, m, hlm, hmh, ?_⟩), ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact h9
      · regs_simp; exact h8
      · regs_simp; exact hdi
      · simp only [V.L27d7, VD.L27d7, VD.L27c0]
        regs_simp
        exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ (by regs_simp)])
          (by decide))

set_option maxRecDepth 100000 in
theorem blk_L27d7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L27d7" ⟨"sbr_reset.L27d7", B.L27d7, some "sbr_reset.L27e0"⟩ := by
  info_off
  measure_hb "L27d7"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9, h8, -⟩ :=
      Q4.g_iff.mp (T.L27d7.mp hs)
    clear hs
    rw [V.L27d7] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hphiS := Nat.le_trans (phi_le hQS.1) (Nat.mul_le_mul hS6 (Nat.le_refl _))
    have hphiS' : phi S ≤ 6 * 99 := Nat.le_trans hphiS (Nat.mul_le_mul_left _ (by omega))
    have hwI := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L27d7]
    vcgen
    all_goals subst s₀
    · -- the interval is sorted: drop it
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2640.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, hax, hD, hR, hSR, hQS⟩), Or.inl ?_⟩
      simp only [V.L2640, VD.L2640, VD.L27d7]
      rw [stkPhi_mk _ _ _ _ rfl, hax, hdx, hcx, hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · refine ⟨T.L27e0.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩, (by q4_rg hRg), hF,
        hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, l, rt, hPD, h9,
        h8, trivial⟩), ?_⟩
      simp only [V.L27e0, VD.L27e0, VD.L27d7]
      exact Nat.le_of_lt (q1_lex_phase_lt (by rw [stkPhi_mk _ _ _ _ rfl]) (by decide))

set_option hygiene false in
/-- `L2794`: the loaded `A l` and the exchange in memory. -/
local macro "q1_424_mem" : tactic => `(tactic| (
  simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
    Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1
  rw [hl9, Option.some.injEq] at h1
  subst h1
  rw [sw16_zx, av_bytes fr 0x480 l]))

set_option hygiene false in
/-- `L2794`: the exit facts and the measure. -/
local macro "q1_424_fin" : tactic => `(tactic| (
  all_goals try (regs_simp; (first | exact hrsp | exact hrbp | exact hax | exact hdx))
  all_goals try (regs_simp; (first | exact hcx | exact h9 | exact h8))
  all_goals simp only [V.L27e0, V.L27b2, VD.L27e0, VD.L27b2, VD.L2794]
  all_goals regs_simp
  all_goals refine q1_lex_phase_lt ?_ (by decide)
  all_goals rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := S.length) (by omega),
    hphi' _ _ _ (by regs_simp), hphi]))

set_option maxRecDepth 100000 in
theorem blk_L2794 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2794" ⟨"sbr_reset.L2794", B.L2794, some "sbr_reset.L27b2"⟩ := by
  info_off
  measure_hb "L2794"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, hdi, l, rt, pv, hPI, h9, h8, hlr, h11⟩ :=
      Q4.g_iff.mp (T.L2794.mp hs)
    clear hs
    rw [V.L2794] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have ⟨p1, p2, p3, p4, p5⟩ := hPI
    have hpv : QS.av fr 0x480 (hi1 - 2) = pv := by
      rw [show hi1 - 2 = hi1 - 1 - 1 by omega]; exact p5
    have hPD : QS.PDone (fun _ => (0 : Int)) lo (hi1 - 1) l rt := by
      unfold QS.PDone; omega
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hl9 : s₀.dmem.loadInt (s₀.regs.get64 .r9) 2
        = some (Int.ofBytes (slice fr (0x480 + 2 * (l + 1)) 2)) := by
      rw [h9]; exact av_load hm hF (by omega)
    have hld : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 x.toInt).loadInt
        (s₀.regs.get64 .rdi) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := Q4.sd_st hm hF hWf (o := 0x480) (q := l) (by omega) (by omega) x
      rw [← h9] at hm1
      rw [hdi, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q4.sd_st hm hF hWf (o := 0x480)
      (q := l) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r11))
    rw [← h9] at hm1
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q4.sd_st hm1 hF1 hWf1 (o := 0x480)
      (q := hi1 - 2) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x480 l))
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
          (BitVec.ofInt 16 (QS.av fr 0x480 l)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hX⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hX hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L2794]
    vcgen
    all_goals subst s₀
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.isSome_some, BitVec.setWidth_eq,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · rw [hl9]; rfl
    · rw [hl9]; rfl
    · exact hld _
    · -- `r10d = 0`: to L27e0
      rename_i v h1 _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L27e0.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩),
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi = r9`: to L27b2
      rename_i v h1 _ _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L27b2.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩),
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi ≠ r9 - 2`: to L27e0
      rename_i v h1 _ _ _ _
      q1_424_mem
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L27e0.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, l, rt, hPD, ?_, ?_, trivial⟩),
        Or.inl ?_⟩
      q1_424_fin
    · -- `rsi = r9 - 2`: to L27b2
      rename_i v h1 _ _ _ _
      q1_424_mem
      refine ⟨T.L27b2.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF2,
          hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, l, rt, hPD,
          ?_, ?_, trivial⟩),
        Nat.le_of_lt ?_⟩
      q1_424_fin

end Kraken.Examples.Sbr.Reset

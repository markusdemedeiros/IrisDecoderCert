import Kraken.X64.Examples.Sbr.Parse.ResetQsLib

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): the interval dispatch (`L1300`)
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
theorem blk_L1300 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1300" ⟨"sbr_reset.L1300", B.L1300, some "sbr_reset.L132d"⟩ := by
  info_off
  measure_hb "L1300"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, -⟩, hm⟩ :=
      T.L1300.mp hs
    clear hs
    rw [V.L1300] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hdx' : s₀.regs.get64 .rdx = QS.ep t₀ 0x4fe lo := hdx
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x4fe hi1 - 2#64 := hcx
    clear hdx hcx
    have tdx := ep_toNat hRs (o := 0x4fe) (q := lo) (by omega)
    have tcx := ep_m2_toNat hRs (o := 0x4fe) (q := hi1) (by omega)
    have tcx4 := ep_m4_toNat hRs (o := 0x4fe) (q := hi1) (by omega) (by omega)
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hphiS := phi_le hQS.1
    have hwI := ep_wB hRs (o := 0x4fe) hW.1 (by omega)
    have hwt : wt (lo, hi1) ≤ 27 := by unfold wt; simp only; omega
    have L1 := av_load hm hF (o := 0x4fe) (q := lo) (by omega)
    have L2 : 1 ≤ hi1 → s₀.dmem.loadInt (QS.ep t₀ 0x4fe hi1 - 2#64) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (hi1 - 1 + 1)) 2)) := fun h => by
      rw [ep_sub2 _ _ _ h]; exact av_load hm hF (by omega)
    have L3 : lo + 2 ≤ hi1 → s₀.dmem.loadInt (QS.ep t₀ 0x4fe lo
        + (QS.ep t₀ 0x4fe hi1 - 2#64 - QS.ep t₀ 0x4fe lo).sshiftRight 2 * 2#64) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (QS.mid lo (hi1 - 1) + 1)) 2)) := fun h => by
      rw [qs_mid_addr hRs h (by omega)]; exact av_load hm hF (by unfold QS.mid; omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1300]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, qs_sh2, Nat.reduceEqDiff] at *
    have hw1 : 1 ≤ wt (lo, hi1) := by unfold wt; simp only; omega
    · -- start ≥ end: drop the interval
      rename_i e c1; subst e
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx] at c1
      simp only [decide_eq_true_eq] at c1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L12d0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, hax, hD, hR, hSR, hQS⟩, hmT.get⟩, Or.inl ?_⟩
      simp only [V.L12d0, VD.L12d0]
      rw [stkPhi_mk s₀ _ _ _ rfl, hax, hdx', hcx', hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by omega) (by omega)
    · -- two elements
      rename_i e c1 c2; subst e
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx] at c1
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx4] at c2
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c1 c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L14f0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, by omega⟩,
        hmT.get⟩, Or.inr ⟨?_, by decide⟩⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx'
      · regs_simp; exact hcx'
      · simp only [V.L14f0, VD.L14f0]
        rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
        regs_simp
    · -- load `*start`
      rename_i e c1 b1 b2 b3 c2; subst e
      rw [hdx', L1]; rfl
    · -- load `*end`
      rename_i e c1 b1 b2 b3 v1 c2 l1; subst e
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx] at c1
      simp only [decide_eq_false_iff_not] at c1
      rw [hcx', L2 (by omega)]; rfl
    · -- load `*mid`
      rename_i e c1 b1 b2 b3 v1 v2 c2 l1 l2; subst e
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx] at c1
      simp only [decide_eq_false_iff_not] at c1
      rw [hdx', hcx', L3 (by omega)]; rfl
    · -- three or more: on to the median of three
      rename_i e c1 b1 b2 b3 v1 v2 v3 c2 l1 l2 l3; subst e
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx] at c1
      rw [cc_nc_sub _ _ _ _, hdx', hcx', tdx, tcx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      have h3 : lo + 3 ≤ hi1 := by omega
      rw [hdx', L1] at l1
      rw [hcx', L2 (by omega)] at l2
      rw [hdx', hcx', L3 (by omega)] at l3
      simp only [Option.some.injEq] at l1 l2 l3
      subst l1 l2 l3
      refine ⟨T.L132d.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_,
          ?_, ?_, ?_⟩, hmT.get⟩, ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx'
      · regs_simp; exact hcx'
      · regs_simp; rw [hcx']
        exact ep_eq_of_toNat hRs (by omega) (by rw [tcx4]; omega)
      · regs_simp; rw [hdx', hcx']
        exact qs_mid_addr hRs (by omega) (by omega)
      · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
      · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
      · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
      · simp only [V.L132d, VD.L132d]
        rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
        regs_simp; exact Nat.le_refl _

theorem blk_L12d8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L12d8" ⟨"sbr_reset.L12d8", B.L12d8, some "sbr_reset.L1300"⟩ := by
  info_off
  measure_hb "L12d8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, ⟨hN1, hN2, S, A0, hax, hD, hR, hSR, hQ⟩, hc0⟩, hm⟩ := T.L12d8.mp hs
    clear hs
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hS1 : S ≠ [] := by rintro rfl; exact hc0 (by rw [hax]; rfl)
    obtain ⟨S', I, rfl⟩ : ∃ S' I, S = S' ++ [I] :=
      ⟨S.dropLast, S.getLast hS1, (List.dropLast_concat_getLast hS1).symm⟩
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hS6 hax
    obtain ⟨hSR', r1, r2⟩ := stkRel_pop hSR
    obtain ⟨hD', hDc⟩ := depth_pop hD
    have hv1 := stk_load hm hF (o := 16 * S'.length) (by omega)
      (addr := s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550224#64)
      (by rw [hrbp]; exact stk_addr0 _ _)
    have hv2 := stk_load hm hF (o := 16 * S'.length + 8) (by omega)
      (addr := s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550232#64)
      (by rw [hrbp]; exact stk_addr1 _ _)
    have e1 : BitVec.ofInt 64 (Int.ofBytes (slice fr (16 * S'.length) 8)) = QS.ep t₀ 0x4fe I.1 := by
      rw [← r1]; simp only [frSlot64, rb]; congr 4; omega
    have e2 : BitVec.ofInt 64 (Int.ofBytes (slice fr (16 * S'.length + 8) 8))
        = QS.ep t₀ 0x4fe I.2 - 2#64 := by
      rw [← r2]; simp only [frSlot64, rb]; congr 4; omega
    have hph : QS.stkPhi s₀ (S'.length + 1) = QS.stkPhi s₀ S'.length
        + wBn 2 (QS.ep t₀ 0x4fe I.1).toNat (QS.ep t₀ 0x4fe I.2 - 2#64).toNat := by
      rw [stkPhi_succ, slot64_fr hm hF hrbp (by omega) (by omega),
        slot64_fr hm hF hrbp (by omega) (by omega), r1, r2]
    have ed := qs_dec32 (S'.length + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at ed
    have es := qs_shl4 S'.length
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L12d8]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hax, ed,
      es, hv1, hv2, Option.isSome_some, Option.some.injEq]
    · rename_i c
      simp only [hax, Int64.toBitVec_ofNat_norm] at c
      rw [qs_nc32 _ _ (by omega) (by omega)] at c
      exfalso; simp at c; omega
    · rename_i c v1 hl1 v2 hl2
      simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
        Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hax, ed,
        es, hv1, hv2, Option.some.injEq] at hl1 hl2
      subst hl1 hl2
      refine ⟨T.L1300.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        ⟨h40, h30, ⟨hN1, hN2, S', A0, I.1, I.2, ?_, hD', hDc, hR, hSR', hQ, ?_, ?_, trivial⟩⟩,
        hm⟩, ?_⟩
      all_goals
        try (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrsp, hrbp, e1, e2]; done)
      simp only [lex_var, VD.L1300, VD.L12d8]
      refine lex_phase ?_ (by decide)
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]), hax,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), hph, e1, e2]

end Kraken.Examples.Sbr.Reset

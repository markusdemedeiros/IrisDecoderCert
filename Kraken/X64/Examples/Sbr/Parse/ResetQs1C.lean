import Kraken.X64.Examples.Sbr.Parse.ResetQs1Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 1 (`stop_dk`): the median of three (`L132d` .. `L13a0`)
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
theorem blk_L132d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L132d" ⟨"sbr_reset.L132d", B.L132d, some "sbr_reset.L1350"⟩ := by
  info_off
  measure_hb "L132d"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h9, h11, h8⟩, hm⟩ := T.L132d.mp hs
    clear hs
    rw [V.L132d] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x4fe (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hst := sd_st hm hF (o := 0x4fe) (q := hi1 - 1) (by omega) (by omega)
      (BitVec.setWidth 16 (s₀.regs.get64 .r9))
    obtain ⟨hm', hF', h40', h30', hSRi, hav⟩ := hst
    rw [← hcx'] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega)
    have h9i : (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt = QS.av fr 0x4fe lo := toInt_av h9
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2).isSome = true := by
      rw [hcx', av_load hm hF (by omega)]; rfl
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hx hm hm'
    simp only [B.L132d]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, Nat.reduceEqDiff]
    · -- `A lo ≤ A e`: to L1350
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1350.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi,
          hsi, h9, h11, h8⟩, hmT.get⟩, Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L1350, VD.L1350]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · -- `A mid < A e < A lo`: to L135c
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L135c.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi,
          hsi, h9, h8⟩, hmT.get⟩, Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L135c, VD.L135c]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1 c2; subst e; exact hld
    · -- `A e ≤ A mid`, `A e < A lo`: `A[e] := A lo`, to L1360
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1360.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF', ⟨h40'.trans h40, h30'.trans h30, hN1, hN2, S, QS.av fr 0x4fe, A0, lo, hi1,
          hi1 - 1, ?_, hD, hc, hR, (hSRi (by omega)).mpr hSR, hQ, fun r => ?_, ?_, ?_, h3, ?_, ?_,
          ?_, Or.inr rfl⟩, hmT'.get⟩, Or.inr ⟨?_, by decide⟩⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · exact (hav r).trans (by rw [h9i])
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact hsi
      · regs_simp; rw [sw16_zx64]; exact h11
      · simp only [V.L1360, VD.L1360]
        regs_simp
        rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]

theorem blk_L1350 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1350" ⟨"sbr_reset.L1350", B.L1350, some "sbr_reset.L135c"⟩ := by
  info_off
  measure_hb "L1350"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h9, h11, h8⟩, hm⟩ := T.L1350.mp hs
    clear hs
    rw [V.L1350] at hn
    subst hn
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1350]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L136f.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_,
          ?_, ?_, ?_⟩, hmT.get⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L136f, VD.L136f]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp
    · rename_i e c1; subst e
      refine ⟨T.L135c.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_,
          ?_, ?_, ?_⟩, hmT.get⟩, ?_⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L135c, VD.L135c]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp; exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L135c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L135c" ⟨"sbr_reset.L135c", B.L135c, some "sbr_reset.L1360"⟩ := by
  info_off
  measure_hb "L135c"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h9, h8⟩, hm⟩ := T.L135c.mp hs
    clear hs
    rw [V.L135c] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hst := sd_st hm hF (o := 0x4fe) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
      (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r9))
    obtain ⟨hm', hF', h40', h30', hSRi, hav⟩ := hst
    rw [← hsi] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt⟩ : MachineData) S.length
        = QS.stkPhi s₀ S.length := fun R z sf e2 => by
      rw [stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega),
        stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)]
    have h9i : (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt = QS.av fr 0x4fe lo := toInt_av h9
    have hA : Box _ := ⟨hx⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hx hm'
    simp only [B.L135c]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rename_i e; subst e; rw [hsi, av_load hm hF (by omega)]; rfl
    rename_i e; subst e
    refine ⟨T.L1360.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, _, hA.get, hsp,
      hfm, hF', ⟨h40'.trans h40, h30'.trans h30, hN1, hN2, S, QS.av fr 0x4fe, A0, lo, hi1,
        QS.mid lo (hi1 - 1), hax, hD, hc, hR, (hSRi (by omega)).mpr hSR, hQ,
        fun r => (hav r).trans (by rw [h9i]), hdx, hcx, h3, hdi, hsi, h8, Or.inl rfl⟩,
        hmT'.get⟩, ?_⟩
    simp only [V.L1360, VD.L1360]
    rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ rfl]
    exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L1360 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1360" ⟨"sbr_reset.L1360", B.L1360, some "sbr_reset.L136f"⟩ := by
  info_off
  measure_hb "L1360"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A, A0, lo, hi1, pos, hax, hD, hc, hR, hSR, hQ, hAv, hdx, hcx, h3,
        hdi, hsi, h8, hpos⟩, hm⟩ := T.L1360.mp hs
    clear hs
    rw [V.L1360] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x4fe (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hst := sd_st hm hF (o := 0x4fe) (q := lo) (by omega) (by omega)
      (BitVec.setWidth 16 (s₀.regs.get64 .r8))
    obtain ⟨hm', hF', h40', h30', hSRi, -⟩ := hst
    rw [← hdx] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt⟩ : MachineData) S.length
        = QS.stkPhi s₀ S.length := fun R z sf e2 => by
      rw [stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega),
        stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)]
    have L1 := av_load hm' hF' (o := 0x4fe) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
    have L2 := av_load hm' hF' (o := 0x4fe) (q := hi1 - 1) (by omega)
    rw [← hsi] at L1
    rw [← hcx'] at L2
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2).isSome = true := by
      rw [hdx, av_load hm hF (by omega)]; rfl
    have hQ' : QW 13 (QS.av (wr fr (0x4fe + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt)) 0x4fe)
        (QS.av (wr fr (0x4fe + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt)) 0x4fe) (S ++ [(lo, hi1)]) :=
      ⟨hQ.1, perm_refl _⟩
    have hA : Box _ := ⟨hx⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hx hm hm' hQ hAv
    simp only [B.L1360]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.isSome_some]
    · rename_i e; subst e; exact hld
    · rename_i e; subst e; rw [L1]; rfl
    · rename_i e v1 l1; subst e; rw [L2]; rfl
    rename_i e v1 l1 v2 l2 f; subst e
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at l1 l2
    rw [L1, Option.some.injEq] at l1
    rw [L2, Option.some.injEq] at l2
    subst l1 l2
    refine ⟨T.L136f.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
      hfm, hF', ⟨h40'.trans h40, h30'.trans h30, hN1, hN2, S, _, lo, hi1, ?_, hD, hc, hR,
        (hSRi (by omega)).mpr hSR, hQ', ?_, ?_, h3, ?_, ?_, ?_, ?_⟩, hmT'.get⟩, ?_⟩
    all_goals try (regs_simp; assumption)
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · simp only [V.L136f, VD.L136f]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp)]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L1390 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1390" ⟨"sbr_reset.L1390", B.L1390, some "sbr_reset.L13a0"⟩ := by
  info_off
  measure_hb "L1390"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h8⟩, hm⟩ := T.L1390.mp hs
    clear hs
    rw [V.L1390] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have e3 := ep_m6 hRs (o := 0x4fe) (q := hi1) (by omega) (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hphiS := phi_le hQS.1
    have hwI := ep_wB hRs (o := 0x4fe) hW.1 (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L1390]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some]
    all_goals rename_i e c; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
      BitVec.ofNat_eq_ofNat] at c ⊢
    all_goals rw [cc_z_sub, hdx, hcx, e3] at c
    all_goals simp only [q1_ep_inj hRs (show 0x4fe + 2 * (lo + 1) ≤ 0x548 by omega)
      (show 0x4fe + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega)] at c
    · -- three elements, sorted: drop
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L12d0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, ?_, hD, hR, hSR, hQS⟩, hmT.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L12d0, VD.L12d0]
      regs_simp
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp), hax, hdx, hcx, hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · simp only [decide_eq_false_iff_not] at c
      refine ⟨T.L13a0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_,
          by omega, ?_, ?_⟩, hmT.get⟩, ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact hsi
      · regs_simp; rw [sw16_zx64]; exact h8
      · regs_simp; rw [hcx]; exact e3
      · simp only [V.L13a0, VD.L13a0]
        regs_simp
        rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
        exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L136f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L136f" ⟨"sbr_reset.L136f", B.L136f, some "sbr_reset.L1390"⟩ := by
  info_off
  measure_hb "L136f"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h8, h11⟩, hm⟩ := T.L136f.mp hs
    clear hs
    rw [V.L136f] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have e3 := ep_m6 hRs (o := 0x4fe) (q := hi1) (by omega) (by omega)
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x4fe (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hphiS := phi_le hQS.1
    have hwI := ep_wB hRs (o := 0x4fe) hW.1 (by omega)
    have hmid : QS.mid lo (hi1 - 1) < hi1 - 1 := by unfold QS.mid; omega
    obtain ⟨hm1, hF1, h401, h301, hSR1, hav1⟩ := sd_st hm hF (o := 0x4fe) (q := hi1 - 1)
      (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r8))
    rw [← hcx'] at hm1
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2).isSome = true := by
      rw [hcx', av_load hm hF (by omega)]; rfl
    have hld2 : ((s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
        (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt).loadInt (s₀.regs.get64 .rsi) 2).isSome
        = true := by
      rw [hsi, av_load hm1 hF1 (by unfold QS.mid; omega)]; rfl
    obtain ⟨hm2, hF2, h402, h302, hSR2, hav2⟩ := sd_st hm1 hF1 (o := 0x4fe)
      (q := QS.mid lo (hi1 - 1)) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r11))
    rw [← hsi] at hm2
    have hsw := av_swap hav1 hav2 (toInt_av h8) (toInt_av h11)
    have hQ' := qw_swap hQ (i := QS.mid lo (hi1 - 1)) (j := hi1 - 1)
      (by unfold InIv QS.mid; simp only; omega) (by unfold InIv; simp only; omega)
    rw [← hsw] at hQ'
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt).storeInt (s₀.regs.get64 .rsi) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r11)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hx hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L136f]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · -- `A mid ≤ A e`: to L1390
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1390.mpr ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hA.get, hsp,
        hfm, hF, ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi,
          hsi, h8⟩, hmT.get⟩, Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L1390, VD.L1390]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1; subst e; exact hld1
    · rename_i e c1; subst e; exact hld2
    all_goals rename_i e c1 f c2; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at c2
    · -- not three elements: to L13a0
      rw [cc_nz_sub, hdx, hcx, show (-4 : Int64).toBitVec = 18446744073709551612#64 from rfl,
        e3] at c2
      simp only [q1_ep_inj hRs (show 0x4fe + 2 * (lo + 1) ≤ 0x548 by omega)
        (show 0x4fe + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega), Bool.not_eq_true',
        decide_eq_false_iff_not] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L13a0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0, lo,
          hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, h3, ?_, ?_, by omega, ?_, ?_⟩, hmT2.get⟩,
        Or.inr ⟨?_, by decide⟩⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact hsi
      · regs_simp; refine h11.trans (congrArg (BitVec.ofInt 16) ?_)
        exact ((congrFun hsw _).trans
          (by rw [swap_eq, ite_eq_left_of_eq_true _ _ (eq_self _)])).symm
      · regs_simp; rw [hcx]; exact e3
      · simp only [V.L13a0, VD.L13a0]
        regs_simp
        rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]
    · -- three elements, now sorted: drop
      rw [cc_nz_sub, hdx, hcx, show (-4 : Int64).toBitVec = 18446744073709551612#64 from rfl,
        e3] at c2
      simp only [q1_ep_inj hRs (show 0x4fe + 2 * (lo + 1) ≤ 0x548 by omega)
        (show 0x4fe + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega), Bool.not_eq_false',
        decide_eq_true_eq] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L12d0.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0, ?_,
          hD, hR, hSR', qw_drop hQ'⟩, hmT2.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L12d0, VD.L12d0]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
        hdx, hcx, hwI, hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)

set_option maxRecDepth 100000 in
theorem blk_L13a0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L13a0" ⟨"sbr_reset.L13a0", B.L13a0, some "sbr_reset.L13c0"⟩ := by
  info_off
  measure_hb "L13a0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, hr, hsp1, hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨h40, h30, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi,
        h4, h11, h8⟩, hm⟩ := T.L13a0.mp hs
    clear hs
    rw [V.L13a0] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
      have := rsp_ok hC; unfold resetStkMin at this; omega
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x4fe) (N := 13) (by omega) hSR hQS.1 (by omega)
    have hmid : QS.mid lo (hi1 - 1) + 1 ≤ hi1 - 2 := by unfold QS.mid; omega
    have hmid0 : lo ≤ QS.mid lo (hi1 - 1) := by unfold QS.mid; omega
    have hl0 : s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2
        = some (Int.ofBytes (slice fr (0x4fe + 2 * (hi1 - 2 + 1)) 2)) := by
      rw [hdi]; exact av_load hm hF (by omega)
    have hld3 : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2 x.toInt).loadInt
        (s₀.regs.get64 .rdi) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := sd_st hm hF (o := 0x4fe) (q := QS.mid lo (hi1 - 1)) (by omega)
        (by omega) x
      rw [hsi, hdi, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, h401, h301, hSR1, hav1⟩ := sd_st hm hF (o := 0x4fe)
      (q := QS.mid lo (hi1 - 1)) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x4fe (hi1 - 2)))
    rw [← hsi] at hm1
    obtain ⟨hm2, hF2, h402, h302, hSR2, hav2⟩ := sd_st hm1 hF1 (o := 0x4fe)
      (q := hi1 - 2) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r11))
    rw [← hdi] at hm2
    have hsw := av_swap hav1 hav2 (toInt_ofInt_av _ _ _) (toInt_av h11)
    have hQ' := qw_swap hQ (i := hi1 - 2) (j := QS.mid lo (hi1 - 1))
      (by unfold InIv; simp only; omega) (by unfold InIv QS.mid; simp only; omega)
    rw [← hsw] at hQ'
    have hPI : QS.PInv (swap (QS.av fr 0x4fe) (hi1 - 2) (QS.mid lo (hi1 - 1))) lo (hi1 - 1)
        (lo + 1) (hi1 - 3) (swap (QS.av fr 0x4fe) (hi1 - 2) (QS.mid lo (hi1 - 1)) (hi1 - 2)) := by
      unfold QS.PInv
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rw [show hi1 - 1 - 1 = hi1 - 2 by omega]
    rw [← hsw] at hPI
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2
          (BitVec.ofInt 16 (QS.av fr 0x4fe (hi1 - 2))).toInt).storeInt (s₀.regs.get64 .rdi) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r11)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x4fe) (N := 13) (by omega) hSR' hQS.1
        (by omega)
    have hmT2 : Box _ := ⟨hm2⟩
    clear hm1 hm2 hav1 hav2 hSR1 hSR2
    have hA : Box _ := ⟨hx⟩
    have hmT : Box _ := ⟨hm⟩
    clear hx hm
    simp only [B.L13a0]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · rename_i e; subst e; rw [hl0]; rfl
    · rename_i e v l; subst e; rw [hsi, av_load hmT.get hF (by omega)]; rfl
    · rename_i e v l; subst e; exact hld3 _
    all_goals rename_i e v l c; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at l
    all_goals rw [hl0, Option.some.injEq] at l
    all_goals subst l
    all_goals rw [sw16_zx, av_bytes fr 0x4fe (hi1 - 2)]
    · -- `lo + 1 ≤ hi1 - 3`: the partition loop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L13d9.mpr ⟨row, hr, hsp1, hC, hBO, ⟨?_, ?_⟩, st, _, hA.get, hsp,
        hfm, hF2, ⟨h402.trans (h401.trans h40), h302.trans (h301.trans h30), hN1, hN2, S, A0, lo,
          hi1, ?_, hD, hc, hR, hSR', hQ', ?_, ?_, ?_, lo + 1, hi1 - 3, _, hPI, ?_, ?_,
          by omega⟩, hmT2.get⟩, Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; rw [hdx]; exact q1_ep_add2 _ _ _
      · regs_simp; exact h8
      · simp only [V.L13d9, VD.L13d9]
        regs_simp
        refine q1_lex_phase_lt ?_ ?_
        · rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
            hphi]
        · rw [h8, hdx, q1_ep_add2, ep_toNat hRs (o := 0x4fe) (q := hi1 - 3) (by omega),
            ep_toNat hRs (o := 0x4fe) (q := lo + 1) (by omega)]
          omega
    · -- `hi1 - 3 < lo + 1`: impossible
      exfalso
      rw [cc_be_sub] at c
      simp only [decide_eq_false_iff_not, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at c
      rw [h8, hdx, q1_ep_add2, ep_toNat hRs (o := 0x4fe) (q := hi1 - 3) (by omega),
        ep_toNat hRs (o := 0x4fe) (q := lo + 1) (by omega)] at c
      omega

end Kraken.Examples.Sbr.Reset

import Kraken.X64.Examples.Sbr.Parse.ResetQs3Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 3 (`vk1`): the median of three (`L23ed` .. `L2460`)
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
theorem blk_L23ed (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L23ed" ⟨"sbr_reset.L23ed", B.L23ed, some "sbr_reset.L2410"⟩ := by
  info_off
  measure_hb "L23ed"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩ :=
      Q3.g_iff.mp (T.L23ed.mp hs)
    clear hs
    rw [V.L23ed] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hst := Q3.sd_st hm hF hWf (o := 0x480) (q := hi1 - 1) (by omega) (by omega)
      (BitVec.setWidth 16 (s₀.regs.get64 .r9))
    obtain ⟨hm', hF', hWf', hSRi, hav⟩ := hst
    rw [← hcx'] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega)
    have h9i : (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt = QS.av fr 0x480 lo := toInt_av h9
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2).isSome = true := by
      rw [hcx', av_load hm hF (by omega)]; rfl
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hX hm hm'
    simp only [B.L23ed]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, Nat.reduceEqDiff]
    · -- `A lo ≤ A e`: to L2410
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2410.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q3_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L2410, VD.L2410]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · -- `A mid < A e < A lo`: to L241c
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L241c.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q3_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h9, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L241c, VD.L241c]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1 c2; subst e; exact hld
    · -- `A e ≤ A mid`, `A e < A lo`: `A[e] := A lo`, to L2420
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2420.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF', hWf', hmT'.get, hN1, hN2, S, QS.av fr 0x480, A0, lo, hi1, hi1 - 1,
          ?_, hD, hc, hR, (hSRi (by omega)).mpr hSR, hQ, fun r => ?_, ?_, ?_, h3, ?_, ?_, ?_,
          Or.inr rfl⟩), Or.inr ⟨?_, by decide⟩⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · exact (hav r).trans (by rw [h9i])
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact hsi
      · regs_simp; rw [sw16_zx64]; exact h11
      · simp only [V.L2420, VD.L2420]
        regs_simp
        rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]

set_option maxRecDepth 100000 in
theorem blk_L2410 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2410" ⟨"sbr_reset.L2410", B.L2410, some "sbr_reset.L241c"⟩ := by
  info_off
  measure_hb "L2410"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩ :=
      Q3.g_iff.mp (T.L2410.mp hs)
    clear hs
    rw [V.L2410] at hn
    subst hn
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L2410]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L242f.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_,
          ?_, h3, ?_, ?_, ?_, ?_⟩), Or.inr ⟨?_, by decide⟩⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L242f, VD.L242f]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp
    · rename_i e c1; subst e
      refine ⟨T.L241c.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q3_rg hRg), hF,
          hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_, ?_,
          ?_⟩), ?_⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L241c, VD.L241c]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp; exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L241c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L241c" ⟨"sbr_reset.L241c", B.L241c, some "sbr_reset.L2420"⟩ := by
  info_off
  measure_hb "L241c"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h8⟩ :=
      Q3.g_iff.mp (T.L241c.mp hs)
    clear hs
    rw [V.L241c] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hst := Q3.sd_st hm hF hWf (o := 0x480) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
      (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r9))
    obtain ⟨hm', hF', hWf', hSRi, hav⟩ := hst
    rw [← hsi] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt⟩ : MachineData) S.length
        = QS.stkPhi s₀ S.length := fun R z sf e2 => by
      rw [stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega),
        stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR
            hQS.1 (by omega)]
    have h9i : (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt = QS.av fr 0x480 lo := toInt_av h9
    have hA : Box _ := ⟨hX⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hX hm'
    simp only [B.L241c]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rename_i e; subst e; rw [hsi, av_load hm hF (by omega)]; rfl
    rename_i e; subst e
    refine ⟨T.L2420.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨hrsp, hrbp⟩, (by q3_rg hRg), hF',
        hWf', hmT'.get, hN1, hN2, S, QS.av fr 0x480, A0, lo, hi1, QS.mid lo (hi1 - 1), hax, hD, hc,
        hR, (hSRi (by omega)).mpr hSR, hQ, fun r => (hav r).trans (by rw [h9i]), hdx, hcx, h3, hdi,
        hsi, h8, Or.inl rfl⟩), ?_⟩
    simp only [V.L2420, VD.L2420]
    rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ rfl]
    exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L2420 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2420" ⟨"sbr_reset.L2420", B.L2420, some "sbr_reset.L242f"⟩ := by
  info_off
  measure_hb "L2420"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A, A0, lo, hi1, pos,
      hax, hD, hc, hR, hSR, hQ, hAv, hdx, hcx, h3, hdi, hsi, h8, hpos⟩ :=
      Q3.g_iff.mp (T.L2420.mp hs)
    clear hs
    rw [V.L2420] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hst := Q3.sd_st hm hF hWf (o := 0x480) (q := lo) (by omega) (by omega)
      (BitVec.setWidth 16 (s₀.regs.get64 .r8))
    obtain ⟨hm', hF', hWf', hSRi, hav⟩ := hst
    rw [← hdx] at hm'
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt⟩ : MachineData) S.length
        = QS.stkPhi s₀ S.length := fun R z sf e2 => by
      rw [stkPhi_eq hm' hF' (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega)
        ((hSRi (by omega)).mpr hSR) hQS.1 (by omega),
        stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR
            hQS.1 (by omega)]
    have L1 := av_load hm' hF' (o := 0x480) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
    have L2 := av_load hm' hF' (o := 0x480) (q := hi1 - 1) (by omega)
    rw [← hsi] at L1
    rw [← hcx'] at L2
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2).isSome = true := by
      rw [hdx, av_load hm hF (by omega)]; rfl
    have hp : lo ≤ pos ∧ pos < hi1 := by
      rcases hpos with h | h <;> subst h <;> (try unfold QS.mid) <;> omega
    have h8i : (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt = A pos := by
      have := Q3.cur_range hR hQ.2 (q := pos) (by omega)
      rw [h8]; exact Q3.toInt_ofInt16 (by omega) (by omega)
    have hQ' : QW (A2.n1N e a (k0N a row) k2) (QS.av (wr fr (0x480 + 2 * (lo + 1))
        (Int.toBytes 2 (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt)) 0x480) A0
        (S ++ [(lo, hi1)]) := by
      have hs := qw_swap hQ (i := lo) (j := pos) (by unfold InIv; simp only; omega)
        (by unfold InIv; simp only; omega)
      refine ⟨hs.1, hs.2.congr fun r => ?_⟩
      rw [hav r, show QS.av fr 0x480 = upd A pos (A lo) from funext hAv, h8i, upd_upd_swap]
    have hA : Box _ := ⟨hX⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hX hm hm' hQ hAv
    simp only [B.L2420]
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
    refine ⟨T.L242f.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩, (by q3_rg hRg), hF', hWf',
        hmT'.get, hN1, hN2, S, _, lo, hi1, ?_, hD, hc, hR, (hSRi (by omega)).mpr hSR, hQ', ?_, ?_,
        h3, ?_, ?_, ?_, ?_⟩), ?_⟩
    all_goals try (regs_simp; assumption)
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · simp only [V.L242f, VD.L242f]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp)]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L2450 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2450" ⟨"sbr_reset.L2450", B.L2450, some "sbr_reset.L2460"⟩ := by
  info_off
  measure_hb "L2450"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h8⟩ :=
      Q3.g_iff.mp (T.L2450.mp hs)
    clear hs
    rw [V.L2450] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have e3 := ep_m6 hRs (o := 0x480) (q := hi1) (by omega) (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hphiS := Nat.le_trans (phi_le hQS.1) (Nat.mul_le_mul hS6 (Nat.le_refl _))
    have hphiS' : phi S ≤ 6 * 99 := Nat.le_trans hphiS (Nat.mul_le_mul_left _ (by omega))
    have hwI := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L2450]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some]
    all_goals rename_i e c; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
      BitVec.ofNat_eq_ofNat] at c ⊢
    all_goals rw [cc_z_sub, hdx, hcx, e3] at c
    all_goals simp only [q1_ep_inj hRs (show 0x480 + 2 * (lo + 1) ≤ 0x548 by omega)
      (show 0x480 + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega)] at c
    · -- three elements, sorted: drop
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2390.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, ?_, hD, hR, hSR, hQS⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L2390, VD.L2390]
      regs_simp
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp), hax, hdx, hcx, hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · simp only [decide_eq_false_iff_not] at c
      refine ⟨T.L2460.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q3_rg hRg), hF,
          hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_,
          by omega, ?_, ?_⟩), ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; exact hsi
      · regs_simp; rw [sw16_zx64]; exact h8
      · regs_simp; rw [hcx]; exact e3
      · simp only [V.L2460, VD.L2460]
        regs_simp
        rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
        exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L242f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L242f" ⟨"sbr_reset.L242f", B.L242f, some "sbr_reset.L2450"⟩ := by
  info_off
  measure_hb "L242f"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h8, h11⟩ :=
      Q3.g_iff.mp (T.L242f.mp hs)
    clear hs
    rw [V.L242f] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have e3 := ep_m6 hRs (o := 0x480) (q := hi1) (by omega) (by omega)
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hphiS := Nat.le_trans (phi_le hQS.1) (Nat.mul_le_mul hS6 (Nat.le_refl _))
    have hphiS' : phi S ≤ 6 * 99 := Nat.le_trans hphiS (Nat.mul_le_mul_left _ (by omega))
    have hwI := ep_wB hRs (o := 0x480) hW.1 (by omega)
    have hmid : QS.mid lo (hi1 - 1) < hi1 - 1 := by unfold QS.mid; omega
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q3.sd_st hm hF hWf (o := 0x480) (q := hi1 - 1)
      (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r8))
    rw [← hcx'] at hm1
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2).isSome = true := by
      rw [hcx', av_load hm hF (by omega)]; rfl
    have hld2 : ((s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
        (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt).loadInt (s₀.regs.get64 .rsi) 2).isSome
        = true := by
      rw [hsi, av_load hm1 hF1 (by unfold QS.mid; omega)]; rfl
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q3.sd_st hm1 hF1 hWf1 (o := 0x480)
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
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega) hSR' hQS.1
        (by omega)
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    have hmT2 : Box _ := ⟨hm2⟩
    clear hX hm hm1 hm2 hav1 hav2 hSR1 hSR2
    simp only [B.L242f]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · -- `A mid ≤ A e`: to L2450
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2450.mpr (Q3.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q3_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L2450, VD.L2450]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1; subst e; exact hld1
    · rename_i e c1; subst e; exact hld2
    all_goals rename_i e c1 f c2; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at c2
    · -- not three elements: to L2460
      rw [cc_nz_sub, hdx, hcx, show (-4 : Int64).toBitVec = 18446744073709551612#64 from rfl,
        e3] at c2
      simp only [q1_ep_inj hRs (show 0x480 + 2 * (lo + 1) ≤ 0x548 by omega)
        (show 0x480 + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega), Bool.not_eq_true',
        decide_eq_false_iff_not] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2460.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, h3, ?_, ?_, by omega, ?_, ?_⟩),
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
      · simp only [V.L2460, VD.L2460]
        regs_simp
        rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]
    · -- three elements, now sorted: drop
      rw [cc_nz_sub, hdx, hcx, show (-4 : Int64).toBitVec = 18446744073709551612#64 from rfl,
        e3] at c2
      simp only [q1_ep_inj hRs (show 0x480 + 2 * (lo + 1) ≤ 0x548 by omega)
        (show 0x480 + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega), Bool.not_eq_false',
        decide_eq_true_eq] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2390.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, ?_, hD, hR, hSR', qw_drop hQ'⟩),
              Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L2390, VD.L2390]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
        hdx, hcx, hwI, hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)

set_option maxRecDepth 100000 in
theorem blk_L2460 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2460" ⟨"sbr_reset.L2460", B.L2460, some "sbr_reset.L2480"⟩ := by
  info_off
  measure_hb "L2460"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h4, h11, h8⟩ :=
      Q3.g_iff.mp (T.L2460.mp hs)
    clear hs
    rw [V.L2460] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hphi : QS.stkPhi s₀ S.length = phi S :=
      stkPhi_eq hm hF hrbp hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2) (by omega) hSR hQS.1
          (by omega)
    have hmid : QS.mid lo (hi1 - 1) + 1 ≤ hi1 - 2 := by unfold QS.mid; omega
    have hmid0 : lo ≤ QS.mid lo (hi1 - 1) := by unfold QS.mid; omega
    have hl0 : s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2
        = some (Int.ofBytes (slice fr (0x480 + 2 * (hi1 - 2 + 1)) 2)) := by
      rw [hdi]; exact av_load hm hF (by omega)
    have hld3 : ∀ x : BitVec 16, ((s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2 x.toInt).loadInt
        (s₀.regs.get64 .rdi) 2).isSome = true := fun x => by
      obtain ⟨hm1, hF1, -⟩ := Q3.sd_st hm hF hWf (o := 0x480) (q := QS.mid lo (hi1 - 1)) (by omega)
        (by omega) x
      rw [hsi, hdi, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q3.sd_st hm hF hWf (o := 0x480)
      (q := QS.mid lo (hi1 - 1)) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x480 (hi1 - 2)))
    rw [← hsi] at hm1
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q3.sd_st hm1 hF1 hWf1 (o := 0x480)
      (q := hi1 - 2) (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r11))
    rw [← hdi] at hm2
    have hsw := av_swap hav1 hav2 (toInt_ofInt_av _ _ _) (toInt_av h11)
    have hQ' := qw_swap hQ (i := hi1 - 2) (j := QS.mid lo (hi1 - 1))
      (by unfold InIv; simp only; omega) (by unfold InIv QS.mid; simp only; omega)
    rw [← hsw] at hQ'
    have hPI : QS.PInv (swap (QS.av fr 0x480) (hi1 - 2) (QS.mid lo (hi1 - 1))) lo (hi1 - 1)
        (lo + 1) (hi1 - 3) (swap (QS.av fr 0x480) (hi1 - 2) (QS.mid lo (hi1 - 1)) (hi1 - 2)) := by
      unfold QS.PInv
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rw [show hi1 - 1 - 1 = hi1 - 2 by omega]
    rw [← hsw] at hPI
    have hSR' := (hSR2 (by omega)).mpr ((hSR1 (by omega)).mpr hSR)
    have hphi' : ∀ R z sf, R.get64 .rbp = s₀.regs.get64 .rbp →
        QS.stkPhi (⟨R, z, sf, (s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2
          (BitVec.ofInt 16 (QS.av fr 0x480 (hi1 - 2))).toInt).storeInt (s₀.regs.get64 .rdi) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r11)).toInt⟩ : MachineData) S.length
        = phi S := fun R z sf e2 =>
      stkPhi_eq hm2 hF2 (e2.trans hrbp) hRs (o := 0x480) (N := A2.n1N e a (k0N a row) k2)
          (by omega) hSR' hQS.1
        (by omega)
    have hmT2 : Box _ := ⟨hm2⟩
    clear hm1 hm2 hav1 hav2 hSR1 hSR2
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L2460]
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
    all_goals rw [sw16_zx, av_bytes fr 0x480 (hi1 - 2)]
    · -- `lo + 1 ≤ hi1 - 3`: the partition loop
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2499.mpr (Q3.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q3_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, ?_, lo + 1, hi1 - 3, _, hPI, ?_, ?_, by omega⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; rw [hdx]; exact q1_ep_add2 _ _ _
      · regs_simp; exact h8
      · simp only [V.L2499, VD.L2499]
        regs_simp
        refine q1_lex_phase_lt ?_ ?_
        · rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
            hphi]
        · rw [h8, hdx, q1_ep_add2, ep_toNat hRs (o := 0x480) (q := hi1 - 3) (by omega),
            ep_toNat hRs (o := 0x480) (q := lo + 1) (by omega)]
          omega
    · -- `hi1 - 3 < lo + 1`: impossible
      exfalso
      rw [cc_be_sub] at c
      simp only [decide_eq_false_iff_not, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at c
      rw [h8, hdx, q1_ep_add2, ep_toNat hRs (o := 0x480) (q := hi1 - 3) (by omega),
        ep_toNat hRs (o := 0x480) (q := lo + 1) (by omega)] at c
      omega

end Kraken.Examples.Sbr.Reset

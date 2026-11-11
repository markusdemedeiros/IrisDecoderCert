import Kraken.X64.Examples.Sbr.Parse.ResetQs4Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 4 (`vk1`): the median of three (`L269d` .. `L2710`)
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
theorem blk_L269d (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L269d" ⟨"sbr_reset.L269d", B.L269d, some "sbr_reset.L26c0"⟩ := by
  info_off
  measure_hb "L269d"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩ :=
      Q4.g_iff.mp (T.L269d.mp hs)
    clear hs
    rw [V.L269d] at hn
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
    have hst := Q4.sd_st hm hF hWf (o := 0x480) (q := hi1 - 1) (by omega) (by omega)
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
    simp only [B.L269d]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, Nat.reduceEqDiff]
    · -- `A lo ≤ A e`: to L26c0
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L26c0.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L26c0, VD.L26c0]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · -- `A mid < A e < A lo`: to L26cc
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L26cc.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h9, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L26cc, VD.L26cc]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1 c2; subst e; exact hld
    · -- `A e ≤ A mid`, `A e < A lo`: `A[e] := A lo`, to L26d0
      rename_i e c1 c2; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L26d0.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF', hWf', hmT'.get, hN1, hN2, S, QS.av fr 0x480, A0, lo, hi1, hi1 - 1,
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
      · simp only [V.L26d0, VD.L26d0]
        regs_simp
        rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
          hphi]

set_option maxRecDepth 100000 in
theorem blk_L26c0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L26c0" ⟨"sbr_reset.L26c0", B.L26c0, some "sbr_reset.L26cc"⟩ := by
  info_off
  measure_hb "L26c0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h11, h8⟩ :=
      Q4.g_iff.mp (T.L26c0.mp hs)
    clear hs
    rw [V.L26c0] at hn
    subst hn
    have hA : Box _ := ⟨hX⟩
    have hmT : Box _ := ⟨hm⟩
    clear hX hm
    simp only [B.L26c0]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L26df.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_,
          ?_, h3, ?_, ?_, ?_, ?_⟩), Or.inr ⟨?_, by decide⟩⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L26df, VD.L26df]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp
    · rename_i e c1; subst e
      refine ⟨T.L26cc.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF,
          hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR, hQ, ?_, ?_, h3, ?_, ?_, ?_,
          ?_⟩), ?_⟩
      all_goals try (regs_simp; assumption)
      simp only [V.L26cc, VD.L26cc]
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
      regs_simp; exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L26cc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L26cc" ⟨"sbr_reset.L26cc", B.L26cc, some "sbr_reset.L26d0"⟩ := by
  info_off
  measure_hb "L26cc"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h9, h8⟩ :=
      Q4.g_iff.mp (T.L26cc.mp hs)
    clear hs
    rw [V.L26cc] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hst := Q4.sd_st hm hF hWf (o := 0x480) (q := QS.mid lo (hi1 - 1)) (by unfold QS.mid; omega)
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
    simp only [B.L26cc]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rename_i e; subst e; rw [hsi, av_load hm hF (by omega)]; rfl
    rename_i e; subst e
    refine ⟨T.L26d0.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨hrsp, hrbp⟩, (by q4_rg hRg), hF',
        hWf', hmT'.get, hN1, hN2, S, QS.av fr 0x480, A0, lo, hi1, QS.mid lo (hi1 - 1), hax, hD, hc,
        hR, (hSRi (by omega)).mpr hSR, hQ, fun r => (hav r).trans (by rw [h9i]), hdx, hcx, h3, hdi,
        hsi, h8, Or.inl rfl⟩), ?_⟩
    simp only [V.L26d0, VD.L26d0]
    rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ rfl]
    exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L26d0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L26d0" ⟨"sbr_reset.L26d0", B.L26d0, some "sbr_reset.L26df"⟩ := by
  info_off
  measure_hb "L26d0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A, A0, lo, hi1, pos,
      hax, hD, hc, hR, hSR, hQ, hAv, hdx, hcx, h3, hdi, hsi, h8, hpos⟩ :=
      Q4.g_iff.mp (T.L26d0.mp hs)
    clear hs
    rw [V.L26d0] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hRs : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := hX.rc
    have hW := qw_cur hQ
    simp only at hW
    have hQS := qw_drop hQ
    have hcx' : s₀.regs.get64 .rcx = QS.ep t₀ 0x480 (hi1 - 1) := by
      rw [hcx]; exact ep_sub2 _ _ _ (by omega)
    have hst := Q4.sd_st hm hF hWf (o := 0x480) (q := lo) (by omega) (by omega)
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
      have := Q4.cur_range hR hQ.2 (q := pos) (by omega)
      rw [h8]; exact Q4.toInt_ofInt16 this.1 this.2
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
    simp only [B.L26d0]
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
    refine ⟨T.L26df.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF', hWf',
        hmT'.get, hN1, hN2, S, _, lo, hi1, ?_, hD, hc, hR, (hSRi (by omega)).mpr hSR, hQ', ?_, ?_,
        h3, ?_, ?_, ?_, ?_⟩), ?_⟩
    all_goals try (regs_simp; assumption)
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · regs_simp; rw [sw16_zx]; exact av_bytes _ _ _
    · simp only [V.L26df, VD.L26df]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp)]
      exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L2700 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2700" ⟨"sbr_reset.L2700", B.L2700, some "sbr_reset.L2710"⟩ := by
  info_off
  measure_hb "L2700"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h8⟩ :=
      Q4.g_iff.mp (T.L2700.mp hs)
    clear hs
    rw [V.L2700] at hn
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
    simp only [B.L2700]
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
      refine ⟨by decide, T.L2640.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, ?_, hD, hR, hSR, hQS⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L2640, VD.L2640]
      regs_simp
      rw [stkPhi_mk s₀ _ _ _ (by regs_simp), hax, hdx, hcx, hwI, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)
    · simp only [decide_eq_false_iff_not] at c
      refine ⟨T.L2710.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨?_, ?_⟩, (by q4_rg hRg), hF,
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
      · simp only [V.L2710, VD.L2710]
        regs_simp
        rw [stkPhi_mk s₀ _ _ _ (by regs_simp)]
        exact Nat.le_refl _

set_option maxRecDepth 100000 in
theorem blk_L26df (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L26df" ⟨"sbr_reset.L26df", B.L26df, some "sbr_reset.L2700"⟩ := by
  info_off
  measure_hb "L26df"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h8, h11⟩ :=
      Q4.g_iff.mp (T.L26df.mp hs)
    clear hs
    rw [V.L26df] at hn
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
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q4.sd_st hm hF hWf (o := 0x480) (q := hi1 - 1)
      (by omega) (by omega) (BitVec.setWidth 16 (s₀.regs.get64 .r8))
    rw [← hcx'] at hm1
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rcx) 2).isSome = true := by
      rw [hcx', av_load hm hF (by omega)]; rfl
    have hld2 : ((s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2
        (BitVec.setWidth 16 (s₀.regs.get64 .r8)).toInt).loadInt (s₀.regs.get64 .rsi) 2).isSome
        = true := by
      rw [hsi, av_load hm1 hF1 (by unfold QS.mid; omega)]; rfl
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q4.sd_st hm1 hF1 hWf1 (o := 0x480)
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
    simp only [B.L26df]
    vcgen
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, Option.isSome_some, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
    · -- `A mid ≤ A e`: to L2700
      rename_i e c1; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2700.mpr (Q4.g_iff.mpr ⟨row, k2, st, fr, hA.get, ⟨hrsp, hrbp⟩,
          (by q4_rg hRg), hF, hWf, hmT.get, hN1, hN2, S, A0, lo, hi1, hax, hD, hc, hR, hSR, hQ,
          hdx, hcx, h3, hdi, hsi, h8⟩), Or.inr ⟨?_, by decide⟩⟩
      simp only [V.L2700, VD.L2700]
      rw [stkPhi_mk s₀ _ _ _ rfl]
    · rename_i e c1; subst e; exact hld1
    · rename_i e c1; subst e; exact hld2
    all_goals rename_i e c1 f c2; subst e
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at c2
    · -- not three elements: to L2710
      rw [cc_nz_sub, hdx, hcx, show (-4 : Int64).toBitVec = 18446744073709551612#64 from rfl,
        e3] at c2
      simp only [q1_ep_inj hRs (show 0x480 + 2 * (lo + 1) ≤ 0x548 by omega)
        (show 0x480 + 2 * (hi1 - 3 + 1) ≤ 0x548 by omega), Bool.not_eq_true',
        decide_eq_false_iff_not] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2710.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
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
      · simp only [V.L2710, VD.L2710]
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
      refine ⟨by decide, T.L2640.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, ?_, hD, hR, hSR', qw_drop hQ'⟩),
              Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      simp only [V.L2640, VD.L2640]
      regs_simp
      rw [hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hphi' _ _ _ (by regs_simp),
        hdx, hcx, hwI, hphi]
      exact lex_head_lt (by unfold wt; simp only; omega) (by unfold wt at *; simp only at *; omega)

set_option maxRecDepth 100000 in
theorem blk_L2710 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2710" ⟨"sbr_reset.L2710", B.L2710, some "sbr_reset.L2730"⟩ := by
  info_off
  measure_hb "L2710"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, st, fr, hX, ⟨hrsp, hrbp⟩, hRg, hF, hWf, hm, hN1, hN2, S, A0, lo, hi1, hax, hD,
      hc, hR, hSR, hQ, hdx, hcx, h3, hdi, hsi, h4, h11, h8⟩ :=
      Q4.g_iff.mp (T.L2710.mp hs)
    clear hs
    rw [V.L2710] at hn
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
      obtain ⟨hm1, hF1, -⟩ := Q4.sd_st hm hF hWf (o := 0x480) (q := QS.mid lo (hi1 - 1)) (by omega)
        (by omega) x
      rw [hsi, hdi, av_load hm1 hF1 (by omega)]; rfl
    obtain ⟨hm1, hF1, hWf1, hSR1, hav1⟩ := Q4.sd_st hm hF hWf (o := 0x480)
      (q := QS.mid lo (hi1 - 1)) (by omega) (by omega) (BitVec.ofInt 16 (QS.av fr 0x480 (hi1 - 2)))
    rw [← hsi] at hm1
    obtain ⟨hm2, hF2, hWf2, hSR2, hav2⟩ := Q4.sd_st hm1 hF1 hWf1 (o := 0x480)
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
    simp only [B.L2710]
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
      refine ⟨by decide, T.L2749.mpr (Q4.g_iff.mpr ⟨row, k2, st, _, hA.get, ⟨?_, ?_⟩,
          (by q4_rg hRg), hF2, hWf2, hmT2.get, hN1, hN2, S, A0, lo, hi1, ?_, hD, hc, hR, hSR', hQ',
          ?_, ?_, ?_, lo + 1, hi1 - 3, _, hPI, ?_, ?_, by omega⟩), Or.inl ?_⟩
      · regs_simp; exact hrsp
      · regs_simp; exact hrbp
      · regs_simp; exact hax
      · regs_simp; exact hdx
      · regs_simp; exact hcx
      · regs_simp; exact hdi
      · regs_simp; rw [hdx]; exact q1_ep_add2 _ _ _
      · regs_simp; exact h8
      · simp only [V.L2749, VD.L2749]
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

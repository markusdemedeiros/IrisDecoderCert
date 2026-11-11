import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the partition branches (`L4164`, `L4194`, `L4190`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- `right - 1` as an address. -/
theorem tlC_dec2 (P : BitVec 64) (r : Nat) (h : 1 ≤ r) :
    BitVec.setWidth 64 (-2 : Int64).toBitVec + (P + BitVec.ofNat 64 (2 * r))
      = P + BitVec.ofNat 64 (2 * (r - 1)) := by
  have c : (BitVec.setWidth 64 (-2 : Int64).toBitVec).toNat = 2 ^ 64 - 2 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, c, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- `left + 1` as an address. -/
theorem tlC_inc2 (P : BitVec 64) (l : Nat) :
    P + BitVec.ofNat 64 (2 * l) + 2#64 = P + BitVec.ofNat 64 (2 * (l + 1)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem blk_L4164 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4164" := by
  cfg_block
  measure_hb "L4164"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, -⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4164] at hn
    subst hn
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hI := hPI
    unfold PInv at hI
    have t10 : (s₀.regs.get64 .r10).toNat = (pA t₀).toNat + 2 * l := by
      rw [hPR.1]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * rt := by
      rw [hPR.2.1]; exact tn_add _ _ (by omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    · -- `right < left`: to L41b0
      rename_i e c; subst e
      rw [CondCode.interp_a_sub _ _ _ rfl, t10, t9] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L41b0 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · exact ⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, by omega⟩,
          hmT.get⟩
      · rw [var_L41b0, phiC_mk _ _ _ _ rfl rfl rfl rfl, t10, t9]
        simp only [QV]
        split <;> omega
    · -- `left ≤ right`: falls into L4169
      rename_i e c; subst e
      rw [CondCode.interp_a_sub _ _ _ rfl, t10, t9] at c
      simp only [decide_eq_false_iff_not] at c
      refine ⟨(tab_L4169 _ _ _ _ _).2 ?_, ?_⟩
      · exact ⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, by omega⟩,
          hmT.get⟩
      · rw [var_L4169, phiC_mk _ _ _ _ rfl rfl rfl rfl]
        simp only [QV, dP, rN]
        rw [t10, t9]
        split <;> omega

theorem blk_L4194 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4194" := by
  cfg_block
  measure_hb "L4194"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR,
      hl, hpl, h15⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4194] at hn
    subst hn
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hI := hPI
    unfold PInv at hI
    have t10 : (s₀.regs.get64 .r10).toNat = (pA t₀).toNat + 2 * l := by
      rw [hPR.1]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * rt := by
      rw [hPR.2.1]; exact tn_add _ _ (by omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    · -- `right < left`: back to L4164
      rename_i e c; subst e
      rw [CondCode.interp_a_sub _ _ _ rfl, t10, t9] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4164 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · exact ⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, trivial⟩,
          hmT.get⟩
      · rw [var_L4164, phiC_mk _ _ _ _ rfl rfl rfl rfl]
        simp only [QV, dP, lle, rN]
        rw [t10, t9]
        split <;> (try split) <;> omega
    · -- `left ≤ right`: falls into L4199
      rename_i e c; subst e
      rw [CondCode.interp_a_sub _ _ _ rfl, t10, t9] at c
      simp only [decide_eq_false_iff_not] at c
      refine ⟨(tab_L4199 _ _ _ _ _).2 ?_, ?_⟩
      · exact ⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP,
          ⟨hSR, hCur, hPI, hPR, by omega, hpl (by omega), h15⟩, hmT.get⟩
      · rw [var_L4199, phiC_mk _ _ _ _ rfl rfl rfl rfl]
        simp only [QV, dP, rN]
        rw [t10, t9]
        split <;> omega

theorem blk_L4190 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4190" := by
  cfg_block
  measure_hb "L4190"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR,
      hl, hpl, hpr, h15⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4190] at hn
    subst hn
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hI := hPI
    unfold PInv at hI
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
    have hPI' : PInv (AV fl) lo (hi1 - 1) l (rt - 1) pv :=
      ⟨i1, by omega, by omega, i4, i5, i6, fun q h1 h2 => by
        by_cases e : q = rt
        · subst e; exact Nat.le_of_lt hpr
        · exact i7 q (by omega) h2⟩
    have t10 : (s₀.regs.get64 .r10).toNat = (pA t₀).toNat + 2 * l := by
      rw [hPR.1]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * rt := by
      rw [hPR.2.1]; exact tn_add _ _ (by omega)
    have e9 : BitVec.setWidth 64 (-2 : Int64).toBitVec + s₀.regs.get64 .r9
        = pA t₀ + v64 (2 * (rt - 1)) := by
      rw [hPR.2.1]; exact tlC_dec2 _ _ (by omega)
    have t9' : (pA t₀ + v64 (2 * (rt - 1))).toNat = (pA t₀).toNat + 2 * (rt - 1) :=
      tn_add _ _ (by omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := hCur
    rename_i e; subst e
    refine ⟨(tab_L4194 _ _ _ _ _).2 ?_, ?_⟩
    · refine ⟨?_, S, lo, hi1, l, rt - 1, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
        hPI', ⟨?_, ?_, ?_⟩, by omega, fun _ => hpl, ?_⟩, hmT.get⟩
      · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hPR.1
      · regs_simp; exact e9
      · regs_simp; exact hPR.2.2
      · regs_simp; exact h15
    · rw [var_L4194, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
      simp only [QV, dP, lle, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [e9, t9', t10, t9]
      split <;> omega

end Kraken.Examples.Sbr.Tlim

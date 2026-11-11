import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the end of the median of three (`L40f7`, `L4105`, `L4110`,
`L4120`, `L4130`)
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
theorem tlq_addr3 (P : BitVec 64) (hi1 : Nat) (h : 3 ≤ hi1) :
    P + BitVec.ofNat 64 (2 * hi1) - 2#64 + 18446744073709551612#64
      = P + BitVec.ofNat 64 (2 * (hi1 - 3)) := by
  rw [show 2 * hi1 = 2 * (hi1 - 3) + 6 by omega]; bv_omega

theorem blk_L40f7 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40f7" := by
  cfg_block
  measure_hb "L40f7"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨h2, hdi, hr8⟩, hlm, hle⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L40f7] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hmd : mid lo (hi1 - 1) < NN x := by unfold mid; omega
    have hvm := hv _ hmd
    have hve := hv (hi1 - 1) (by omega)
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2 = some (u16 fl (mid lo (hi1 - 1)) : Int) :=
      ld16 hfl _ hdi (by simp only; unfold mid; omega) (by simp only; omega)
    have L2 : s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2 = some (u16 fl (hi1 - 1) : Int) :=
      ld16 hfl (hi1 - 1) (by rw [hdx]; exact hi_addr _ _ (by omega)) (by simp only; omega)
        (by simp only; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm hfl
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L2]; rfl
    · -- `A mid ≤ A e`: to L4120
      rename_i e vm lm ve le c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at lm le
      rw [L1] at lm; rw [L2] at le
      simp only [Option.some.injEq] at lm le
      subst lm le
      simp only [sw16'] at c
      rw [cc16_le _ _ hvm hve] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4120 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          ⟨h2, ?_, ?_⟩, hlm, c, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hdi
        · regs_simp; exact hr8
        · regs_simp; exact zx16' _ (Nat.lt_trans hvm (by decide))
      · rw [var_L4120, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · -- `A e < A mid`: falls into L4105
      rename_i e vm lm ve le c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at lm le
      rw [L1] at lm; rw [L2] at le
      simp only [Option.some.injEq] at lm le
      subst lm le
      simp only [sw16'] at c
      rw [cc16_le _ _ hvm hve] at c
      simp only [decide_eq_false_iff_not] at c
      refine ⟨?_, ?_⟩
      rotate_left
      · rw [var_L4105, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _
      rw [tab_L4105]
      refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
        ⟨h2, ?_, ?_⟩, hle, Nat.lt_of_not_le c, ?_, ?_⟩, hmT.get⟩
      · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hdi
      · regs_simp; exact hr8
      · regs_simp; exact zx16' _ (Nat.lt_trans hvm (by decide))
      · regs_simp; exact zx16' _ (Nat.lt_trans hve (by decide))

theorem blk_L4105 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4105" := by
  cfg_block
  measure_hb "L4105"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨h2, hdi, hr8⟩, hle, hlt, hr9, hr15⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L4105] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hmd : mid lo (hi1 - 1) < hi1 - 1 := by unfold mid; omega
    have hvm := hv _ (show mid lo (hi1 - 1) < NN x by omega)
    have hve := hv (hi1 - 1) (by omega)
    have hdx' : s₀.regs.get64 .rdx = pA t₀ + BitVec.ofNat 64 (2 * (hi1 - 1)) := by
      rw [hdx]; exact hi_addr _ _ (by omega)
    have hl1' : (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt).length = 60 := by
      rw [setW2_length _ _ _ (by omega)]; exact hl1
    have hm2 : ∀ w, (s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt).storeInt (s₀.regs.get64 .rdi) 2 w
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 fl (hi1 - 1)
          (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt) (mid lo (hi1 - 1)) w, x.a.nlim, stk, pb⟩ :=
      fun w => st_fl (st_fl hm hl1 (hi1 - 1) (by omega) hdx' _) hl1' _ (by omega) hdi w
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (w : Int), R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = s₀.regs.get64 .rcx → R.get64 .rsi = s₀.regs.get64 .rsi →
        R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := (s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2
                  (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt).storeInt (s₀.regs.get64 .rdi) 2 w }
          = phi (S ++ [(lo, hi1)]) :=
        fun R zm sf w e2 e3 e4 e5 => by
      have h := hm2 w
      exact phiC_eq h hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hA2 : ∀ q, AV (setW2 (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt)
        (mid lo (hi1 - 1)) (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) q
        = swap (AV fl) (mid lo (hi1 - 1)) (hi1 - 1) q := fun q => by
      rw [hr15, AV_set hl1' _ (by omega) _ (by omega) q]
      apply upd_swap_of
      intro r; rw [hr9]; exact AV_set hl1 _ (by omega) _ (by omega) r
    have hQI2 := qi_swap hQI (i := mid lo (hi1 - 1)) (j := hi1 - 1)
      ⟨by simp only; unfold mid; omega, by simp only; omega⟩ ⟨by simp only; omega, by simp only; omega⟩
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2).isSome = true := by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hdx' (by simp only; omega)
        (by simp only; omega)]
      rfl
    have hld2 : ((s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2
        (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt).loadInt (s₀.regs.get64 .rdi) 2).isSome
        = true := by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) (st_fl hm hl1 (hi1 - 1) (by omega) hdx' _)) _
        hdi (by simp only; rw [hl1']; omega) (by simp only; omega)]
      rfl
    have hmT' : Box _ := ⟨hm2⟩
    clear hm hm2
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld1
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld2
    · (have e : s₀ = _ := ‹s₀ = _›; subst e)
      rw [tab_L4110, var_L4110, hphi' _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
        (by regs_simp)]
      have e1 : AV (setW2 (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt)
        (mid lo (hi1 - 1)) (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) lo = AV fl lo := by
        refine (hA2 lo).trans ?_
        have n1 : ¬lo = lo + (hi1 - 1 - lo) / 2 := by omega
        have n2 : ¬lo = hi1 - 1 := by omega
        simp only [swap_eq, n1, n2, ↓reduceIte]
      have e2 : AV (setW2 (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt)
        (mid lo (hi1 - 1)) (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) (mid lo (hi1 - 1))
          = AV fl (hi1 - 1) := by
        refine (hA2 _).trans ?_
        simp only [swap_eq, ↓reduceIte]
      have e3 : AV (setW2 (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r9)).toInt)
        (mid lo (hi1 - 1)) (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) (hi1 - 1)
          = AV fl (mid lo (hi1 - 1)) := by
        refine (hA2 _).trans ?_
        have n1 : ¬hi1 - 1 = lo + (hi1 - 1 - lo) / 2 := by omega
        simp only [swap_eq, n1, ↓reduceIte]
      refine ⟨⟨by simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR,
        S, lo, hi1, _, stk, pb,
        Lens_set (Lens_set hL (hi1 - 1) (by omega) _) _ (by omega) _, hP,
        ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, qi_congr hQI2 hA2⟩, ⟨⟨h2, ?_, ?_⟩, ?_, ?_, ?_⟩⟩, hmT'.get _⟩,
        by (try rw [hphi]); simp only [QV]; omega⟩
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hdi
      · regs_simp; exact hr8
      · rw [e1, e2]; exact hle
      · rw [e2, e3]; exact Nat.le_of_lt hlt
      · regs_simp; rw [e2]; exact hr15

theorem blk_L4110 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4110" := by
  cfg_block
  measure_hb "L4110"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨⟨h2, hdi, hr8⟩, hlm, hme, hr15⟩⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L4110] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have tsi : (s₀.regs.get64 .rsi).toNat = (pA t₀).toNat + 2 * lo := by
      rw [hsi]; exact tn_add _ _ (by omega)
    have h9 : s₀.regs.get64 .rdx + 18446744073709551612#64 = pA t₀ + v64 (2 * (hi1 - 3)) := by
      rw [hdx]; exact tlq_addr3 _ _ (by omega)
    have t9 : (pA t₀ + v64 (2 * (hi1 - 3))).toNat = (pA t₀).toNat + 2 * (hi1 - 3) :=
      tn_add _ _ (by omega)
    have h4 : (-4 : Int64).toBitVec = 18446744073709551612#64 := by decide
    have hE : (s₀.regs.get64 .rsi == pA t₀ + v64 (2 * (hi1 - 3))) = decide (hi1 = lo + 3) := by
      by_cases hc : hi1 = lo + 3
      · simp only [decide_eq_true hc, beq_iff_eq]
        apply BitVec.eq_of_toNat_eq; rw [tsi, t9]; omega
      · simp only [decide_eq_false hc, beq_eq_false_iff_ne, ne_eq]
        intro e; have := congrArg BitVec.toNat e; rw [tsi, t9] at this; omega
    have hDrop : hi1 = lo + 3 → QI (NN x) (AV fl) (A0 x) S ∧ stkPhi s₀ S.length = phi S :=
      fun h => by
        have hd := qi_drop (S := S) (I := (lo, hi1)) hQI (fun q h1 h2 => by
          simp only at h1 h2
          have e : mid lo (hi1 - 1) = lo + 1 := by unfold mid; omega
          rcases (show q = lo ∨ q = lo + 1 by omega) with e1 | e1
          · rw [e1, ← e]; exact hlm
          · rw [e1, show lo + 1 + 1 = hi1 - 1 by omega, ← e]; exact hme)
        exact ⟨hd, stkPhi_S hm hl2 hbp hR.1 hSR hd (by omega)⟩
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    · -- `start ≠ end - 2`: to L4130
      rename_i c
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result_sub, h4, h9, hE] at c
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4130 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          ⟨⟨h2, ?_, ?_⟩, hlm, hme, ?_⟩, by omega, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hdi
        · regs_simp; exact hr8
        · regs_simp; exact hr15
        · regs_simp; rw [h4, h9]
      · rw [var_L4130, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · -- three elements, sorted: drop
      rename_i c
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result_sub, h4, h9, hE] at c
      simp only [Bool.not_eq_false', decide_eq_true_eq] at c
      obtain ⟨hd, hpS⟩ := hDrop c
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4060]
        refine ⟨?_, S, ?_, hD, fl, stk, pb, hL, hP, ⟨hSR, hd⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
      · rw [var_L4060, stkPhi_mk _ _ _ _ (by regs_simp)]
        dsimp only [rN]
        rw [Reg64s.get64_set64]; simp only [reduceCtorEq, ↓reduceIte]
        rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hpS, hphi, phi_append, phi_one]
        unfold wt; simp only [QV]; omega


theorem blk_L4120 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4120" := by
  cfg_block
  measure_hb "L4120"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨h2, hdi, hr8⟩, hlm, hme, hr9⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L4120] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have tsi : (s₀.regs.get64 .rsi).toNat = (pA t₀).toNat + 2 * lo := by
      rw [hsi]; exact tn_add _ _ (by omega)
    have h9 : s₀.regs.get64 .rdx + 18446744073709551612#64 = pA t₀ + v64 (2 * (hi1 - 3)) := by
      rw [hdx]; exact tlq_addr3 _ _ (by omega)
    have t9 : (pA t₀ + v64 (2 * (hi1 - 3))).toNat = (pA t₀).toNat + 2 * (hi1 - 3) :=
      tn_add _ _ (by omega)
    have h4 : (-4 : Int64).toBitVec = 18446744073709551612#64 := by decide
    have hE : (s₀.regs.get64 .rsi == pA t₀ + v64 (2 * (hi1 - 3))) = decide (hi1 = lo + 3) := by
      by_cases hc : hi1 = lo + 3
      · simp only [decide_eq_true hc, beq_iff_eq]
        apply BitVec.eq_of_toNat_eq; rw [tsi, t9]; omega
      · simp only [decide_eq_false hc, beq_eq_false_iff_ne, ne_eq]
        intro e; have := congrArg BitVec.toNat e; rw [tsi, t9] at this; omega
    have hDrop : hi1 = lo + 3 → QI (NN x) (AV fl) (A0 x) S ∧ stkPhi s₀ S.length = phi S :=
      fun h => by
        have hd := qi_drop (S := S) (I := (lo, hi1)) hQI (fun q h1 h2 => by
          simp only at h1 h2
          have e : mid lo (hi1 - 1) = lo + 1 := by unfold mid; omega
          rcases (show q = lo ∨ q = lo + 1 by omega) with e1 | e1
          · rw [e1, ← e]; exact hlm
          · rw [e1, show lo + 1 + 1 = hi1 - 1 by omega, ← e]; exact hme)
        exact ⟨hd, stkPhi_S hm hl2 hbp hR.1 hSR hd (by omega)⟩
    have hvm := qi_lt hR.1 hQI _ (show mid lo (hi1 - 1) < NN x by unfold mid; omega)
    have hr15 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r9))
        = v64 (AV fl (mid lo (hi1 - 1))) := by
      rw [hr9]; exact zx32_64 _ (Nat.lt_trans hvm (by decide))
    have hE2 : (s₀.regs.get64 .rsi == t₀.regs.get64 .rdi + 312050#64
        + BitVec.ofNat 64 (2 * (hi1 - 3))) = decide (hi1 = lo + 3) := hE
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    · -- three elements, sorted: drop
      rename_i c
      simp only [CondCode.interp_z, StatusFlags.zf_from_result_sub, h4, h9, hE, decide_eq_true_eq] at c
      obtain ⟨hd, hpS⟩ := hDrop c
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4060]
        refine ⟨?_, S, ?_, hD, fl, stk, pb, hL, hP, ⟨hSR, hd⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
      · rw [var_L4060, stkPhi_mk _ _ _ _ (by regs_simp)]
        dsimp only [rN]
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        try rw [hcx]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hpS, hphi, phi_append, phi_one]
        unfold wt; simp only [QV]; omega
    · -- `start ≠ end - 2`: to L4130
      rename_i c
      simp only [CondCode.interp_z, StatusFlags.zf_from_result_sub, h4, h9, hE, decide_eq_false_iff_not] at c
      refine ⟨(tab_L4130 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          ⟨⟨h2, ?_, ?_⟩, hlm, hme, ?_⟩, by omega, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hdi
        · regs_simp; exact hr8
        · regs_simp; exact hr15
        · regs_simp; rw [h4, h9]
      · rw [var_L4130, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _

theorem blk_L4130 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4130" := by
  cfg_block
  measure_hb "L4130"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨⟨h2, hdi, hr8⟩, hlm, hme, hr15⟩,
      h3, hr9⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4130] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hm1 : lo + 1 ≤ mid lo (hi1 - 1) := by unfold mid; omega
    have hm3 : mid lo (hi1 - 1) < hi1 - 2 := by unfold mid; omega
    have hvm := hv _ (show mid lo (hi1 - 1) < NN x by omega)
    have hv2 := hv (hi1 - 2) (by omega)
    have hr8' : s₀.regs.get64 .r8 = pA t₀ + BitVec.ofNat 64 (2 * (hi1 - 2)) := by
      rw [hr8, show hi1 - 1 - 1 = hi1 - 2 by omega]
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r8) 2 = some (u16 fl (hi1 - 2) : Int) :=
      ld16 hfl _ hr8' (by simp only; omega) (by simp only; omega)
    have hl1' : ∀ w, (setW2 fl (mid lo (hi1 - 1)) w).length = 60 := fun w => by
      rw [setW2_length _ _ _ (by omega)]; exact hl1
    have hm2 : ∀ w1 w2, (s₀.dmem.storeInt (s₀.regs.get64 .rdi) 2 w1).storeInt
          (s₀.regs.get64 .r8) 2 w2
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 fl (mid lo (hi1 - 1)) w1) (hi1 - 2) w2,
          x.a.nlim, stk, pb⟩ :=
      fun w1 w2 => st_fl (st_fl hm hl1 _ (by omega) hdi w1) (hl1' w1) _ (by omega) hr8' w2
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (w1 w2 : Int),
        R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = s₀.regs.get64 .rcx → R.get64 .rsi = s₀.regs.get64 .rsi →
        R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := (s₀.dmem.storeInt (s₀.regs.get64 .rdi) 2 w1).storeInt
                  (s₀.regs.get64 .r8) 2 w2 }
          = phi (S ++ [(lo, hi1)]) :=
        fun R zm sf w1 w2 e2 e3 e4 e5 => by
      have h := hm2 w1 w2
      exact phiC_eq h hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hA2 : ∀ q, AV (setW2 (setW2 fl (mid lo (hi1 - 1))
        (BitVec.ofNat 16 (AV fl (hi1 - 2))).toInt) (hi1 - 2)
        (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) q
        = swap (AV fl) (hi1 - 2) (mid lo (hi1 - 1)) q := fun q => by
      rw [← sw64_16, hr15, AV_set (hl1' _) _ (by omega) _ (by omega) q]
      apply upd_swap_of
      intro r; exact AV_set hl1 _ (by omega) _ (by omega) r
    have hQI2 := qi_swap hQI (i := hi1 - 2) (j := mid lo (hi1 - 1))
      ⟨by simp only; omega, by simp only; omega⟩ ⟨by simp only; omega, by simp only; omega⟩
    have tsi : (s₀.regs.get64 .rsi).toNat = (pA t₀).toNat + 2 * lo := by
      rw [hsi]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * (hi1 - 3) := by
      rw [hr9]; exact tn_add _ _ (by omega)
    have hld2 : (s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2).isSome = true := by
      rw [ld16 hfl _ hdi (by simp only; omega) (by simp only; omega)]; rfl
    have hld3 : ∀ w, ((s₀.dmem.storeInt (s₀.regs.get64 .rdi) 2 w).loadInt
        (s₀.regs.get64 .r8) 2).isSome = true := fun w => by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) (st_fl hm hl1 _ (by omega) hdi w)) _
        hr8' (by simp only; (try rw [hl1']); omega) (by simp only; (try rw [hl1']); omega)]; rfl
    have e10 : s₀.regs.get64 .rsi + 2#64 = pA t₀ + v64 (2 * (lo + 1)) := by
      rw [hsi, BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
    have t10 : (pA t₀ + v64 (2 * (lo + 1))).toNat = (pA t₀).toNat + 2 * (lo + 1) :=
      tn_add _ _ (by omega)
    have eL : ∀ q, q ≠ hi1 - 2 → q ≠ mid lo (hi1 - 1) →
        swap (AV fl) (hi1 - 2) (mid lo (hi1 - 1)) q = AV fl q := fun q h1 h2 => by
      simp only [swap_eq, h1, h2, ↓reduceIte]
    have ePv : swap (AV fl) (hi1 - 2) (mid lo (hi1 - 1)) (hi1 - 1 - 1) = AV fl (mid lo (hi1 - 1)) := by
      rw [show hi1 - 1 - 1 = hi1 - 2 by omega]; simp only [swap_eq, ↓reduceIte]
    have hPI : PInv (swap (AV fl) (hi1 - 2) (mid lo (hi1 - 1))) lo (hi1 - 1) (lo + 1) (hi1 - 3)
        (AV fl (mid lo (hi1 - 1))) := by
      refine ⟨by omega, by omega, by omega, by omega, ePv, fun q h1 h2 => ?_, fun q h1 h2 => ?_⟩
      · rw [show q = lo by omega, eL _ (by omega) (by omega)]; exact hlm
      · rcases (show q = hi1 - 2 ∨ q = hi1 - 1 by omega) with e | e
        · rw [e]; simp only [swap_eq, ↓reduceIte]; exact Nat.le_refl _
        · rw [e, eL _ (by omega) (by omega)]; exact hme
    have hmT' : Box _ := ⟨hm2⟩
    clear hm hm2 hfl
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    · rw [L1]; rfl
    · exact hld2
    · exact hld3 _
    all_goals
      rename_i v ll c
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll c
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [CondCode.interp_be_sub _ _ _ rfl, e10, t10, t9] at c
      simp only [sw16']
      left; apply Table.ofLabels_at
    · -- `left ≤ right`: to L4169
      simp only [decide_eq_true_eq] at c
      refine ⟨by decide, (tab_L4169 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, lo + 1, hi1 - 3, AV fl (mid lo (hi1 - 1)), _, stk, pb,
          Lens_set (Lens_set hL _ (by omega) _) _ (by omega) _, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, qi_congr hQI2 hA2⟩, ?_, ⟨?_, ?_, ?_⟩, by omega⟩,
          hmT'.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · first
            | exact (congrArg (fun A => PInv A lo (hi1 - 1) (lo + 1) (hi1 - 3)
                (AV fl (mid lo (hi1 - 1)))) (funext hA2)).mpr hPI
            | (rw [show (fun q => AV _ q) = _ from funext hA2]; exact hPI)
        · regs_simp; exact e10
        · regs_simp; exact hr9
        · regs_simp; exact hr8
      · rw [var_L4169, hphi' _ _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp), hphi]
        simp only [QV, dP, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [e10, t10, t9]
        omega
    · -- `right < left`: to L41b4
      simp only [decide_eq_false_iff_not] at c
      exfalso; omega

end Kraken.Examples.Sbr.Tlim

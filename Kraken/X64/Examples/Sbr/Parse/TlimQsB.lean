import Kraken.X64.Examples.Sbr.Parse.TlimQsLib

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the interval dispatch (`L4090`)
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
theorem cc_nc_sub' {w : Nat} (a b : BitVec w) (af ofl : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := ofl })
      = decide (b.toNat ≤ a.toNat) := cc_nc_sub _ _ _ rfl

theorem blk_L4090 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4090" := by
  cfg_block
  measure_hb "L4090"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨hcx, hD, hDc, hsi, hdx, hQI⟩, -⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4090] at hn
    subst hn
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hv := qi_lt hR.1 hQI
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have L1 : lo + 3 ≤ hi1 → s₀.dmem.loadInt (s₀.regs.get64 .rsi) 2 = some (u16 fl lo : Int) :=
      fun h => ld16 hfl lo hsi (by simp only; omega) (by simp only; omega)
    have L2 : lo + 3 ≤ hi1 → s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2
        = some (u16 fl (hi1 - 1) : Int) :=
      fun h => ld16 hfl (hi1 - 1) (by rw [hdx]; exact hi_addr _ _ (by omega)) (by simp only; omega)
        (by simp only; omega)
    have hmid : lo + 3 ≤ hi1 → s₀.regs.get64 .rsi
        + (s₀.regs.get64 .rdx - s₀.regs.get64 .rsi).sshiftRight 2 * 2#64 + 0#64
        = pA t₀ + BitVec.ofNat 64 (2 * mid lo (hi1 - 1)) := fun h => by
      rw [hsi, hdx]; exact mid_addr _ _ _ (by omega) (by omega) (by omega) (by omega)
    have L3 : lo + 3 ≤ hi1 → s₀.dmem.loadInt (s₀.regs.get64 .rsi
        + (s₀.regs.get64 .rdx - s₀.regs.get64 .rsi).sshiftRight 2 * 2#64 + 0#64) 2
        = some (u16 fl (mid lo (hi1 - 1)) : Int) :=
      fun h => ld16 hfl _ (hmid h) (by simp only; unfold mid; omega) (by simp only; omega)
    have hDrop : hi1 ≤ lo + 1 → QI (NN x) (AV fl) (A0 x) S ∧ stkPhi s₀ S.length = phi S :=
      fun h => by
        have hd := qi_drop_small (S := S) (I := (lo, hi1)) hQI (by simp only; omega)
        exact ⟨hd, stkPhi_S hm hl2 hbp hR.1 hSR hd (by omega)⟩
    have tsi : (s₀.regs.get64 .rsi).toNat = (pA t₀).toNat + 2 * lo := by
      rw [hsi]; exact tn_add _ _ (by omega)
    have tdx : (s₀.regs.get64 .rdx).toNat = (pA t₀).toNat + 2 * hi1 - 2 := by
      rw [hdx]; exact tn_hi _ _ (by omega) (by omega)
    have tdx4 : (s₀.regs.get64 .rdx + 18446744073709551614#64).toNat
        = (pA t₀).toNat + 2 * hi1 - 4 := by
      rw [hdx]; exact tn_hi4 _ _ (by omega) (by omega)
    have h2el : ¬(pA t₀).toNat + 2 * hi1 - 2 ≤ (pA t₀).toNat + 2 * lo →
        (pA t₀).toNat + 2 * hi1 - 4 ≤ (pA t₀).toNat + 2 * lo → hi1 = lo + 2 := by
      intro a b; omega
    have hlt : lo + 3 ≤ hi1 → lo < NN x := fun h => by omega
    have hlte : lo + 3 ≤ hi1 → hi1 - 1 < NN x := fun h => by omega
    have hltm : lo + 3 ≤ hi1 → mid lo (hi1 - 1) < NN x := fun h => by unfold mid; omega
    have hmT : Box _ := ⟨hm⟩
    clear hm hfl
    vcgen
    all_goals try call_simp
    all_goals simp only [AddrIndex.offset64_scale2,
      Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.ofNat_eq_ofNat] at *
    · -- start ≥ end: drop
      rename_i e c1; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      simp only [decide_eq_true_eq] at c1
      obtain ⟨hd, hpS⟩ := hDrop (by omega)
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L4060]
        exact ⟨hR, S, hcx, hD, fl, stk, pb, hL, hP, ⟨hSR, hd⟩, hmT.get⟩
      · rw [var_L4060, stkPhi_mk _ _ _ _ rfl]
        dsimp only [rN]
        rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hpS, hphi, phi_append, phi_one]
        unfold wt; simp only [QV]; omega
    · -- two elements
      rename_i e c1 c2; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at c1 c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine (tab_L4280 _ _ _ _ _).2 ?_
        refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, h2el c1 c2⟩,
          hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
      · rw [var_L4280, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · -- load `*start`
      rename_i e c1 b1 b2 b3 c2; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat]
      rw [L1 (by omega)]; rfl
    · -- load `*end`
      rename_i e c1 b1 b2 b3 vl c2 ll; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat]
      rw [L2 (by omega)]; rfl
    · -- load `*mid`
      rename_i e c1 b1 b2 b3 vl vh c2 ll lh; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      rw [L3 (by omega)]; rfl
    · -- `A lo ≤ A e`: to L40e0
      rename_i e c1 b1 b2 b3 vl vh vm cle c2 ll lh lm; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      have h3 : lo + 3 ≤ hi1 := by omega
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat] at ll lh
      rw [L1 h3] at ll; rw [L2 h3] at lh; rw [L3 h3] at lm
      simp only [Option.some.injEq] at ll lh lm
      subst ll lh lm
      simp only [sw16'] at cle
      rw [cc16_le _ _ (hv _ (by omega)) (hv _ (by omega))] at cle
      simp only [decide_eq_true_eq] at cle
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L40e0 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, cle⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hmid h3
        · regs_simp; rw [hdx]; exact hi_addr2 _ _ (by omega)
        · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hlt h3)) (by decide))
        · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hlte h3)) (by decide))
        · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hltm h3)) (by decide))
      · rw [var_L40e0, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · -- `A e < A lo`: falls into L40c3
      rename_i e c1 b1 b2 b3 vl vh vm cle c2 ll lh lm; subst e
      rw [cc_nc_sub _ _ _ rfl, tsi, tdx] at c1
      rw [cc_nc_sub', tsi, tdx4] at c2
      simp only [decide_eq_false_iff_not] at c1 c2
      have h3 : lo + 3 ≤ hi1 := by omega
      simp only [AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat] at ll lh
      rw [L1 h3] at ll; rw [L2 h3] at lh; rw [L3 h3] at lm
      simp only [Option.some.injEq] at ll lh lm
      subst ll lh lm
      simp only [sw16'] at cle
      rw [cc16_le _ _ (hv _ (by omega)) (hv _ (by omega))] at cle
      simp only [decide_eq_false_iff_not] at cle
      refine ⟨?_, ?_⟩
      rotate_left
      · rw [var_L40c3, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _
      rw [tab_L40c3]
      refine ⟨?_, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
        ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, Nat.lt_of_not_le cle⟩, hmT.get⟩
      · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hmid h3
      · regs_simp; rw [hdx]; exact hi_addr2 _ _ (by omega)
      · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hlt h3)) (by decide))
      · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hlte h3)) (by decide))
      · regs_simp; exact zx16' _ (Nat.lt_trans (hv _ (hltm h3)) (by decide))

end Kraken.Examples.Sbr.Tlim

import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the `checksort` scan (`L41e0`)
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

theorem blk_L41e0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41e0" := by
  cfg_block
  measure_hb "L41e0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, m, hm1, hm2,
      hr8, hsrt⟩, hm⟩, hn⟩ := hs₀
    rw [var_L41e0] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hPD' := hPD
    unfold PDone at hPD'
    have t8 : (s₀.regs.get64 .r8).toNat = (pA t₀).toNat + 2 * m := by
      rw [hr8]; exact tn_add _ _ (by omega)
    have tdx : (s₀.regs.get64 .rdx).toNat = (pA t₀).toNat + 2 * hi1 - 2 := by
      rw [hdx]; exact tn_hi _ _ (by omega) (by omega)
    have e8 : s₀.regs.get64 .r8 + 2#64 = pA t₀ + v64 (2 * (m + 1)) := by
      rw [hr8, BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
    have t8' : (pA t₀ + v64 (2 * (m + 1))).toNat = (pA t₀).toNat + 2 * (m + 1) :=
      tn_add _ _ (by omega)
    have hfl := focus (T_fl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have L1 : m < hi1 - 1 → s₀.dmem.loadInt (s₀.regs.get64 .r8) 2 = some (u16 fl m : Int) :=
      fun h => ld16 hfl m hr8 (by simp only; omega) (by simp only; omega)
    have L2 : m < hi1 - 1 → s₀.dmem.loadInt (s₀.regs.get64 .r8 + 2#64) 2
        = some (u16 fl (m + 1) : Int) :=
      fun h => ld16 hfl (m + 1) e8 (by simp only; omega) (by simp only; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm hfl
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · -- `end ≤ p`: to L41f7
      rename_i e c; subst e
      rw [cc_nc_sub _ _ _ rfl, t8, tdx] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L41f7 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, m, hm1, hm2, ?_, hsrt⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
        · regs_simp; exact hr8
      · rw [var_L41f7, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV]; omega
    · rename_i e c; subst e
      rw [cc_nc_sub _ _ _ rfl, t8, tdx] at c
      simp only [decide_eq_false_iff_not] at c
      rw [L1 (by omega)]; rfl
    · rename_i e v c ll; subst e
      rw [cc_nc_sub _ _ _ rfl, t8, tdx] at c
      simp only [decide_eq_false_iff_not] at c
      rw [L2 (by omega)]; rfl
    · -- in order: next
      rename_i e v1 v2 c ll1 ll2 c2; subst e
      rw [cc_nc_sub _ _ _ rfl, t8, tdx] at c
      simp only [decide_eq_false_iff_not] at c
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll1 ll2
      rw [L1 (by omega)] at ll1; rw [L2 (by omega)] at ll2
      simp only [Option.some.injEq] at ll1 ll2; subst ll1 ll2
      rw [sw16', ofInt16_nat, cc16_le _ _ (hv m (by omega)) (hv (m + 1) (by omega))] at c2
      simp only [decide_eq_true_eq] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L41e0 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, m + 1, by omega, by omega, ?_,
            fun q a b => ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
        · regs_simp; exact e8
        · by_cases h : q = m
          · subst h; exact c2
          · exact hsrt q a (by omega)
      · rw [var_L41e0, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [e8, t8', t8, tdx]
        omega
    · -- out of order: falls into L41f7
      rename_i e v1 v2 c ll1 ll2 c2; subst e
      rw [cc_nc_sub _ _ _ rfl, t8, tdx] at c
      simp only [decide_eq_false_iff_not] at c
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll1 ll2
      rw [L1 (by omega)] at ll1; rw [L2 (by omega)] at ll2
      simp only [Option.some.injEq] at ll1 ll2; subst ll1 ll2
      rw [sw16', ofInt16_nat, cc16_le _ _ (hv m (by omega)) (hv (m + 1) (by omega))] at c2
      refine ⟨(tab_L41f7 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, m, hm1, hm2, ?_, hsrt⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
        · regs_simp; exact hr8
      · rw [var_L41f7, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV]; omega

end Kraken.Examples.Sbr.Tlim

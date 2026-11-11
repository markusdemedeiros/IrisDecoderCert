import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, after the partition (`L41ca`, `L41d3`, `L41f7`)
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
theorem tlC_z64 (a b : BitVec 64) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat = b.toNat) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result_sub]
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h, this]

theorem blk_L41ca (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41ca" := by
  cfg_block
  measure_hb "L41ca"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, -⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L41ca] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    · rename_i e c; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4200 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, trivial⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L4200, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV]; omega
    · rename_i e c; subst e
      refine ⟨(tab_L41d3 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, trivial⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L41d3, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        exact Nat.le_refl _

theorem blk_L41d3 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41d3" := by
  cfg_block
  measure_hb "L41d3"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, -⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L41d3] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    simp only at hWc
    have hPD' := hPD
    unfold PDone at hPD'
    have tsi : (s₀.regs.get64 .rsi).toNat = (pA t₀).toNat + 2 * lo := by
      rw [hsi]; exact tn_add _ _ (by omega)
    have tdx : (s₀.regs.get64 .rdx).toNat = (pA t₀).toNat + 2 * hi1 - 2 := by
      rw [hdx]; exact tn_hi _ _ (by omega) (by omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    rename_i e; subst e
    refine ⟨(tab_L41e0 _ _ _ _ _).2 ?_, ?_⟩
    · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP,
        ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, hPD, ?_, ?_, lo, Nat.le_refl _, by omega, ?_,
          fun q a b => absurd b (by omega)⟩, hmT.get⟩
      · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact h10
      · regs_simp; exact h9
      · regs_simp; exact hsi
    · rw [var_L41e0, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
      simp only [QV, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      rw [tdx, tsi]
      omega

theorem blk_L41f7 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41f7" := by
  cfg_block
  measure_hb "L41f7"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, m, hm1, hm2,
      hdi, hsrt⟩, hm⟩, hn⟩ := hs₀
    rw [var_L41f7] at hn
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
    have hPD' := hPD
    unfold PDone at hPD'
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have tdi : (s₀.regs.get64 .rdi).toNat = (pA t₀).toNat + 2 * m := by
      rw [hdi]; exact tn_add _ _ (by omega)
    have tdx : (s₀.regs.get64 .rdx).toNat = (pA t₀).toNat + 2 * hi1 - 2 := by
      rw [hdx]; exact tn_hi _ _ (by omega) (by omega)
    have hDrop : m = hi1 - 1 → QI (NN x) (AV fl) (A0 x) S ∧ stkPhi s₀ S.length = phi S :=
      fun h => by
        have hd := qi_drop (S := S) (I := (lo, hi1)) hQI (fun q a b => hsrt q a (by
          simp only at b; omega))
        exact ⟨hd, stkPhi_S hm hl2 hbp hR.1 hSR hd (by omega)⟩
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    · -- the interval is in order: drop it
      rename_i e c; subst e
      rw [tlC_z64, tdi, tdx] at c
      simp only [decide_eq_true_eq] at c
      obtain ⟨hd, hpS⟩ := hDrop (by omega)
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4060 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · exact ⟨hR, S, hcx, hD, fl, stk, pb, hL, hP, ⟨hSR, hd⟩, hmT.get⟩
      · rw [var_L4060, stkPhi_mk _ _ _ _ rfl]
        dsimp only [rN]
        rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hpS, hphi, phi_append, phi_one]
        unfold wt; simp only [QV]; omega
    · -- to the push
      rename_i e c; subst e
      refine ⟨(tab_L4200 _ _ _ _ _).2 ?_, ?_⟩
      · exact ⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, trivial⟩,
          hmT.get⟩
      · rw [var_L4200, phiC_mk _ _ _ _ rfl rfl rfl rfl]
        simp only [QV]; omega

end Kraken.Examples.Sbr.Tlim

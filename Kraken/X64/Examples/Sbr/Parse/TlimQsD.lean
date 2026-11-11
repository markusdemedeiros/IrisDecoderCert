import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the median of three (`L40e0`, `L40ec`, `L40f0`)
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

theorem blk_L40e0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40e0" := by
  cfg_block
  measure_hb "L40e0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, hMed, hle⟩, hm⟩, hn⟩ := hs₀
    rw [var_L40e0] at hn
    subst hn
    obtain ⟨hcx, hD, -, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨h2, hdi, hr8, hr10, -, hr9⟩ := id hMed
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hvl := hv lo (by omega)
    have hvm := hv (mid lo (hi1 - 1)) (by unfold mid; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    · -- `A lo ≤ A mid`: to L40f7
      rename_i e c; subst e
      rw [hr10, hr9, sw64_16, sw64_16, cc16_le _ _ hvl hvm] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L40f7 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hCur.2.2.1, ?_, ?_, hQI⟩,
          ⟨h2, ?_, ?_⟩, c, hle⟩, hmT.get⟩
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hdi
        · regs_simp; exact hr8
      · rw [var_L40f7, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · -- `A mid < A lo`: falls into L40ec
      rename_i e c; subst e
      rw [hr10, hr9, sw64_16, sw64_16, cc16_le _ _ hvl hvm] at c
      simp only [decide_eq_false_iff_not] at c
      rw [tab_L40ec, var_L40ec, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
      refine ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hCur.2.2.1, ?_, ?_, hQI⟩,
          ⟨h2, ?_, ?_⟩, ?_, ?_, Or.inl ⟨Nat.lt_of_not_le c, hle⟩⟩, hmT.get⟩, Nat.le_refl _⟩
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hdi
      · regs_simp; exact hr8
      · regs_simp; exact hr10
      · regs_simp; exact hr9

theorem blk_L40ec (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40ec" := by
  cfg_block
  measure_hb "L40ec"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨h2, hdi, hr8⟩, hr10, hr9, hor⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L40ec] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hN := NN_le hR.1
    have hpn := pA_nat hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hvl := hv lo (by omega)
    have hmd : mid lo (hi1 - 1) < 30 := by unfold mid; omega
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hm' : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rdi) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl (mid lo (hi1 - 1)) v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 _ hmd hdi v
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (v : Int), R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = s₀.regs.get64 .rcx → R.get64 .rsi = s₀.regs.get64 .rsi →
        R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := s₀.dmem.storeInt (s₀.regs.get64 .rdi) 2 v } = phi (S ++ [(lo, hi1)]) :=
        fun R zm sf v e2 e3 e4 e5 => by
      have h := hm' v
      exact phiC_eq h hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rdi) 2).isSome = true := by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hdi (by simp only; omega)
        (by simp only; omega)]
      rfl
    have hmT' : Box _ := ⟨hm'⟩
    clear hm hm'
    vcgen
    all_goals try call_simp
    all_goals simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld
    · (have e : s₀ = _ := ‹s₀ = _›; subst e)
      rw [tab_L40f0, var_L40f0, hphi' _ _ _ _ rfl rfl rfl rfl]
      refine ⟨⟨hR, S, lo, hi1, AV fl, mid lo (hi1 - 1),
        setW2 fl (mid lo (hi1 - 1)) (BitVec.setWidth 16 (s₀.regs.get64 .r10)).toInt, stk, pb,
        Lens_set hL _ hmd _, hP, ?_, ?_⟩, by (try rw [hphi]); simp only [QV]; omega⟩
      rotate_left
      · exact hmT'.get _
      refine ⟨hSR, hCur, h2, Or.inl rfl, ?_, hr9, hdi, ?_, fun _ => hor, fun h => ?_⟩
      · intro q; rw [hr10]; exact AV_set hl1 _ hmd _ (by omega) q
      · rw [hr8, show hi1 - 1 - 1 = hi1 - 2 by omega]
      · exact absurd h (show ¬(mid lo (hi1 - 1) = hi1 - 1) by unfold mid; omega)

theorem blk_L40f0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40f0" := by
  cfg_block
  measure_hb "L40f0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, A, pos, fl, stk, pb, hL, hP, ⟨hSR, hCur, h2, hpos, hA, hr9, hdi, hr8,
      hpm, hpe⟩, hm⟩, hn⟩ := hs₀
    rw [var_L40f0] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hN := NN_le hR.1
    have hpn := pA_nat hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hmd : mid lo (hi1 - 1) < hi1 - 1 := by unfold mid; omega
    have hpl : pos < hi1 := by omega
    have hvp := hv pos (by omega)
    have hQI2 := qi_swap hQI (i := lo) (j := pos) ⟨Nat.le_refl _, by simp only; omega⟩
      ⟨by simp only; unfold mid at hpos; omega, hpl⟩
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (v : Int), R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = s₀.regs.get64 .rcx → R.get64 .rsi = s₀.regs.get64 .rsi →
        R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2 v } = phi (S ++ [(lo, hi1)]) :=
        fun R zm sf v e2 e3 e4 e5 => by
      have h := st_fl hm hl1 lo (by omega) hsi v
      exact phiC_eq h hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsi) 2).isSome = true := by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hsi (by simp only; omega)
        (by simp only; omega)]
      rfl
    have hA2 : ∀ q, AV (setW2 fl lo (BitVec.setWidth 16 (BitVec.ofNat 64 (A pos))).toInt) q
        = swap A lo pos q := fun q => by
      rw [AV_set hl1 lo (by omega) _ (by omega) q]
      exact upd_swap_of hA q
    have hm' : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rsi) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl lo v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 lo (by omega) hsi v
    have hmT' : Box _ := ⟨hm'⟩
    clear hm hm'
    vcgen
    all_goals try call_simp
    all_goals simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld
    · (have e : s₀ = _ := ‹s₀ = _›; subst e)
      rw [tab_L40f7, var_L40f7, hphi' _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
        (by regs_simp)]
      rw [hr9]
      refine ⟨⟨by simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR,
        S, lo, hi1, _, stk, pb, Lens_set hL lo (by omega) _, hP,
        ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, qi_congr hQI2 hA2⟩, ⟨h2, ?_, ?_⟩, ?_, ?_⟩, hmT'.get _⟩,
        by (try rw [hphi]); simp only [QV]; omega⟩
      · regs_simp; exact hcx
      · regs_simp; exact hsi
      · regs_simp; exact hdx
      · regs_simp; exact hdi
      · regs_simp; rw [hr8, show hi1 - 2 = hi1 - 1 - 1 by omega]
      · have e1 : AV (setW2 fl lo (BitVec.setWidth 16 (BitVec.ofNat 64 (A pos))).toInt) lo = swap A lo pos lo := hA2 lo
        have e2 : AV (setW2 fl lo (BitVec.setWidth 16 (BitVec.ofNat 64 (A pos))).toInt) (mid lo (hi1 - 1)) = swap A lo pos (mid lo (hi1 - 1)) := hA2 _
        rw [e1, e2]
        rcases hpos with hp | hp
        · obtain ⟨c1, c2⟩ | ⟨c1, c2⟩ := hpm hp <;> subst hp <;>
            simp only [swap_eq, ↓reduceIte, show mid lo (hi1 - 1) ≠ lo by unfold mid; omega] <;> omega
        · obtain ⟨c1, c2⟩ := hpe hp; subst hp
          simp only [swap_eq, ↓reduceIte, show mid lo (hi1 - 1) ≠ lo by unfold mid; omega,
            show mid lo (hi1 - 1) ≠ hi1 - 1 by unfold mid; omega]; omega
      · have e1 : AV (setW2 fl lo (BitVec.setWidth 16 (BitVec.ofNat 64 (A pos))).toInt) lo = swap A lo pos lo := hA2 lo
        have e2 : AV (setW2 fl lo (BitVec.setWidth 16 (BitVec.ofNat 64 (A pos))).toInt) (hi1 - 1) = swap A lo pos (hi1 - 1) := hA2 _
        rw [e1, e2]
        rcases hpos with hp | hp
        · obtain ⟨c1, c2⟩ | ⟨c1, c2⟩ := hpm hp <;> subst hp <;>
            simp only [swap_eq, ↓reduceIte, show hi1 - 1 ≠ lo by omega,
              show hi1 - 1 ≠ mid lo (hi1 - 1) by unfold mid; omega] <;> omega
        · obtain ⟨c1, c2⟩ := hpe hp; subst hp
          simp only [swap_eq, ↓reduceIte, show hi1 - 1 ≠ lo by omega]; omega

end Kraken.Examples.Sbr.Tlim

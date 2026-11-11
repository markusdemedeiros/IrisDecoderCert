import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the median of three (`L40c3`, `L40c9`)
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

theorem blk_L40c3 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40c3" := by
  cfg_block
  measure_hb "L40c3"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, hMed, hlt⟩, hm⟩, hn⟩ := hs₀
    rw [var_L40c3] at hn
    subst hn
    obtain ⟨-, hD, -, -, -, hQI⟩ := id hCur
    obtain ⟨h2, -, -, hr10, hr11, hr9⟩ := id hMed
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    simp only at hWc
    have hv := qi_lt hR.1 hQI
    have hve := hv (hi1 - 1) (by omega)
    have hvm := hv (mid lo (hi1 - 1)) (by unfold mid; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    · -- `A mid < A e`: to L40ec
      rename_i e c; subst e
      rw [hr11, hr9, sw64_16, sw64_16, cc16_g _ _ hve hvm] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L40ec _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · exact ⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, ⟨h2, hMed.2.1, hMed.2.2.1⟩, hr10,
          hr9, Or.inr ⟨c, hlt⟩⟩, hmT.get⟩
      · rw [var_L40ec, phiC_mk _ _ _ _ rfl rfl rfl rfl]
    · -- `A e ≤ A mid`: falls into L40c9
      rename_i e c; subst e
      rw [hr11, hr9, sw64_16, sw64_16, cc16_g _ _ hve hvm] at c
      simp only [decide_eq_false_iff_not] at c
      rw [tab_L40c9, var_L40c9, phiC_mk _ _ _ _ rfl rfl rfl rfl]
      exact ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, hMed, hlt, Nat.le_of_not_lt c⟩, hmT.get⟩,
        Nat.le_refl _⟩

theorem blk_L40c9 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L40c9" := by
  cfg_block
  measure_hb "L40c9"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, hMed, hlt, hle⟩, hm⟩, hn⟩ := hs₀
    rw [var_L40c9] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨h2, hdi, hr8, hr10, hr11, hr9⟩ := id hMed
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
    have hve := hv (hi1 - 1) (by omega)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hm' : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl (hi1 - 1) v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 (hi1 - 1) (by omega) (by rw [hdx]; exact hi_addr _ _ (by omega)) v
    have hphi' : ∀ (s : MachineData) v, s.dmem = s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v →
        s.regs.get64 .rbp = s₀.regs.get64 .rbp → s.regs.get64 .rcx = s₀.regs.get64 .rcx →
        s.regs.get64 .rsi = s₀.regs.get64 .rsi → s.regs.get64 .rdx = s₀.regs.get64 .rdx →
        phiC s = phi (S ++ [(lo, hi1)]) := fun s v e1 e2 e3 e4 e5 => by
      have h := hm' v
      rw [← e1] at h
      exact phiC_eq h hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2).isSome = true := by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) (hi1 - 1)
        (by rw [hdx]; exact hi_addr _ _ (by omega)) (by simp only; omega) (by simp only; omega)]
      rfl
    have hmT : Box _ := ⟨hm⟩
    have hmT' : Box _ := ⟨hm'⟩
    clear hm hm'
    vcgen
    all_goals try call_simp
    all_goals simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat] at *
    · rename_i e; subst e; exact hld
    · rename_i e; subst e
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L40f0 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨by simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR,
          S, lo, hi1, AV fl, hi1 - 1,
          setW2 fl (hi1 - 1) (BitVec.setWidth 16 (s₀.regs.get64 .r10)).toInt, stk, pb,
          Lens_set hL _ (by omega) _, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩, by omega, Or.inr rfl,
          ?_, ?_, ?_, ?_, fun h => absurd h (by unfold mid; omega), fun _ => ⟨hlt, hle⟩⟩,
          hmT'.get _⟩
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · intro q; rw [hr10]; exact AV_set hl1 _ (by omega) _ (by omega) q
        · regs_simp; rw [hr11]; exact zx32_64 _ (by omega)
        · regs_simp; exact hdi
        · regs_simp; rw [hr8, show hi1 - 1 - 1 = hi1 - 2 by omega]
      · rw [var_L40f0, hphi' _ _ rfl (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp), hphi]

end Kraken.Examples.Sbr.Tlim

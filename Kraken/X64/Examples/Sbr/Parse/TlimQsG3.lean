import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the left scan (`L4170`)
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

theorem blk_L4170 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4170" := by
  cfg_block
  measure_hb "L4170"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl, h15⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L4170] at hn
    subst hn
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hv := qi_lt hR.1 hCur.2.2.2.2.2
    have hI := hPI
    unfold PInv at hI
    have hvp : pv < 2 ^ 15 := by rw [← hI.2.2.2.2.1]; exact hv _ (by omega)
    have hva : u16 fl l < 2 ^ 15 := hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r10) 2 = some (u16 fl l : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.1 (by simp only; omega)
        (by simp only; omega)
    have t10 : (s₀.regs.get64 .r10).toNat = (pA t₀).toNat + 2 * l := by
      rw [hPR.1]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * rt := by
      rw [hPR.2.1]; exact tn_add _ _ (by omega)
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := hI
    have e10 : BitVec.setWidth 64 2#64 + s₀.regs.get64 .r10 = pA t₀ + v64 (2 * (l + 1)) := by
      rw [hPR.1, show BitVec.setWidth 64 2#64 = 2#64 from rfl, BitVec.add_comm, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
    have t10' : (pA t₀ + v64 (2 * (l + 1))).toNat = (pA t₀).toNat + 2 * (l + 1) :=
      tn_add _ _ (by omega)
    have hext : u16 fl l < pv → PInv (AV fl) lo (hi1 - 1) (l + 1) rt pv := fun h =>
      ⟨by omega, by omega, i3, by omega, i5, fun q h1 h2 => by
        by_cases e : q = l
        · subst e; exact Nat.le_of_lt h
        · exact i6 q h1 (by omega), i7⟩
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · -- `pv ≤ A left`: to L4194
      rename_i e v ll c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [h15, sw64_16, ofInt16_nat, cc16_ge _ _ hva hvp] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4194 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1, hCur.2.2.1,
          ?_, ?_, hCur.2.2.2.2.2⟩, hPI, ⟨?_, ?_, ?_⟩, by omega, fun _ => c, ?_⟩, hmT.get⟩
        · exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · regs_simp; exact h15
      · rw [var_L4194, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, lle, rN]
        rw [t10, t9]
        split <;> omega
    · -- `A left < pv`, `left + 1 ≤ right`: back to L4170
      rename_i e v ll c c2; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [h15, sw64_16, ofInt16_nat, cc16_ge _ _ hva hvp] at c
      simp only [decide_eq_false_iff_not] at c
      simp only [Int64.toBitVec_ofNat_norm] at c2
      rw [CondCode.interp_be_sub _ _ _ rfl, e10, t10', t9] at c2
      simp only [decide_eq_true_eq] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4170 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l + 1, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1,
          hCur.2.2.1, ?_, ?_, hCur.2.2.2.2.2⟩, hext (by omega), ⟨?_, ?_, ?_⟩, by omega, ?_⟩,
          hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact e10
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · regs_simp; exact h15
      · rw [var_L4170, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [e10, t10', t9, t10]
        omega
    · -- `A left < pv`, `right < left + 1`: to L4194
      rename_i e v ll c c2; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [h15, sw64_16, ofInt16_nat, cc16_ge _ _ hva hvp] at c
      simp only [decide_eq_false_iff_not] at c
      simp only [Int64.toBitVec_ofNat_norm] at c2
      rw [CondCode.interp_be_sub _ _ _ rfl, e10, t10', t9] at c2
      simp only [decide_eq_false_iff_not] at c2
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4194 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l + 1, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1,
          hCur.2.2.1, ?_, ?_, hCur.2.2.2.2.2⟩, hext (by omega), ⟨?_, ?_, ?_⟩, by omega,
          fun h => absurd h (by omega), ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact e10
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · regs_simp; exact h15
      · rw [var_L4194, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, lle, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [e10, t10', t9, t10]
        split <;> omega

end Kraken.Examples.Sbr.Tlim

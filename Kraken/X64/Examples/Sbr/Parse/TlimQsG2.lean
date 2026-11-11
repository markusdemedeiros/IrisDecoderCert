import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the partition loads (`L4169`, `L41b0`, `L4199`)
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

theorem blk_L4169 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4169" := by
  cfg_block
  measure_hb "L4169"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4169] at hn
    subst hn
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hv := qi_lt hR.1 hCur.2.2.2.2.2
    have hI := hPI
    unfold PInv at hI
    have hvp : pv < 2 ^ 15 := by rw [← hI.2.2.2.2.1]; exact hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r8) 2 = some (u16 fl (hi1 - 1 - 1) : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.2.2 (by simp only; omega)
        (by simp only; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · rename_i e v ll; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      have hu : u16 fl (hi1 - 1 - 1) = pv := hI.2.2.2.2.1
      refine ⟨(tab_L4170 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1, hCur.2.2.1,
          ?_, ?_, hCur.2.2.2.2.2⟩, hPI, ⟨?_, ?_, ?_⟩, hl, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · rw [← hu]; regs_simp; exact zx16' _ (by omega)
      · rw [var_L4170, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact Nat.le_refl _


theorem blk_L41b0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41b0" := by
  cfg_block
  measure_hb "L41b0"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L41b0] at hn
    subst hn
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hv := qi_lt hR.1 hCur.2.2.2.2.2
    have hI := hPI
    unfold PInv at hI
    have hvp : pv < 2 ^ 15 := by rw [← hI.2.2.2.2.1]; exact hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r8) 2 = some (u16 fl (hi1 - 1 - 1) : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.2.2 (by simp only; omega)
        (by simp only; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · rename_i e v ll; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      have hu : u16 fl (hi1 - 1 - 1) = pv := hI.2.2.2.2.1
      refine ⟨(tab_L41b4 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1, hCur.2.2.1,
          ?_, ?_, hCur.2.2.2.2.2⟩, hPI, ⟨?_, ?_, ?_⟩, hl, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · rw [← hu]; regs_simp; exact zx16' _ (by omega)
      · rw [var_L41b4, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV]
        exact Nat.le_refl _


theorem blk_L4199 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4199" := by
  cfg_block
  measure_hb "L4199"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl, hpl, h15⟩,
      hm⟩,
      hn⟩ := hs₀
    rw [var_L4199] at hn
    subst hn
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hN := NN_le hR.1
    have hWc := qi_cur hCur.2.2.2.2.2
    simp only at hWc
    have hv := qi_lt hR.1 hCur.2.2.2.2.2
    have hI := hPI
    unfold PInv at hI
    have hvp : pv < 2 ^ 15 := by rw [← hI.2.2.2.2.1]; exact hv _ (by omega)
    have hvr : u16 fl rt < 2 ^ 15 := hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r9) 2 = some (u16 fl rt : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.2.1 (by simp only; omega)
        (by simp only; omega)
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · -- `pv < A right`: to L4190
      rename_i e v ll c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [sw16', h15, sw64_16, cc16_g _ _ hvr hvp] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4190 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1, hCur.2.2.1,
          ?_, ?_, hCur.2.2.2.2.2⟩, hPI, ⟨?_, ?_, ?_⟩, hl, hpl, c, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · regs_simp; exact h15
      · rw [var_L4190, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
    · -- `A right ≤ pv`: to L4150
      rename_i e v ll c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      rw [sw16', h15, sw64_16, cc16_g _ _ hvr hvp] at c
      simp only [decide_eq_false_iff_not] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4150 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hCur.2.1, hCur.2.2.1,
          ?_, ?_, hCur.2.2.2.2.2⟩, hPI, ⟨?_, ?_, ?_⟩, hl, hpl, Nat.le_of_not_lt c, ?_⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hCur.1
        · regs_simp; exact hCur.2.2.2.1
        · regs_simp; exact hCur.2.2.2.2.1
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
        · regs_simp; exact hPR.2.2
        · regs_simp; exact zx16' _ (by omega)
      · rw [var_L4150, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp)]
        simp only [QV, dP, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega

end Kraken.Examples.Sbr.Tlim

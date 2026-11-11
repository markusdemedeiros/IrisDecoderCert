import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the pivot placed at `left` (`L41b4`)
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
/-- Exchanging the pivot slot `e - 1` with `left` ends the partition. -/
theorem tlC_pdone {A : Nat → Nat} {lo e l rt pv : Nat} (h : PInv A lo e l rt pv) (hl : rt < l) :
    PDone (swap A (e - 1) l) lo e l rt := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h
  have hBl : swap A (e - 1) l l = pv := by
    by_cases c : l = e - 1
    · simp only [swap_eq, c, ↓reduceIte]; exact i5
    · simp only [swap_eq, c, ↓reduceIte]; exact i5
  refine ⟨i1, i2, hl, i4, fun q a b => ?_, fun q a b => ?_⟩
  · rw [hBl]
    by_cases c : q = l
    · subst c; rw [hBl]; exact Nat.le_refl _
    · simp only [swap_eq, show q ≠ e - 1 by omega, c, ↓reduceIte]; exact i6 q a (by omega)
  · rw [hBl]
    by_cases c1 : q = e - 1
    · simp only [swap_eq, c1, ↓reduceIte]; exact i7 l hl (by omega)
    · by_cases c2 : q = l
      · subst c2; rw [hBl]; exact Nat.le_refl _
      · simp only [swap_eq, c1, c2, ↓reduceIte]; exact i7 q a b

theorem blk_L41b4 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L41b4" := by
  cfg_block
  measure_hb "L41b4"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl, h15⟩,
      hm⟩, hn⟩ := hs₀
    rw [var_L41b4] at hn
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
    have hI := hPI
    unfold PInv at hI
    have hva : u16 fl l < 2 ^ 15 := hv _ (by omega)
    have hvp : pv < 2 ^ 15 := by rw [← hI.2.2.2.2.1]; exact hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r10) 2 = some (u16 fl l : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.1 (by simp only; omega)
        (by simp only; omega)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hlen1 : ∀ v, (setW2 fl l v).length = 60 := fun v => by
      rw [setW2_length _ _ _ (by omega)]; exact hl1
    have hm1 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .r10) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl l v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 l (by omega) hPR.1 v
    have hld3 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .r10) 2 v).loadInt
        (s₀.regs.get64 .r8) 2).isSome = true := fun v => by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) (hm1 v)) (hi1 - 1 - 1) hPR.2.2
        (by simp only [hlen1]; omega) (by simp only [hlen1]; omega)]
      rfl
    have hm2 : ∀ v1 v2, (s₀.dmem.storeInt (s₀.regs.get64 .r10) 2 v1).storeInt
        (s₀.regs.get64 .r8) 2 v2
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 fl l v1) (hi1 - 1 - 1) v2, x.a.nlim, stk, pb⟩ :=
      fun v1 v2 => st_fl (hm1 v1) (hlen1 v1) (hi1 - 1 - 1) (by omega) hPR.2.2 v2
    have hphi2 : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (v1 v2 : Int),
        R.get64 .rbp = s₀.regs.get64 .rbp → R.get64 .rcx = s₀.regs.get64 .rcx →
        R.get64 .rsi = s₀.regs.get64 .rsi → R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := (s₀.dmem.storeInt (s₀.regs.get64 .r10) 2 v1).storeInt
                  (s₀.regs.get64 .r8) 2 v2 } = phi (S ++ [(lo, hi1)]) :=
      fun R zm sf v1 v2 e2 e3 e4 e5 =>
        phiC_eq (hm2 v1 v2) hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega)
          (e4.trans hsi) (e5.trans hdx)
    have hI5 : AV fl (hi1 - 1 - 1) = pv := hI.2.2.2.2.1
    have hB1 : ∀ q, AV (setW2 fl l (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt) q
        = Qsort.upd (AV fl) l (AV fl (hi1 - 1 - 1)) q := fun q => by
      rw [h15, AV_set hl1 l (by omega) pv (by omega) q, hI5]
    have hB : ∀ q, AV (setW2 (setW2 fl l (BitVec.setWidth 16 (s₀.regs.get64 .r15)).toInt)
        (hi1 - 1 - 1) (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 16 (u16 fl l : Int))))).toInt) q = swap (AV fl) (hi1 - 1 - 1) l q :=
      fun q => by
        rw [zx16' _ (by omega), AV_set (hlen1 _) (hi1 - 1 - 1) (by omega) (u16 fl l) (by omega) q]
        exact upd_swap_of hB1 q
    have eB := funext hB
    have hPD := tlC_pdone hPI hl
    rw [← eB] at hPD
    have hQI2 := qi_swap hQI (i := hi1 - 1 - 1) (j := l) ⟨by simp only; omega, by simp only; omega⟩
      ⟨by simp only; omega, by simp only; omega⟩
    rw [← eB] at hQI2
    have hmT : Box _ := ⟨hm2⟩
    clear hm hm1 hm2 eB hB hB1
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld3 _
    · -- to L4200
      rename_i e v ll _ _; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4200 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, _, stk, pb,
          Lens_set (Lens_set hL l (by omega) _) (hi1 - 1 - 1) (by omega) _, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI2⟩, hPD, ?_, ?_, trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
      · rw [var_L4200, hphi2 _ _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp), ← hphi]
        simp only [QV]; omega
    · -- to L41d3
      rename_i e v ll _ _ _; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L41d3 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨?_, S, lo, hi1, l, rt, _, stk, pb,
          Lens_set (Lens_set hL l (by omega) _) (hi1 - 1 - 1) (by omega) _, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI2⟩, hPD, ?_, ?_, trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
      · rw [var_L41d3, hphi2 _ _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp), ← hphi]
    · -- falls into L41ca
      rename_i e v ll _ _ _; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      refine ⟨(tab_L41ca _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, _, stk, pb,
          Lens_set (Lens_set hL l (by omega) _) (hi1 - 1 - 1) (by omega) _, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI2⟩, hPD, ?_, ?_, trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact hPR.1
        · regs_simp; exact hPR.2.1
      · rw [var_L41ca, hphi2 _ _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp), ← hphi]
        exact Nat.le_refl _

end Kraken.Examples.Sbr.Tlim

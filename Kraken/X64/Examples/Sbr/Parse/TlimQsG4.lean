import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the partition exchange (`L4150`)
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
/-- The exchange of `left` and `right` keeps the partition invariant, one step inward. -/
theorem tlC_pinv_swap {A : Nat → Nat} {lo e l rt pv : Nat} (h : PInv A lo e l rt pv)
    (hl : l ≤ rt) (h1 : pv ≤ A l) (h2 : A rt ≤ pv) :
    PInv (swap A l rt) lo e (l + 1) (rt - 1) pv := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := h
  refine ⟨by omega, by omega, by omega, by omega, ?_, fun q a b => ?_, fun q a b => ?_⟩
  · simp only [swap_eq, show e - 1 ≠ l by omega, show e - 1 ≠ rt by omega, ↓reduceIte]; exact i5
  · by_cases c1 : q = l
    · simp only [swap_eq, c1, ↓reduceIte]; exact h2
    · simp only [swap_eq, c1, show q ≠ rt by omega, ↓reduceIte]; exact i6 q a (by omega)
  · by_cases c1 : q = l
    · simp only [swap_eq, c1, ↓reduceIte]; rw [show rt = l by omega]; exact h1
    · by_cases c2 : q = rt
      · subst c2; simp only [swap_eq, c1, ↓reduceIte]; exact h1
      · simp only [swap_eq, c1, c2, ↓reduceIte]; exact i7 q (by omega) b

omit [CodeEnv] in
/-- `right - 1` as an address. -/
theorem tlC_sub2 (P : BitVec 64) (r : Nat) (h : 1 ≤ r) :
    BitVec.setWidth 64 (-2 : Int64).toBitVec + (P + BitVec.ofNat 64 (2 * r))
      = P + BitVec.ofNat 64 (2 * (r - 1)) := by
  have c : (BitVec.setWidth 64 (-2 : Int64).toBitVec).toNat = 2 ^ 64 - 2 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, c, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem blk_L4150 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4150" := by
  cfg_block
  measure_hb "L4150"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, pv, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPI, hPR, hl, hpl, hpr,
      h12⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4150] at hn
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
    have hvr : u16 fl rt < 2 ^ 15 := hv _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .r10) 2 = some (u16 fl l : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.1 (by simp only; omega)
        (by simp only; omega)
    have L2 : s₀.dmem.loadInt (s₀.regs.get64 .r9) 2 = some (u16 fl rt : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hPR.2.1 (by simp only; omega)
        (by simp only; omega)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hlen1 : ∀ v, (setW2 fl rt v).length = 60 := fun v => by
      rw [setW2_length _ _ _ (by omega)]; exact hl1
    have hm1 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl rt v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 rt (by omega) hPR.2.1 v
    have hld3 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 v).loadInt
        (s₀.regs.get64 .r10) 2).isSome = true := fun v => by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) (hm1 v)) l hPR.1 (by simp only [hlen1]; omega)
        (by simp only [hlen1]; omega)]
      rfl
    have hm2 : ∀ v1 v2, (s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 v1).storeInt
        (s₀.regs.get64 .r10) 2 v2
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 fl rt v1) l v2, x.a.nlim, stk, pb⟩ := fun v1 v2 =>
      st_fl (hm1 v1) (hlen1 v1) l (by omega) hPR.1 v2
    have hphi2 : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (v1 v2 : Int),
        R.get64 .rbp = s₀.regs.get64 .rbp → R.get64 .rcx = s₀.regs.get64 .rcx →
        R.get64 .rsi = s₀.regs.get64 .rsi → R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
                dmem := (s₀.dmem.storeInt (s₀.regs.get64 .r9) 2 v1).storeInt
                  (s₀.regs.get64 .r10) 2 v2 } = phi (S ++ [(lo, hi1)]) :=
      fun R zm sf v1 v2 e2 e3 e4 e5 =>
      phiC_eq (hm2 v1 v2) hl2 (e2.trans hbp) hR.1 hSR hQI (e3.trans hcx) (by omega) (e4.trans hsi)
        (e5.trans hdx)
    have hB1 : ∀ q, AV (setW2 fl rt (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofInt 16 (u16 fl l : Int))))).toInt) q = Qsort.upd (AV fl) rt (AV fl l) q :=
        fun q => by
      rw [zx16' _ (by omega)]; exact AV_set hl1 rt (by omega) _ (by omega) q
    have hB : ∀ q, AV (setW2 (setW2 fl rt (BitVec.setWidth 16 (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofInt 16 (u16 fl l : Int))))).toInt) l
          (BitVec.setWidth 16 (s₀.regs.get64 .r12)).toInt) q
        = swap (AV fl) l rt q := fun q => by
      rw [h12, AV_set (hlen1 _) l (by omega) _ (Nat.lt_trans hvr (by decide)) q]
      exact upd_swap_of hB1 q
    have eB := funext hB
    have hPI2 := tlC_pinv_swap hPI hl hpl hpr
    rw [← eB] at hPI2
    have hQI2 := qi_swap hQI (i := l) (j := rt) ⟨by simp only; omega, by simp only; omega⟩
      ⟨by simp only; omega, by simp only; omega⟩
    rw [← eB] at hQI2
    have t10 : (s₀.regs.get64 .r10).toNat = (pA t₀).toNat + 2 * l := by
      rw [hPR.1]; exact tn_add _ _ (by omega)
    have t9 : (s₀.regs.get64 .r9).toNat = (pA t₀).toNat + 2 * rt := by
      rw [hPR.2.1]; exact tn_add _ _ (by omega)
    have e10 : BitVec.setWidth 64 2#64 + s₀.regs.get64 .r10 = pA t₀ + v64 (2 * (l + 1)) := by
      rw [hPR.1, show BitVec.setWidth 64 2#64 = 2#64 from rfl, BitVec.add_comm, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
    have e9 : BitVec.setWidth 64 (-2 : Int64).toBitVec + s₀.regs.get64 .r9
        = pA t₀ + v64 (2 * (rt - 1)) := by
      rw [hPR.2.1]; exact tlC_sub2 _ _ (by omega)
    have t10' : (pA t₀ + v64 (2 * (l + 1))).toNat = (pA t₀).toNat + 2 * (l + 1) :=
      tn_add _ _ (by omega)
    have t9' : (pA t₀ + v64 (2 * (rt - 1))).toNat = (pA t₀).toNat + 2 * (rt - 1) :=
      tn_add _ _ (by omega)
    have hmT : Box _ := ⟨hm2⟩
    clear hm hm1 hm2 eB hB hB1
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L2]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld3 _
    · rename_i e v ll; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll
      rw [L1] at ll; simp only [Option.some.injEq] at ll; subst ll
      refine ⟨(tab_L4164 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l + 1, rt - 1, pv, _, stk, pb,
          Lens_set (Lens_set hL rt (by omega) _) l (by omega) _, hP,
          ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI2⟩, hPI2, ⟨?_, ?_, ?_⟩, trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact e10
        · regs_simp; exact e9
        · regs_simp; exact hPR.2.2
      · rw [var_L4164, hphi2 _ _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp) (by regs_simp),
          ← hphi]
        simp only [QV, dP, lle, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [e10, e9, t10', t9', t10, t9]
        split <;> omega

end Kraken.Examples.Sbr.Tlim

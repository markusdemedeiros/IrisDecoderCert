import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, two elements (`L4280`)
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

theorem blk_L4280 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4280" := by
  cfg_block
  measure_hb "L4280"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, fl, stk, pb, hL, hP, ⟨hSR, hCur, h2⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4280] at hn
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
    have hva : u16 fl lo < 2 ^ 15 := hv _ (by omega)
    have hvb : u16 fl (hi1 - 1) < 2 ^ 15 := hv _ (by omega)
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have hrdx : s₀.regs.get64 .rdx = pA t₀ + v64 (2 * (hi1 - 1)) := by
      rw [hdx]; exact hi_addr _ _ (by omega)
    have L1 : s₀.dmem.loadInt (s₀.regs.get64 .rsi) 2 = some (u16 fl lo : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hsi (by simp only; omega)
        (by simp only; omega)
    have L2 : s₀.dmem.loadInt (s₀.regs.get64 .rdx) 2 = some (u16 fl (hi1 - 1) : Int) :=
      ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) hm) _ hrdx (by simp only; omega)
        (by simp only; omega)
    have hlen1 : ∀ v, (setW2 fl (hi1 - 1) v).length = 60 := fun v => by
      rw [setW2_length _ _ _ (by omega)]; exact hl1
    have hm1 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 fl (hi1 - 1) v, x.a.nlim, stk, pb⟩ := fun v =>
      st_fl hm hl1 (hi1 - 1) (by omega) hrdx v
    have hld5 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v).loadInt
        (s₀.regs.get64 .rsi) 2).isSome = true := fun v => by
      rw [ld16 (focus (T_fl k x ra t₀ (Saved t₀) _) (hm1 v)) lo hsi
        (by simp only [hlen1]; omega) (by simp only [hlen1]; omega)]
      rfl
    have hm2 : ∀ v1 v2, (s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v1).storeInt
        (s₀.regs.get64 .rsi) 2 v2
        =⋆ T k x ra t₀ (Saved t₀) ⟨setW2 (setW2 fl (hi1 - 1) v1) lo v2, x.a.nlim, stk, pb⟩ :=
      fun v1 v2 => st_fl (hm1 v1) (hlen1 v1) lo (by omega) hsi v2
    have hB1 : ∀ q, AV (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (v64 (u16 fl lo))).toInt) q
        = Qsort.upd (AV fl) (hi1 - 1) (AV fl lo) q := fun q =>
      AV_set hl1 (hi1 - 1) (by omega) _ (by omega) q
    have hB : ∀ q, AV (setW2 (setW2 fl (hi1 - 1) (BitVec.setWidth 16 (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofInt 16 (u16 fl lo : Int))))).toInt) lo
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 16 (u16 fl (hi1 - 1) : Int))))).toInt) q = swap (AV fl) lo (hi1 - 1) q :=
      fun q => by
        rw [zx16' (u16 fl lo) (by omega), zx16' (u16 fl (hi1 - 1)) (by omega),
          AV_set (hlen1 _) lo (by omega) (u16 fl (hi1 - 1)) (by omega) q]
        exact upd_swap_of hB1 q
    have eB := funext hB
    have hQIs := qi_swap hQI (i := lo) (j := hi1 - 1) ⟨by simp only; omega, by simp only; omega⟩
      ⟨by simp only; omega, by simp only; omega⟩
    rw [← eB] at hQIs
    have hd2 : u16 fl (hi1 - 1) < u16 fl lo → QI (NN x) (AV (setW2 (setW2 fl (hi1 - 1)
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 16 (u16 fl lo : Int))))).toInt) lo
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofInt 16 (u16 fl (hi1 - 1) : Int))))).toInt)) (A0 x) S := fun c =>
      qi_drop hQIs fun q a b => by
        simp only at a b
        obtain rfl : q = lo := by omega
        have e1 : q + 1 = hi1 - 1 := by omega
        rw [hB, hB, e1]
        simp only [swap_eq, ↓reduceIte, show hi1 - 1 ≠ q by omega]
        exact Nat.le_of_lt c
    have hd1 : u16 fl lo ≤ u16 fl (hi1 - 1) → QI (NN x) (AV fl) (A0 x) S := fun c =>
      qi_drop hQI fun q a b => by
        simp only at a b
        obtain rfl : q = lo := by omega
        rw [show q + 1 = hi1 - 1 by omega]; exact c
    have hpS2 : u16 fl (hi1 - 1) < u16 fl lo → ∀ (v1 v2 : Int) (s : MachineData),
        s.regs.get64 .rbp = s₀.regs.get64 .rbp →
        s.dmem = (s₀.dmem.storeInt (s₀.regs.get64 .rdx) 2 v1).storeInt (s₀.regs.get64 .rsi) 2 v2 →
        stkPhi s S.length = phi S :=
      fun c v1 v2 s e2 e3 =>
        stkPhi_S (by rw [e3]; exact hm2 v1 v2) hl2 (e2.trans hbp) hR.1 hSR (hd2 c) (by omega)
    have hpS1 : u16 fl lo ≤ u16 fl (hi1 - 1) → stkPhi s₀ S.length = phi S := fun c =>
      stkPhi_S hm hl2 hbp hR.1 hSR (hd1 c) (by omega)
    have hmT : Box _ := ⟨hm2⟩
    have hmT' : Box _ := ⟨hm⟩
    clear hm hm1 hm2 eB hB hB1
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L1]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L2]; rfl
    · -- in order: drop
      rename_i e v1 ll1 v2 ll2 c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll1 ll2
      rw [L1] at ll1; rw [L2] at ll2
      simp only [Option.some.injEq] at ll1 ll2; subst ll1 ll2
      rw [sw16', sw16', cc16_le _ _ hva hvb] at c
      simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4060 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, ?_, hD, fl, stk, pb, hL, hP, ⟨hSR, hd1 c⟩, hmT'.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
      · rw [var_L4060, stkPhi_mk _ _ _ _ (by regs_simp)]
        dsimp only [rN]
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hpS1 c, hphi, phi_append,
          phi_one]
        unfold wt; simp only [QV]; omega
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); rw [L2]; rfl
    · (have e : s₀ = _ := ‹s₀ = _›; subst e); exact hld5 _
    · -- exchange, then drop
      rename_i e v1 ll1 v2 ll2 c; subst e
      simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
        BitVec.ofNat_eq_ofNat] at ll1 ll2
      rw [L1] at ll1; rw [L2] at ll2
      simp only [Option.some.injEq] at ll1 ll2; subst ll1 ll2
      rw [sw16', sw16', cc16_le _ _ hva hvb] at c
      simp only [decide_eq_false_iff_not] at c
      have c' := Nat.lt_of_not_le c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4060 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S, ?_, hD, _, stk, pb,
          Lens_set (Lens_set hL (hi1 - 1) (by omega) _) lo (by omega) _, hP, ⟨hSR, hd2 c'⟩,
          hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
      · rw [var_L4060]
        dsimp only [rN]
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          hpS2 c' _ _ _ (by regs_simp) rfl, hphi, phi_append, phi_one]
        unfold wt; simp only [QV]; omega

end Kraken.Examples.Sbr.Tlim

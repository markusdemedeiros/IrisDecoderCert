import Kraken.X64.Examples.Sbr.Parse.TlimQsLib2

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the start (`L403f`) and the pushes (`L4200`..`L425a`)
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
theorem tlq_toInt64 (n : Nat) (h : n < 2 ^ 62) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_ofNat]; omega
  · simp [BitVec.msb_eq_decide]; omega

omit [CodeEnv] in
theorem tlq_ge64 (a b : Nat) (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (BitVec.ofNat 64 a - BitVec.ofNat 64 b)
      { cf := cf, af := af, of := (BitVec.ofNat 64 a - BitVec.ofNat 64 b).signed
          != (BitVec.ofNat 64 a).signed - (BitVec.ofNat 64 b).signed }) = decide (b ≤ a) := by
  rw [CondCode.interp_ge_cmp _ _ _ _ (by decide), BitVec.slt_eq_decide, tlq_toInt64 a ha,
    tlq_toInt64 b hb]
  by_cases h : a < b <;> simp [h] <;> omega

omit [CodeEnv] in
theorem tlq_sub (P : BitVec 64) (a b : Nat) (h : b ≤ a) (ha : P.toNat + a < 2 ^ 64) :
    P + BitVec.ofNat 64 a - (P + BitVec.ofNat 64 b) = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem tlq_push {p : BitVec 64} {stk : List UInt8} {S : List Iv} (h : StkRel p stk S)
    (hl : stk.length = 1024) (hS : S.length < 64) (I : Iv) (a b : BitVec 64)
    (ha : a = p + BitVec.ofNat 64 (2 * I.1)) (hb : b = p + BitVec.ofNat 64 (2 * I.2) - 2#64) :
    StkRel p (setW8 (setW8 stk (2 * S.length) a.toInt) (2 * S.length + 1) b.toInt) (S ++ [I]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hj
  have hl' : (setW8 stk (2 * S.length) a.toInt).length = 1024 := by
    rw [setW8_length _ _ _ (by omega)]; exact hl
  rw [w8_setW8 _ _ _ (by omega), w8_setW8 _ _ _ (by omega), w8_setW8 _ _ _ (by omega),
    w8_setW8 _ _ _ (by omega)]
  by_cases hj' : j < S.length
  · rw [List.getElem_append_left hj']
    have := h j hj'
    simp only [show 2 * j ≠ 2 * S.length + 1 by omega, show 2 * j ≠ 2 * S.length by omega,
      show 2 * j + 1 ≠ 2 * S.length + 1 by omega, show 2 * j + 1 ≠ 2 * S.length by omega,
      ↓reduceIte]
    exact this
  · obtain rfl : j = S.length := by omega
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero,
      show 2 * S.length ≠ 2 * S.length + 1 by omega, ↓reduceIte]
    exact ⟨ha, hb⟩

theorem blk_L403f (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L403f" := by
  cfg_block
  measure_hb "L403f"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hRg, hlb, h14, h15, fl, stk, pb, hL, hP, ⟨hAV, hw0⟩, hm⟩, hn⟩ := hs₀
    rw [var_L403f] at hn
    subst hn
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hRg.1.2.1
    have hpn := pA_nat hC
    have hN := NN_le hC
    have hN1 : 1 ≤ NN x := by
      have := hC.2.2.2.1; have : 0 < x.lb.toNat := by
        have h := hlb; rw [ne_eq, ← BitVec.toNat_inj] at h; simp at h; omega
      simp only [NN]; omega
    have hstk := focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have ha1 : s₀.regs.get64 .rbp + (-1080 : Int64).toBitVec
        = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * 1) := by
      rw [hbp, show (-1080 : Int64).toBitVec = 18446744073709550536#64 by decide]
      simp only [rS]; generalize t₀.regs.get64 .rsp = R; bv_omega
    have hs8 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + (-1080 : Int64).toBitVec) 8 v =⋆
        T k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, setW8 stk 1 v, pb⟩ := fun v =>
      focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, setW8 stk 1 v, pb⟩).symm
        (st64 hstk 1 ha1 (by simp only; omega) (by simp only; omega) v)
    have hSR : ∀ v : BitVec 64, v = pA t₀ + BitVec.ofNat 64 (2 * NN x) - 2#64 →
        StkRel (pA t₀) (setW8 stk 1 v.toInt) [(0, NN x)] := fun v hv j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero]
      refine ⟨?_, ?_⟩
      · rw [w8_setW8 _ _ _ (by omega)]; simp only [show (0:Nat) ≠ 1 by decide, ↓reduceIte, hw0]; simp
      · rw [w8_setW8 _ _ _ (by omega)]; simp only [↓reduceIte, hv]
    have hQI := qi_init (A0 x) (NN x)
    have hQI' : QI (NN x) (AV fl) (A0 x) [(0, NN x)] := qi_congr hQI hAV
    have hphi : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (v : BitVec 64),
        R.get64 .rbp = s₀.regs.get64 .rbp → v = pA t₀ + BitVec.ofNat 64 (2 * NN x) - 2#64 →
        stkPhi { regs := R, zmms := zm, status := sf,
                 dmem := s₀.dmem.storeInt (s₀.regs.get64 .rbp + (-1080 : Int64).toBitVec) 8 v.toInt } 1
          = phi [(0, NN x)] := fun R zm sf v e1 e2 => by
      have := stkPhi_eq (s := { regs := R, zmms := zm, status := sf,
                                dmem := s₀.dmem.storeInt (s₀.regs.get64 .rbp
                                  + (-1080 : Int64).toBitVec) 8 v.toInt })
        (hs8 _) (by simp only; rw [setW8_length _ _ _ (by omega)]; exact hl2) (e1.trans hbp)
        (p := pA t₀) (N := NN x) (by omega) (by omega) (hSR v e2) hQI'.2.2.1 (by simp)
      simpa using this
    have hst : BitVec.setWidth 64 (-2 : Int64).toBitVec + (s₀.regs.get64 .r14
        + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r15)) * 2#64)
        = pA t₀ + BitVec.ofNat 64 (2 * NN x) - 2#64 := by
      rw [h14, h15, zx32_64 _ (by omega)]
      have c : BitVec.setWidth 64 (-2 : Int64).toBitVec = 18446744073709551614#64 := by decide
      have m : BitVec.ofNat 64 (NN x) * 2#64 = BitVec.ofNat 64 (2 * NN x) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
      rw [c, m]
      generalize pA t₀ = P
      generalize BitVec.ofNat 64 (2 * NN x) = Q
      bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + (-1080 : Int64).toBitVec) 8).isSome
        = true := by
      obtain ⟨w, hw, -⟩ := ld64 hstk 1 ha1 (by simp only; omega) (by simp only; omega)
      rw [hw]; rfl
    have hmT : Box _ := ⟨hs8⟩
    clear hm hstk hs8
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    · exact hld
    · simp only [AddrIndex.offset64_scale2, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4068 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨⟨⟨hC, ?_, ?_, ?_, hN1, hlb⟩, [(0, NN x)], ?_, depth_init hN1, fl, _, pb,
          ⟨hl1, (setW8_length _ _ _ (by omega)).trans hl2, hl3⟩, hP, ⟨hSR _ hst, hQI'⟩,
          hmT.get _⟩, ?_⟩
        · simp only [Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hRg
        · regs_simp; exact h14
        · regs_simp; rw [hRg.2]; simp only [pA, sA, BitVec.add_assoc]; rfl
        · regs_simp; rfl
        · regs_simp; decide
      · rw [var_L4068]
        dsimp only [rN]
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [show (BitVec.setWidth 64 (BitVec.setWidth 32 1#64)).toNat = 1 by decide,
          hphi _ _ _ _ (by regs_simp) hst, phi_one]
        unfold wt; simp only [QV]; omega

theorem blk_L4200 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4200" := by
  cfg_block
  measure_hb "L4200"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, -⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4200] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨p1, p2, p3, p4, -, -⟩ := id hPD
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have e1 : s₀.regs.get64 .rdx - s₀.regs.get64 .r10 = BitVec.ofNat 64 (2 * (hi1 - 1 - l)) := by
      rw [hdx, h10, hi_addr _ _ (by omega), tlq_sub _ _ _ (by omega) (by omega)]; congr 1; omega
    have e2 : s₀.regs.get64 .r10 - s₀.regs.get64 .rsi = BitVec.ofNat 64 (2 * (l - lo)) := by
      rw [hsi, h10, tlq_sub _ _ _ (by omega) (by omega)]; congr 1; omega
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    all_goals rename_i c
    all_goals rw [e1, e2, tlq_ge64 _ _ (by omega) (by omega)] at c
    · simp only [decide_eq_true_eq] at c
      left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4250 _ _ _ _ _).2 ?_, Or.inr ⟨?_, by decide⟩⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          hPD, ?_, ?_, by omega⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L4250, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
    · simp only [decide_eq_false_iff_not] at c
      refine ⟨(tab_L4211 _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          hPD, ?_, ?_, by omega⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L4211, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _

theorem blk_L4211 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4211" := by
  cfg_block
  measure_hb "L4211"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, hc⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4211] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨p1, p2, p3, p4, -, -⟩ := id hPD
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    all_goals rename_i c
    all_goals rw [cc_nc_sub _ _ _ rfl, hcx, show BitVec.setWidth 64 (Int64.toBitVec 64) = 64#64 by decide,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat] at c
    · simp only [decide_eq_true_eq] at c; exfalso; omega
    · refine ⟨(tab_L421b _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          hPD, ?_, ?_, hc⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L421b, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _

theorem blk_L4250 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4250" := by
  cfg_block
  measure_hb "L4250"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, hc⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L4250] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨p1, p2, p3, p4, -, -⟩ := id hPD
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hmT : Box _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    all_goals rename_i c
    all_goals rw [cc_nc_sub _ _ _ rfl, hcx, show BitVec.setWidth 64 (Int64.toBitVec 64) = 64#64 by decide,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat] at c
    · simp only [decide_eq_true_eq] at c; exfalso; omega
    · refine ⟨(tab_L425a _ _ _ _ _).2 ?_, ?_⟩
      · refine ⟨?_, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, ⟨?_, hD, hDc, ?_, ?_, hQI⟩,
          hPD, ?_, ?_, hc⟩, hmT.get⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx
        · regs_simp; exact hsi
        · regs_simp; exact hdx
        · regs_simp; exact h10
        · regs_simp; exact h9
      · rw [var_L425a, phiC_mk _ _ _ _ (by regs_simp) (by regs_simp) (by regs_simp)
          (by regs_simp)]
        exact Nat.le_refl _

theorem blk_L421b (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L421b" := by
  cfg_block
  measure_hb "L421b"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, hc⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L421b] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := id hPD
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have es := shl4 S.length (by omega)
    have hst := focus (T_stk k x ra t₀ (Saved t₀) _) hm
    have ha0 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + (-1088 : Int64).toBitVec
        = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * (2 * S.length)) := by
      rw [hbp, show (-1088 : Int64).toBitVec = 18446744073709550528#64 by decide]
      exact addr_pop0 _ _ (by omega)
    have ha1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec
        = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * (2 * S.length + 1)) := by
      rw [hbp, show (-1080 : Int64).toBitVec = 18446744073709550536#64 by decide]
      exact addr_pop1 _ _ (by omega)
    have hl' : ∀ v, (setW8 stk (2 * S.length) v).length = 1024 := fun v => by
      rw [setW8_length _ _ _ (by omega)]; exact hl2
    have hl'' : ∀ v w, (setW8 (setW8 stk (2 * S.length) v) (2 * S.length + 1) w).length = 1024 :=
      fun v w => by rw [setW8_length _ _ _ (by rw [hl' v]; omega)]; exact hl' v
    have hs1 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v =⋆ setW8 stk (2 * S.length) v =@ (rS t₀ - 0x448#64)
        ⋆ Tstk k x ra t₀ (Saved t₀) fl x.a.nlim pb := fun v =>
      st64 hst _ ha0 (by simp only; omega) (by simp only; omega) v
    have hs2 : ∀ v w, (s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v).storeInt (s₀.regs.get64 .rbp
        + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec) 8 w
        =⋆ T k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim,
          setW8 (setW8 stk (2 * S.length) v) (2 * S.length + 1) w, pb⟩ := fun v w =>
      focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, _, pb⟩).symm
        (st64 (hs1 v) _ ha1 (by rw [hl' v]; omega) (by rw [hl' v]; omega) w)
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8).isSome = true := by
      obtain ⟨w, hw, -⟩ := ld64 hst _ ha0 (by simp only; omega) (by simp only; omega)
      rw [hw]; rfl
    have hld2 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v).loadInt (s₀.regs.get64 .rbp
        + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec) 8).isSome = true := fun v => by
      obtain ⟨w, hw, -⟩ := ld64 (hs1 v) _ ha1 (by rw [hl' v]; omega) (by rw [hl' v]; omega)
      rw [hw]; rfl
    have hr9' : s₀.regs.get64 .r9 = pA t₀ + BitVec.ofNat 64 (2 * (rt + 1)) - 2#64 := by
      rw [h9, hi_addr _ _ (by omega), Nat.add_sub_cancel]
    have hSR' := tlq_push hSR hl2 (by omega) (lo, rt + 1) _ _ hsi hr9'
    have hQI' := qi_split hQI p1 p2 p3 (by omega) p5 (fun q a b => p6 q a (by omega))
    replace hQI' : QI (NN x) (AV fl) (A0 x) ((S ++ [(lo, rt + 1)]) ++ [(l + 1, hi1)]) := by
      simpa using hQI'
    obtain ⟨hD', hDc'⟩ := depth_push (B := (lo, rt + 1)) (c := hi1 - (l + 1)) hD hDc (by omega)
      (by simp only; omega) (by omega)
    have hps := phi_split (lo := lo) (hi1 := hi1) (l := l) (rt := rt) (by omega) p3 (by omega)
    have hcx' : BitVec.ofNat 64 S.length + 1#64 = BitVec.ofNat 64 (S ++ [(lo, rt + 1)]).length := by
      apply BitVec.eq_of_toNat_eq; simp
    have hsi' : BitVec.setWidth 64 2#64 + s₀.regs.get64 .r10 = pA t₀ + BitVec.ofNat 64 (2 * (l + 1)) := by
      rw [h10]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (a c : BitVec 64),
        a = s₀.regs.get64 .rsi → c = s₀.regs.get64 .r9 →
        R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = BitVec.ofNat 64 (S ++ [(lo, rt + 1)]).length →
        R.get64 .rsi = pA t₀ + BitVec.ofNat 64 (2 * (l + 1)) →
        R.get64 .rdx = s₀.regs.get64 .rdx →
        phiC { regs := R, zmms := zm, status := sf,
               dmem := (s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
                 + (-1088 : Int64).toBitVec) 8 a.toInt).storeInt
                 (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
                 + (-1080 : Int64).toBitVec) 8 c.toInt }
          = phi ((S ++ [(lo, rt + 1)]) ++ [(l + 1, hi1)]) :=
        fun R zm sf a c ea ec e2 e3 e4 e5 => by
      have h := hs2 a.toInt c.toInt
      exact phiC_eq h (hl'' _ _) (e2.trans hbp) hR.1
        (tlq_push hSR hl2 (by omega) (lo, rt + 1) a c (ea.trans hsi) (ec.trans hr9')) hQI' e3
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) e4
        (e5.trans hdx)
    have hmT : Box _ := ⟨hs2⟩
    clear hm hst hs1 hs2
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    all_goals simp only [show (4#64).toNat % 256 % 64 = 4 by decide, show ¬ (4:Nat) = 0 by decide,
      ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, AddrIndex.offset64_scale1, hcx, es]
    · exact hld1
    · exact hld2 _
    · left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4090 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S ++ [(lo, rt + 1)], l + 1, hi1, fl, _, pb, ⟨hl1, hl'' _ _, hl3⟩, hP,
          ⟨hSR', ⟨?_, hD', hDc', ?_, ?_, hQI'⟩, trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx'
        · regs_simp; exact hsi'
        · regs_simp; exact hdx
      · rw [var_L4090, hphi' _ _ _ _ _ rfl rfl (by regs_simp) (by regs_simp; try exact hcx')
          (by regs_simp; try exact hsi') (by regs_simp), hphi]
        simp only [List.append_assoc, List.singleton_append, phi_append, QV] at hps ⊢
        omega

theorem blk_L425a (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L425a" := by
  cfg_block
  measure_hb "L425a"
    intro n
    refine Triple.pinR fun s₀ hs₀ => ?_
    obtain ⟨⟨hR, S, lo, hi1, l, rt, fl, stk, pb, hL, hP, ⟨hSR, hCur, hPD, h10, h9, hc⟩, hm⟩,
      hn⟩ := hs₀
    rw [var_L425a] at hn
    subst hn
    obtain ⟨hcx, hD, hDc, hsi, hdx, hQI⟩ := id hCur
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := id hPD
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by omega)
    have hWc := qi_cur hQI
    simp only at hWc
    have hphi := phiC_eq hm hl2 hbp hR.1 hSR hQI hcx (by omega) hsi hdx
    have es := shl4 S.length (by omega)
    have hst := focus (T_stk k x ra t₀ (Saved t₀) _) hm
    have ha0 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + (-1088 : Int64).toBitVec
        = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * (2 * S.length)) := by
      rw [hbp, show (-1088 : Int64).toBitVec = 18446744073709550528#64 by decide]
      exact addr_pop0 _ _ (by omega)
    have ha1 : s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec
        = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * (2 * S.length + 1)) := by
      rw [hbp, show (-1080 : Int64).toBitVec = 18446744073709550536#64 by decide]
      exact addr_pop1 _ _ (by omega)
    have hl' : ∀ v, (setW8 stk (2 * S.length) v).length = 1024 := fun v => by
      rw [setW8_length _ _ _ (by omega)]; exact hl2
    have hl'' : ∀ v w, (setW8 (setW8 stk (2 * S.length) v) (2 * S.length + 1) w).length = 1024 :=
      fun v w => by rw [setW8_length _ _ _ (by rw [hl' v]; omega)]; exact hl' v
    have hs1 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v =⋆ setW8 stk (2 * S.length) v =@ (rS t₀ - 0x448#64)
        ⋆ Tstk k x ra t₀ (Saved t₀) fl x.a.nlim pb := fun v =>
      st64 hst _ ha0 (by simp only; omega) (by simp only; omega) v
    have hs2 : ∀ v w, (s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v).storeInt (s₀.regs.get64 .rbp
        + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec) 8 w
        =⋆ T k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim,
          setW8 (setW8 stk (2 * S.length) v) (2 * S.length + 1) w, pb⟩ := fun v w =>
      focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, _, pb⟩).symm
        (st64 (hs1 v) _ ha1 (by rw [hl' v]; omega) (by rw [hl' v]; omega) w)
    have hld1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8).isSome = true := by
      obtain ⟨w, hw, -⟩ := ld64 hst _ ha0 (by simp only; omega) (by simp only; omega)
      rw [hw]; rfl
    have hld2 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
        + (-1088 : Int64).toBitVec) 8 v).loadInt (s₀.regs.get64 .rbp
        + BitVec.ofNat 64 (16 * S.length) + (-1080 : Int64).toBitVec) 8).isSome = true := fun v => by
      obtain ⟨w, hw, -⟩ := ld64 (hs1 v) _ ha1 (by rw [hl' v]; omega) (by rw [hl' v]; omega)
      rw [hw]; rfl
    have hr9' : s₀.regs.get64 .r9 = pA t₀ + BitVec.ofNat 64 (2 * (rt + 1)) - 2#64 := by
      rw [h9, hi_addr _ _ (by omega), Nat.add_sub_cancel]
    have hQI' := qi_comm2 (qi_split hQI p1 p2 p3 (by omega) p5 (fun q a b => p6 q a (by omega)))
    replace hQI' : QI (NN x) (AV fl) (A0 x) ((S ++ [(l + 1, hi1)]) ++ [(lo, rt + 1)]) := by
      simpa using hQI'
    obtain ⟨hD', hDc'⟩ := depth_push (B := (l + 1, hi1)) (c := rt + 1 - lo) hD hDc (by omega)
      (by simp only; omega) (by omega)
    have hps := phi_split' (lo := lo) (hi1 := hi1) (l := l) (rt := rt) (by omega) p3 (by omega)
    have hcx' : BitVec.ofNat 64 S.length + 1#64 = BitVec.ofNat 64 (S ++ [(l + 1, hi1)]).length := by
      apply BitVec.eq_of_toNat_eq; simp
    have hsi' : BitVec.setWidth 64 2#64 + s₀.regs.get64 .r10 = pA t₀ + BitVec.ofNat 64 (2 * (l + 1)) := by
      rw [h10]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega
    have hphi' : ∀ (R : Reg64s) (zm : _) (sf : StatusFlags) (a b : BitVec 64),
        a = pA t₀ + BitVec.ofNat 64 (2 * (l + 1)) → b = s₀.regs.get64 .rdx →
        R.get64 .rbp = s₀.regs.get64 .rbp →
        R.get64 .rcx = BitVec.ofNat 64 (S ++ [(l + 1, hi1)]).length →
        R.get64 .rsi = s₀.regs.get64 .rsi →
        R.get64 .rdx = pA t₀ + BitVec.ofNat 64 (2 * (rt + 1)) - 2#64 →
        phiC { regs := R, zmms := zm, status := sf,
               dmem := (s₀.dmem.storeInt (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
                 + (-1088 : Int64).toBitVec) 8 a.toInt).storeInt
                 (s₀.regs.get64 .rbp + BitVec.ofNat 64 (16 * S.length)
                 + (-1080 : Int64).toBitVec) 8 b.toInt }
          = phi ((S ++ [(l + 1, hi1)]) ++ [(lo, rt + 1)]) :=
        fun R zm sf a b ea eb e2 e3 e4 e5 => by
      have h := hs2 a.toInt b.toInt
      exact phiC_eq h (hl'' _ _) (e2.trans hbp) hR.1
        (tlq_push hSR hl2 (by omega) (l + 1, hi1) a b ea (eb.trans hdx)) hQI' e3
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (e4.trans hsi) e5
    have hmT : Box _ := ⟨hs2⟩
    clear hm hst hs1 hs2
    vcgen
    all_goals try call_simp
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat]
    all_goals (have e : s₀ = _ := ‹s₀ = _›; subst e)
    all_goals simp only [show (4#64).toNat % 256 % 64 = 4 by decide, show ¬ (4:Nat) = 0 by decide,
      ↓reduceIte, Reg64s.get64_set64, reduceCtorEq, AddrIndex.offset64_scale1, hcx, es]
    · exact hld1
    · exact hld2 _
    · left; apply Table.ofLabels_at
      refine ⟨by decide, (tab_L4090 _ _ _ _ _).2 ?_, Or.inl ?_⟩
      · refine ⟨?_, S ++ [(l + 1, hi1)], lo, rt + 1, fl, _, pb, ⟨hl1, hl'' _ _, hl3⟩, hP,
          ⟨tlq_push hSR hl2 (by omega) (l + 1, hi1) _ _ hsi' hdx, ⟨?_, hD', hDc', ?_, ?_, hQI'⟩,
            trivial⟩, hmT.get _ _⟩
        · simp only [QR, Regs, Regs0, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hR
        · regs_simp; exact hcx'
        · regs_simp; exact hsi
        · regs_simp; exact hr9'
      · rw [var_L4090, hphi' _ _ _ _ _ hsi' rfl (by regs_simp) (by regs_simp; exact hcx')
          (by regs_simp; try exact hsi) (by regs_simp; try exact hr9'), hphi]
        simp only [List.append_assoc, List.singleton_append, phi_append, QV] at hps ⊢
        omega

end Kraken.Examples.Sbr.Tlim

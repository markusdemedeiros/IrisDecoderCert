import Kraken.X64.Examples.Sbr.Parse.TlimAcc

/-!
# `sbr_make_f_tablelim`: around the two copies (`L3ff5`, `L4000`, `L4020`, `L4026`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- An unsigned 32-bit `cmp` of small values: the carry flag. -/
theorem ccmp (n c : Nat) (hn : n < 2 ^ 31) (hc : c < 2 ^ 31) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned
      != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).unsigned
        - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned)) :
    CondCode.c.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)) f)
      = decide (n < c) := by
  rw [cc_c_sub _ _ f hf]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  congr 1
  apply propext
  omega

omit [CodeEnv] in
/-- An unsigned 32-bit `cmp` of small values: no carry. -/
theorem ncmp (n c : Nat) (hn : n < 2 ^ 31) (hc : c < 2 ^ 31) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned
      != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).unsigned
        - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)) f)
      = decide (c ≤ n) := by
  rw [cc_nc_sub _ _ f hf]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  congr 1
  apply propext
  omega

omit [CodeEnv] in
theorem add32 (a b : Nat) (h : a + b < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 b) + BitVec.setWidth 32 (BitVec.ofNat 64 a))
      = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

omit [CodeEnv] in
/-- With fewer than two patches the second copy is empty. -/
theorem cp_cp2 (x : TArgs) (fl : List UInt8) (h1 : x.a.npatch ≤ 1)
    (h : ∀ q, AV fl q = if q ≤ x.a.n0 then u16 x.a.ftLow q else u16 x.a.ftLim q) :
    ∀ q, AV fl q = A0 x q := by
  intro q
  rw [h q]
  simp only [A0, limIn]
  by_cases e : q ≤ x.a.n0
  · simp only [e, ↓reduceIte]
  · simp only [e, ↓reduceIte, show ¬ q < x.a.n0 + x.a.npatch by omega]

theorem blk_L3ff5 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3ff5" := by
  cfg_block
  measure_hb "L3ff5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, h14, h15, fl, stk, pb, hL, hP, hAV, hm⟩, hn⟩ := hs₀
    rw [var_L3ff5] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -⟩ := hC'
    have hnp := RO_np (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hnp
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hnp, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast,
      zx_small _ (show x.a.npatch < 2 ^ 31 by omega)] at *
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L4026], by decide⟩⟩
      rw [tab_L4026]
      rename_i hc
      rw [ccmp _ _ (by omega) (by omega) _ (by rfl), decide_eq_true_eq] at hc
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, fl, stk, pb, hL, hP, cp_cp2 x fl (by omega) hAV,
        hmT⟩, ?_⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14, h15]
    · rw [tab_L4000, var_L4000]
      rename_i hc
      rw [ccmp _ _ (by omega) (by omega) _ (by rfl), decide_eq_false_iff_not] at hc
      refine ⟨⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, fl, stk, pb, hL, hP, hAV, hmT⟩, ?_, by omega⟩,
        Nat.le_refl _⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14, h15]

theorem blk_L4000 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4000" := by
  cfg_block
  measure_hb "L4000"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hCp, hdx, hnp2⟩, hn⟩ := hs₀
    have hCp' := hCp
    obtain ⟨hC, -, -, -, h15, -⟩ := hCp'
    have hC' := hC
    obtain ⟨-, hn0, -⟩ := hC'
    rw [var_L4000] at hn
    subst hn
    have hH : Hide _ := hCp
    clear hCp
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat] at *
    · exfalso; rename_i hc
      rw [h15, ncmp _ _ (by omega) (by omega) _ (by rfl), decide_eq_true_eq] at hc
      omega
    · rw [tab_L400a, var_L400a]
      exact ⟨⟨hH, hdx, hnp2⟩, Nat.le_refl _⟩

theorem blk_L4020 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4020" := by
  cfg_block
  measure_hb "L4020"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, h14, h15, fl, stk, pb, hL, hP, hAV, hm⟩, hn⟩ := hs₀
    rw [var_L4020] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, -, hnp6, -⟩ := hC'
    have hnp := RO_np (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hnp
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hnp, Option.isSome_some,
      Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast,
      zx_small _ (show x.a.npatch < 2 ^ 31 by omega)] at *
    rw [tab_L4026, var_L4026]
    refine ⟨⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, fl, stk, pb, hL, hP, hAV, hmT⟩, ?_⟩,
      Nat.le_refl _⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14, h15]

theorem blk_L4026 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4026" := by
  cfg_block
  measure_hb "L4026"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, h14, h15, fl, stk, pb, hL, hP, hAV, hm⟩, hdx⟩, hn⟩ :=
      hs₀
    rw [var_L4026] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    obtain ⟨hL1, hL2, hL3⟩ := id hL
    replace hL2 : stk.length = 1024 := hL2
    have hstk := focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm
    have hs8 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709550528#64) 8 v =⋆
        T k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, setW8 stk 0 v, pb⟩ := fun v =>
      focus (T_stk k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, setW8 stk 0 v, pb⟩).symm
        (st64 hstk 0 (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega)
          (by simp only; omega) v)
    have hl8 := ld64 hstk 0 (addr := s₀.regs.get64 .rbp + 18446744073709550528#64)
      (by rw [hbp]; simp only [rS]; bv_omega) (by simp only; omega) (by simp only; omega)
    obtain ⟨w, hw, -⟩ := hl8
    have hj4 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709550528#64) 8 v).loadInt
        (s₀.regs.get64 .rbp + 18446744073709551564#64) 4).isSome = true := fun v => by
      have h := focus (T_j k x ra t₀ (Saved t₀) _) (hs8 v)
      simp only [Junk] at h
      obtain ⟨F, h⟩ := pick_lr h
      obtain ⟨F, h⟩ := pick_ll h
      rw [show s₀.regs.get64 .rbp + 18446744073709551564#64 = rS t₀ - 0x3c#64 by
        rw [hbp]; simp only [rS]; bv_omega]
      exact slot_load h (by omega)
    have hsH : Hide _ := hs8
    have hNN : x.a.n0 + x.a.npatch < 31 := by omega
    clear hm hstk hs8
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.ofNat_eq_ofNat, hw, hj4,
      AddrIndex.offset64_none, BitVec.add_zero, hdx, h15, Option.isSome_some] at *
    all_goals simp only [add32 _ _ (show x.a.n0 + x.a.npatch < 2 ^ 32 by omega)] at *
    · exfalso; rename_i hc
      rw [ncmp _ _ (by omega) (by omega) _ (by rfl), decide_eq_true_eq] at hc
      omega
    · rw [tab_L403f, var_L403f]
      unfold Hide at hsH
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, ?_, fl, _, pb, ⟨hL1, ?_, hL3⟩, hP, ⟨hAV, ?_⟩,
        hsH _⟩, Nat.le_refl _⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14]
      · exact (setW8_length stk 0 _ (by omega)).trans hL2
      · refine (w8_setW8 stk 0 (t₀.regs.get64 .rdi + 312050#64) (by omega) 0).trans ?_
        simp only [↓reduceIte]

end Kraken.Examples.Sbr.Tlim

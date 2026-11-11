import Kraken.X64.Examples.Sbr.Parse.TlimAcc

/-!
# `sbr_make_f_tablelim`: `AV_QSORT` helpers

* The measure `stkPhi` read from memory is `phi` of the pending intervals (`stkPhi_eq`), and
  `phiC` with the current interval is `phi (S ++ [(lo, hi1)])`.
* Bounds: `NN x ≤ 30`; the values below `NN x` stay below `2 ^ 15` (`Perm.bounds`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

/-- An opaque box for big hypotheses (`whnf` does not unfold it). -/
structure Box (p : Prop) : Prop where
  get : p

/-- `Triple.pin` with the equation the other way round (`subst` then eliminates the new state,
not the pinned one). -/
theorem Triple.pinR {P : MachineData → Prop} {c : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop}
    (h : ∀ s₀, P s₀ → ⦃ fun s => s₀ = s ⦄ c ⦃ Q; E ⦄) : ⦃ P ⦄ c ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (h s hs).le_wp s rfl

/-! ## Bounds -/

theorem NN_le {x : TArgs} {t₀ : MachineData} (hC : TlimC x.lb x.a t₀) : NN x ≤ 30 := by
  obtain ⟨-, h1, h2, -⟩ := hC; simp only [NN]; omega

theorem pA_nat {x : TArgs} {t₀ : MachineData} (hC : TlimC x.lb x.a t₀) :
    0x4c2f2 ≤ (pA t₀).toNat ∧ (pA t₀).toNat + 0x4e < 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw⟩ := hC
  simp only [pA, sA] at *
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

/-- The input values are below `2 ^ 15`. -/
theorem A0_lt {x : TArgs} {t₀ : MachineData} (hC : TlimC x.lb x.a t₀) (q : Nat) (hq : q < NN x) :
    A0 x q < 2 ^ 15 := by
  obtain ⟨-, -, -, -, -, -, -, hT, hps, hkm, -⟩ := hC
  simp only [A0, limIn]
  split
  · rename_i h
    have := (hT.1 q h).2
    omega
  · have := psum_mono x.a.pnum (show q - x.a.n0 ≤ x.a.npatch by simp only [NN] at hq; omega)
    omega

theorem qi_lt {x : TArgs} {t₀ : MachineData} (hC : TlimC x.lb x.a t₀) {A : Nat → Nat}
    {P : List Iv} (h : QI (NN x) A (A0 x) P) : ∀ q, q < NN x → A q < 2 ^ 15 :=
  h.2.2.2.bounds (P := fun v => v < 2 ^ 15) (A0_lt hC)

/-- The end of the sort: the model's `Sorted`. -/
theorem qi_Sorted {N : Nat} {A A0 : Nat → Nat} (h : QI N A A0 []) : Sorted N A0 A :=
  ⟨qi_sorted_succ h, h.2.2.2.prov, h.2.2.2.frame⟩

/-! ## The measure -/

omit [CodeEnv] in
theorem wB_iv {p : BitVec 64} (hp : 2 ≤ p.toNat) {lo hi1 : Nat} (hl : lo ≤ hi1)
    (hw : p.toNat + 2 * hi1 < 2 ^ 64) :
    wB (p + BitVec.ofNat 64 (2 * lo)) (p + BitVec.ofNat 64 (2 * hi1) - 2#64) = wt (lo, hi1) := by
  have e1 : (p + BitVec.ofNat 64 (2 * lo)).toNat = p.toNat + 2 * lo := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : (p + BitVec.ofNat 64 (2 * hi1) - 2#64).toNat = p.toNat + 2 * hi1 - 2 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  have := wBn_iv (w := 2) (p := p.toNat) (lo := lo) (hi1 := hi1) (by omega) (by omega)
  unfold wB; unfold wBn at this; unfold wt
  rw [e1, e2]; simp only at this ⊢; omega

omit [CodeEnv] in
theorem addr_stk0 (r : BitVec 64) (n : Nat) (hn : n < 64) :
    r - 8#64 - 0x440#64 + BitVec.ofNat 64 (16 * n) = r - 0x448#64 + BitVec.ofNat 64 (8 * (2 * n)) := by
  rw [show 8 * (2 * n) = 16 * n by omega]; bv_omega

omit [CodeEnv] in
theorem addr_stk1 (r : BitVec 64) (n : Nat) (hn : n < 64) :
    r - 8#64 - 0x440#64 + BitVec.ofNat 64 (16 * n) + 8#64
      = r - 0x448#64 + BitVec.ofNat 64 (8 * (2 * n + 1)) := by
  rw [show 8 * (2 * n + 1) = 16 * n + 8 by omega]; bv_omega

/-- A word of the stack read from memory. -/
theorem ld8_stk {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hlen : st.stk.length = 1024) (j : Nat) (hj : j < 128)
    {a : BitVec 64} (ha : a = rS t₀ - 0x448#64 + BitVec.ofNat 64 (8 * j)) :
    ld8 s a = w8 st.stk j := by
  have h := focus (T_stk k x ra t₀ FR st) hm
  obtain ⟨v, hv, e⟩ := ld64 h j ha (by omega) (by omega)
  unfold ld8; rw [hv]; exact e

theorem stkPhi_take {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hlen : st.stk.length = 1024)
    (hbp : s.regs.get64 .rbp = rS t₀ - 8#64) {p : BitVec 64} (hp : 2 ≤ p.toNat)
    {N : Nat} (hpN : p.toNat + 2 * N < 2 ^ 64) {S : List Iv} (hS : StkRel p st.stk S)
    (hW : Within N S) (hn : S.length ≤ 64) :
    ∀ n, n ≤ S.length → stkPhi s n = phi (S.take n) := by
  intro n
  induction n with
  | zero => intro _; simp [stkPhi, phi]
  | succ n ih =>
    intro hn1
    have e0 : stkPhi s (n + 1) = stkPhi s n + wB (ld8 s (s.regs.get64 .rbp - 0x440#64 + v64 (16 * n)))
        (ld8 s (s.regs.get64 .rbp - 0x440#64 + v64 (16 * n) + 8#64)) := by
      simp [stkPhi, List.range_succ, List.map_append, List.sum_append]
    rw [e0, ih (by omega)]
    have h1 := ld8_stk hm hlen (2 * n) (by omega) (a := s.regs.get64 .rbp - 0x440#64 + v64 (16 * n))
      (by rw [hbp]; exact addr_stk0 _ n (by omega))
    have h2 := ld8_stk hm hlen (2 * n + 1) (by omega)
      (a := s.regs.get64 .rbp - 0x440#64 + v64 (16 * n) + 8#64)
      (by rw [hbp]; exact addr_stk1 _ n (by omega))
    obtain ⟨r1, r2⟩ := hS n (by omega)
    rw [h1, h2, r1, r2]
    have hw := hW S[n] (List.getElem_mem _)
    rw [wB_iv hp hw.1 (by omega), List.take_succ, List.getElem?_eq_getElem (by omega),
      phi_append]
    simp [phi, Option.toList]

theorem stkPhi_eq {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hlen : st.stk.length = 1024)
    (hbp : s.regs.get64 .rbp = rS t₀ - 8#64) {p : BitVec 64} (hp : 2 ≤ p.toNat)
    {N : Nat} (hpN : p.toNat + 2 * N < 2 ^ 64) {S : List Iv} (hS : StkRel p st.stk S)
    (hW : Within N S) (hn : S.length ≤ 64) : stkPhi s S.length = phi S := by
  rw [stkPhi_take hm hlen hbp hp hpN hS hW hn S.length (Nat.le_refl _), List.take_length]

omit [CodeEnv] in
/-- `stkPhi` reads only memory and `rbp`. -/
theorem stkPhi_mk (s : MachineData) (R : Reg64s) (z) (st) (hb : R.get64 .rbp = s.regs.get64 .rbp)
    (n : Nat) : stkPhi { regs := R, zmms := z, status := st, dmem := s.dmem } n = stkPhi s n := by
  unfold stkPhi ld8; simp only [hb]

omit [CodeEnv] in
theorem phiC_mk (s : MachineData) (R : Reg64s) (z) (st) (hb : R.get64 .rbp = s.regs.get64 .rbp)
    (hc : R.get64 .rcx = s.regs.get64 .rcx) (hsi : R.get64 .rsi = s.regs.get64 .rsi)
    (hdx : R.get64 .rdx = s.regs.get64 .rdx) :
    phiC { regs := R, zmms := z, status := st, dmem := s.dmem } = phiC s := by
  unfold phiC rN; simp only [hc, hsi, hdx, stkPhi_mk s R z st hb]

/-- The measure with the current interval. -/
theorem phiC_eq {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hlen : st.stk.length = 1024)
    (hbp : s.regs.get64 .rbp = rS t₀ - 8#64) (hC : TlimC x.lb x.a t₀) {S : List Iv} {lo hi1 : Nat}
    {A : Nat → Nat} (hSR : StkRel (pA t₀) st.stk S) (hQ : QI (NN x) A (A0 x) (S ++ [(lo, hi1)]))
    (hcx : s.regs.get64 .rcx = BitVec.ofNat 64 S.length) (hS : S.length ≤ 64)
    (hsi : s.regs.get64 .rsi = pA t₀ + BitVec.ofNat 64 (2 * lo))
    (hdx : s.regs.get64 .rdx = pA t₀ + BitVec.ofNat 64 (2 * hi1) - 2#64) :
    phiC s = phi (S ++ [(lo, hi1)]) := by
  have hpn := pA_nat hC
  have hN := NN_le hC
  have hW := hQ.2.2.1
  have hc := qi_cur hQ
  simp only at hc
  unfold phiC rN
  rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hsi, hdx,
    stkPhi_eq hm hlen hbp (p := pA t₀) (N := NN x) (by omega) (by omega) hSR
      (fun J hJ => hW J (by simp [hJ])) hS,
    wB_iv (by omega) hc.1 (by omega), phi_append, phi_one]

/-- The measure between partitions. -/
theorem stkPhi_S {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hlen : st.stk.length = 1024)
    (hbp : s.regs.get64 .rbp = rS t₀ - 8#64) (hC : TlimC x.lb x.a t₀) {S : List Iv}
    {A : Nat → Nat} (hSR : StkRel (pA t₀) st.stk S) (hQ : QI (NN x) A (A0 x) S)
    (hS : S.length ≤ 64) : stkPhi s S.length = phi S := by
  have hpn := pA_nat hC
  have hN := NN_le hC
  exact stkPhi_eq hm hlen hbp (p := pA t₀) (N := NN x) (by omega) (by omega) hSR hQ.2.2.1 hS

/-! ## Register arithmetic (standalone, small contexts) -/

omit [CodeEnv] in
theorem dec32 (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) - 1#32) = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

omit [CodeEnv] in
theorem shl4 (m : Nat) (h : m < 2 ^ 32) : BitVec.ofNat 64 m <<< 4 = BitVec.ofNat 64 (16 * m) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

omit [CodeEnv] in
theorem addr_pop0 (r : BitVec 64) (m : Nat) (hm : m < 64) :
    r - 8#64 + BitVec.ofNat 64 (16 * m) + 18446744073709550528#64
      = r - 0x448#64 + BitVec.ofNat 64 (8 * (2 * m)) := by
  rw [show 8 * (2 * m) = 16 * m by omega]; bv_omega

omit [CodeEnv] in
theorem addr_pop1 (r : BitVec 64) (m : Nat) (hm : m < 64) :
    r - 8#64 + BitVec.ofNat 64 (16 * m) + 18446744073709550536#64
      = r - 0x448#64 + BitVec.ofNat 64 (8 * (2 * m + 1)) := by
  rw [show 8 * (2 * m + 1) = 16 * m + 8 by omega]; bv_omega

omit [CodeEnv] in
theorem nc32_cmp (n c : Nat) (hn : n < 2 ^ 31) (hc : c < 2 ^ 31) (af ofl : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c))
      { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned
            != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).unsigned
              - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned, af := af, of := ofl })
      = decide (c ≤ n) := by
  rw [cc_nc_sub _ _ _ rfl]; simp; omega

omit [CodeEnv] in
theorem tn_add (P : BitVec 64) (n : Nat) (h : P.toNat + n < 2 ^ 64) :
    (P + BitVec.ofNat 64 n).toNat = P.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem tn_hi (P : BitVec 64) (n : Nat) (h2 : 2 ≤ P.toNat) (h : P.toNat + n < 2 ^ 64) :
    (P + BitVec.ofNat 64 n - 2#64).toNat = P.toNat + n - 2 := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega

omit [CodeEnv] in
theorem tn_hi4 (P : BitVec 64) (n : Nat) (h2 : 4 ≤ P.toNat) (h : P.toNat + n < 2 ^ 64) :
    (P + BitVec.ofNat 64 n - 2#64 + 18446744073709551614#64).toNat = P.toNat + n - 4 := by
  rw [BitVec.toNat_add, tn_hi P n (by omega) h]; simp; omega

omit [CodeEnv] in
theorem zx16' (u : Nat) (hu : u < 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))) = BitVec.ofNat 64 u := by
  apply BitVec.eq_of_toNat_eq; simp; omega

omit [CodeEnv] in
theorem sw16' (u : Nat) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))))
      = BitVec.ofNat 16 u := by
  rw [sw16, ofInt16_nat]

omit [CodeEnv] in
/-- `mid = start + ((end - start) >> 1)` in bytes. -/
theorem mid_addr (P : BitVec 64) (lo hi1 : Nat) (hl : lo + 2 ≤ hi1) (h2 : 2 ≤ P.toNat)
    (h : P.toNat + 2 * hi1 < 2 ^ 64) (h64 : hi1 < 2 ^ 32) :
    P + BitVec.ofNat 64 (2 * lo)
      + (P + BitVec.ofNat 64 (2 * hi1) - 2#64 - (P + BitVec.ofNat 64 (2 * lo))).sshiftRight 2
        * 2#64 + 0#64
      = P + BitVec.ofNat 64 (2 * (lo + (hi1 - 1 - lo) / 2)) := by
  have e1 : P + BitVec.ofNat 64 (2 * hi1) - 2#64 - (P + BitVec.ofNat 64 (2 * lo))
      = BitVec.ofNat 64 (2 * (hi1 - 1 - lo)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn_hi P _ h2 h, tn_add P _ (by omega), BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (2 * (hi1 - 1 - lo))).sshiftRight 2
      = BitVec.ofNat 64 ((hi1 - 1 - lo) / 2) := by
    rw [BitVec.sshiftRight_eq_of_msb_false (by simp [BitVec.msb_eq_decide]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [e1, e2]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

omit [CodeEnv] in
theorem hi_addr (P : BitVec 64) (hi1 : Nat) (h : 1 ≤ hi1) :
    P + BitVec.ofNat 64 (2 * hi1) - 2#64 = P + BitVec.ofNat 64 (2 * (hi1 - 1)) := by
  rw [show 2 * hi1 = 2 * (hi1 - 1) + 2 by omega]; bv_omega

omit [CodeEnv] in
theorem hi_addr2 (P : BitVec 64) (hi1 : Nat) (h : 2 ≤ hi1) :
    P + BitVec.ofNat 64 (2 * hi1) - 2#64 + 18446744073709551614#64
      = P + BitVec.ofNat 64 (2 * (hi1 - 1 - 1)) := by
  rw [show 2 * hi1 = 2 * (hi1 - 1 - 1) + 4 by omega]; bv_omega

/-- Register reads through `set64`. -/
macro "regs_simp" : tactic => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])

/-! ## The stack relation -/

omit [CodeEnv] in
theorem stkRel_pop {p : BitVec 64} {stk : List UInt8} {S : List Iv} {I : Iv}
    (h : StkRel p stk (S ++ [I])) : StkRel p stk S
      ∧ w8 stk (2 * S.length) = p + BitVec.ofNat 64 (2 * I.1)
      ∧ w8 stk (2 * S.length + 1) = p + BitVec.ofNat 64 (2 * I.2) - 2#64 := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · have := h S.length (by simp)
    simpa using this

end Kraken.Examples.Sbr.Tlim

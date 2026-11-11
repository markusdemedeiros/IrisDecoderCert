import Kraken.X64.Examples.Sbr.Parse.ResetQs1Lib

/-!
# `sbr_reset`, `AV_QSORT` copy 4 (`vk1`): the `A2.S` wrapper

Copy 4 runs inside `A2.S` with extra facts: `k[0]`, `k[2]` (`C`), the registers `r12`, `r13`,
`r15` (`Rg`, untouched by the sort), and the frame facts `Inc` (`vk0`), `-0x30`, `TA` (`W`, kept by
the element and stack stores). `G Q` is the table's shape with `Q k0 k2 fr` the sort's part.

* `g_iff`: `G Q` as `C`, `Base`, `Rg`, `FrOk`, `W`, the memory and `Q`.
* `w_wr`: `W` is kept by a store below `vk0` or into `vk1`.
* `sd_st`: `sd_st` of copy 1 with `W` for the saved slots.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

namespace Q4

variable [CodeEnv]

/-- The static facts: `AtMaster`'s, `bs_freq_scale ≠ 0`, the stored `k[1]`, `k[2]`, two regions,
`num_bands_1` in range. -/
def C (e : REnv) (a : RArgs) (t₀ : MachineData) (row k2 : Nat) (st : St) : Prop :=
  ResetCI a t₀ ∧ BandsOK e.lg e.pw ∧ rateRow (srI a) = some row ∧ k2 ≤ 64 ∧ k0N a row ≤ k2
  ∧ (k2 : Int) - k0A a row ≤ maxQ (srI a) ∧ 1 ≤ u8 a.sp 3
  ∧ st.x = xk0 a row ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ st.k2 = BitVec.ofNat 32 k2
  ∧ st.k1 = BitVec.ofNat 32 (A2.k1Of (k0N a row) k2) ∧ 110 * k0N a row < 49 * k2
  ∧ A2.N1 e a (k0N a row) k2

/-- The registers kept through the sort. -/
def Rg (e : REnv) (a : RArgs) (k0 k2 : Nat) (t₀ s : MachineData) : Prop :=
  (s.regs.get64 .r15).setWidth 32 + (s.regs.get64 .r15).setWidth 32
    = BitVec.ofNat 32 (A2.n1N e a k0 k2)
  ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (A2.n1N e a k0 k2)

/-- The frame facts kept through the sort. -/
def W (e : REnv) (a : RArgs) (t₀ : MachineData) (k0 k2 : Nat) (fr : List UInt8) : Prop :=
  A2.N0 e a k0 k2 ∧ A2.Inc fr 0x400 (A2.n0N e a k0 k2) k0 (A2.k1Of k0 k2)
  ∧ frSlot64 fr 0x30 = BitVec.ofNat 64 (A2.n1N e a k0 k2)
  ∧ ∃ vm, A2.TA fr t₀ (A2.n0N e a k0 k2) vm

/-- The table's shape for copy 4. -/
def G (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (Q : Nat → Nat → List UInt8 → Prop) : Prop :=
  A2.S k e a ra t₀ s (fun k0 k2 _ fr => 110 * k0 < 49 * k2
    ∧ A2.Inc fr 0x400 (A2.n0N e a k0 k2) k0 (A2.k1Of k0 k2) ∧ A2.N0 e a k0 k2
    ∧ A2.N1 e a k0 k2
    ∧ (s.regs.get64 .r15).setWidth 32 + (s.regs.get64 .r15).setWidth 32
      = BitVec.ofNat 32 (A2.n1N e a k0 k2)
    ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (A2.n1N e a k0 k2)
    ∧ frSlot64 fr 0x30 = BitVec.ofNat 64 (A2.n1N e a k0 k2)
    ∧ ∃ vm, A2.TA fr t₀ (A2.n0N e a k0 k2) vm ∧ Q k0 k2 fr)

theorem g_iff {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData}
    {Q : Nat → Nat → List UInt8 → Prop} :
    G k e a ra t₀ s Q ↔ ∃ (row k2 : Nat) (st : St) (fr : List UInt8), C e a t₀ row k2 st
      ∧ Base t₀ s ∧ Rg e a (k0N a row) k2 t₀ s ∧ FrOk fr ∧ W e a t₀ (k0N a row) k2 fr
      ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr) ∧ Q (k0N a row) k2 fr := by
  constructor
  · rintro ⟨row, k2, hr, hk2, hk0, hq, hu, hC, hB, hb, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h110, hInc, hN0, hN1, h15, h12, h13, h30, vm, hTA, hQ⟩, hm⟩
    exact ⟨row, k2, st, fr, ⟨hC, hB, hr, hk2, hk0, hq, hu, hx, hsp, hfm, hk2v, hk1v, h110, hN1⟩,
      hb, ⟨h15, h12, h13⟩, hF, ⟨hN0, hInc, h30, vm, hTA⟩, hm, hQ⟩
  · rintro ⟨row, k2, st, fr, ⟨hC, hB, hr, hk2, hk0, hq, hu, hx, hsp, hfm, hk2v, hk1v, h110, hN1⟩,
      hb, ⟨h15, h12, h13⟩, hF, ⟨hN0, hInc, h30, vm, hTA⟩, hm, hQ⟩
    exact ⟨row, k2, hr, hk2, hk0, hq, hu, hC, hB, hb, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h110, hInc, hN0, hN1, h15, h12, h13, h30, vm, hTA, hQ⟩, hm⟩

omit [CodeEnv] in
theorem Rg.tr {e : REnv} {a : RArgs} {k0 k2 : Nat} {t₀ s s' : MachineData}
    (h : Rg e a k0 k2 t₀ s) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15)
    (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12) (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) :
    Rg e a k0 k2 t₀ s' := by
  unfold Rg at *; rw [h15, h12, h13]; exact h

theorem C.rc {e : REnv} {a : RArgs} {t₀ : MachineData} {row k2 : Nat} {st : St}
    (h : C e a t₀ row k2 st) : 0x578 ≤ (t₀.regs.get64 .rsp).toNat := by
  have := rsp_ok h.1; unfold resetStkMin at this; omega

theorem C.n1 {e : REnv} {a : RArgs} {t₀ : MachineData} {row k2 : Nat} {st : St}
    (h : C e a t₀ row k2 st) :
    2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2.2
  simp only [A2.n1N]; exact ⟨by omega, by omega⟩

omit [CodeEnv] in
theorem toInt_ofInt16 {x : Int} (h1 : -256 ≤ x) (h2 : x ≤ 256) : (BitVec.ofInt 16 x).toInt = x := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod]; split <;> omega

omit [CodeEnv] in
/-- An element of a permutation of `A0` is in `A0`'s range. -/
theorem cur_range {N : Nat} {A A0 : Nat → Int} {B tot : Int} (hR : QS.AB N A0 B tot)
    (hP : Perm N A A0) {q : Nat} (hq : q < N) : -B ≤ A q ∧ A q ≤ B := by
  obtain ⟨t, ht, e⟩ := hP.prov q hq
  rw [e]; exact hR.1 t ht

omit [CodeEnv] in
theorem inc_congr {fr fr' : List UInt8} {o n : Nat} {v0 v1 : Int}
    (h : ∀ j, j ≤ n → A2.fv fr' o j = A2.fv fr o j) :
    A2.Inc fr' o n v0 v1 ↔ A2.Inc fr o n v0 v1 := by
  unfold A2.Inc
  rw [h 0 (by omega), h n (Nat.le_refl _)]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, fun i hi => ?_⟩
    have := h2 i hi
    rwa [h i (by omega), h (i + 1) (by omega)] at this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, fun i hi => ?_⟩
    rw [h i (by omega), h (i + 1) (by omega)]
    exact h2 i hi

omit [CodeEnv] in
/-- `W` is kept by a store below `vk0` (the stack) or into `vk1`. -/
theorem w_wr {fr : List UInt8} (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int)
    (hd : o + n ≤ 0x400 ∨ (0x464 ≤ o ∧ o + n ≤ 0x4e8)) {e : REnv} {a : RArgs}
    {t₀ : MachineData} {k0 k2 : Nat} :
    W e a t₀ k0 k2 (wr fr o (Int.toBytes n v)) ↔ W e a t₀ k0 k2 fr := by
  unfold W A2.TA
  rw [slot_wr64 hF h v (d := 0x30) (by simp only [rb]; omega),
    slot_wr64 hF h v (d := 0x40) (by simp only [rb]; omega),
    slot_wr64 hF h v (d := 0x48) (by simp only [rb]; omega),
    slot_wr64 hF h v (d := 0x88) (by simp only [rb]; omega),
    slot_wr32 hF h v (d := 0x50) (by simp only [rb]; omega)]
  constructor
  · rintro ⟨hN0, hI, hr⟩
    have : A2.n0N e a k0 k2 ≤ 48 := by have := hN0.2.1; simp only [A2.n0N]; omega
    refine ⟨hN0, (inc_congr fun j hj => ?_).mp hI, hr⟩
    simp only [A2.fv]; rw [slice_wr_other hF h v (by omega)]
  · rintro ⟨hN0, hI, hr⟩
    have : A2.n0N e a k0 k2 ≤ 48 := by have := hN0.2.1; simp only [A2.n0N]; omega
    refine ⟨hN0, (inc_congr fun j hj => ?_).mpr hI, hr⟩
    simp only [A2.fv]; rw [slice_wr_other hF h v (by omega)]

omit [CodeEnv] in
theorem arr_congr {fr fr' : List UInt8} {o n : Nat} {B tot : Int}
    (h : ∀ i, 1 ≤ i → i ≤ n → A2.fv fr' o i = A2.fv fr o i) :
    A2.Arr fr' o n B tot ↔ A2.Arr fr o n B tot := by
  constructor
  · rintro ⟨A, hA, hs⟩
    exact ⟨A, fun i h1 h2 => by rw [← h i h1 h2]; exact hA i h1 h2, hs⟩
  · rintro ⟨A, hA, hs⟩
    exact ⟨A, fun i h1 h2 => by rw [h i h1 h2]; exact hA i h1 h2, hs⟩

omit [CodeEnv] in
/-- `Arr` of `vk1` is kept by a store outside it. -/
theorem arr_wr {fr : List UInt8} (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int)
    {m : Nat} (hm : m ≤ 49) (hd : o + n ≤ 0x482 ∨ 0x4e4 ≤ o) {B tot : Int} :
    A2.Arr (wr fr o (Int.toBytes n v)) 0x480 m B tot ↔ A2.Arr fr 0x480 m B tot :=
  arr_congr fun i _ hi => by simp only [A2.fv]; rw [slice_wr_other hF h v (by omega)]

omit [CodeEnv] in
/-- `W` after the store of `num_bands_1` to `-0x30`. -/
theorem w_set30 {fr : List UInt8} (hF : FrOk fr) {e : REnv} {a : RArgs} {t₀ : MachineData}
    {k0 k2 : Nat} (hN0 : A2.N0 e a k0 k2)
    (hI : A2.Inc fr 0x400 (A2.n0N e a k0 k2) k0 (A2.k1Of k0 k2)) {vm : Int}
    (hT : A2.TA fr t₀ (A2.n0N e a k0 k2) vm) {v : Int}
    (hv : BitVec.ofInt 64 v = BitVec.ofNat 64 (A2.n1N e a k0 k2)) :
    W e a t₀ k0 k2 (wr fr (rb 0x30) (Int.toBytes 8 v)) := by
  have h : rb 0x30 + 8 ≤ 0x548 := by simp only [rb]; omega
  have : A2.n0N e a k0 k2 ≤ 48 := by have := hN0.2.1; simp only [A2.n0N]; omega
  refine ⟨hN0, (inc_congr fun j hj => ?_).mpr hI, ?_, vm, ?_⟩
  · simp only [A2.fv]; rw [slice_wr_other hF h v (by simp only [rb]; omega)]
  · rw [slot_wr_same hF h rfl, hv]
  · unfold A2.TA at *
    rw [slot_wr64 hF h v (d := 0x40) (by simp only [rb]; omega),
      slot_wr64 hF h v (d := 0x48) (by simp only [rb]; omega),
      slot_wr64 hF h v (d := 0x88) (by simp only [rb]; omega),
      slot_wr32 hF h v (d := 0x50) (by simp only [rb]; omega)]
    exact hT

/-- A 16-bit store to element `q` of `vk1`. -/
theorem sd_st {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    {k0 k2 : Nat} (hW : W e a t₀ k0 k2 fr) {o q : Nat}
    (h : o + 2 * (q + 1) + 2 ≤ 0x4e8) (ho : 0x464 ≤ o + 2 * (q + 1)) (x : BitVec 16) :
    (m.storeInt (QS.ep t₀ o q) 2 x.toInt
      =⋆ Mm k e a ra t₀ st (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)))
    ∧ FrOk (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt))
    ∧ W e a t₀ k0 k2 (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt))
    ∧ (∀ {o' : Nat} {S : List Iv}, S.length ≤ 64 →
        (QS.StkRel (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) t₀ o' S
          ↔ QS.StkRel fr t₀ o' S))
    ∧ (∀ r, QS.av (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) o r
        = upd (QS.av fr o) q x.toInt r) := by
  obtain ⟨h1, h2, -, -, h5, h6⟩ := Reset.sd_st hm hF (o := o) (q := q) (by omega) (by omega) x
  exact ⟨h1, h2, (w_wr hF (by omega) _ (Or.inr ⟨ho, h⟩)).mpr hW, h5, h6⟩

end Q4

/-- A kept register after register writes. -/
macro "q4_reg" : tactic =>
  `(tactic| first | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; done) | rfl)

/-- `Q4.Rg` after register writes, from `h : Q4.Rg .. s₀`. -/
macro "q4_rg " h:term : tactic =>
  `(tactic| exact Q4.Rg.tr $h (by q4_reg) (by q4_reg) (by q4_reg))

end Kraken.Examples.Sbr.Reset

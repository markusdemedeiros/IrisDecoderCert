import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib

/-!
# `sbr_reset`: the inlined `AV_QSORT` copies, frame access

Shared by the four copies (`QS.*` of `spec/QS.py`). The array and the explicit stack of a copy
are views of the frame region `fr` (`rbp - 0x570`, `FrOk`): element `q` of the array at frame
offset `o` is `QS.av fr o q` at address `QS.ep t₀ o q`, stack entry `j` the slots
`frSlot64 fr (0x570 - 16 j)` (start) and `frSlot64 fr (0x568 - 16 j)` (end).

* Addresses: `ep_fr` (as a frame offset), `ep_toNat` (no wrap, from `0x578 ≤ rsp₀`).
* Loads / stores of elements: `av_load`, `av_store`, `av_wr` (the array after a store),
  `slot_wr32` / `slot_wr64` (frame slots elsewhere unchanged), `stk_wr` (the stack unchanged).
* Signed 16-bit comparisons: `cc_le16`, `cc_g16`, `cc_ge16`.
* The stack: `stk_load` / `stk_store` (8-byte words, `stk_addr0` / `stk_addr1` for the pop's
  addresses), `stkRel_pop` / `stkRel_push`, `stk_wr_hi` (a write above the stack), `slot_wr_same`.
* The measure: `slot64_fr` (a stack slot read from memory), `stkPhi_succ`, `stkPhi_mk`, `ep_wB`,
  `stkPhi_eq` (`stkPhi` of the stack is `phi S`).
* Register arithmetic: `qs_dec32`, `qs_shl4`, `qs_nc32`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

namespace Kraken.Examples.Sbr.Reset

/-! ## Addresses -/

/-- Element `q` as a frame offset. -/
theorem ep_fr (t₀ : MachineData) (o q : Nat) :
    QS.ep t₀ o q = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (o + 2 * (q + 1)) := by
  simp only [QS.ep, QS.pA, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The address of element `q` as a number (no wrap below `rsp₀`). -/
theorem ep_toNat {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o q : Nat}
    (h : o + 2 * (q + 1) ≤ 0x548) :
    (QS.ep t₀ o q).toNat = (t₀.regs.get64 .rsp).toNat - 0x578 + (o + 2 * (q + 1)) := by
  rw [ep_fr, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := (t₀.regs.get64 .rsp).isLt
  omega

/-- The end pointer `ep hi1 - 2` is the address of element `hi1 - 1`. -/
theorem ep_sub2 (t₀ : MachineData) (o hi1 : Nat) (h : 1 ≤ hi1) :
    QS.ep t₀ o hi1 - 2#64 = QS.ep t₀ o (hi1 - 1) := by
  simp only [QS.ep]
  rw [show 2 * hi1 = 2 * (hi1 - 1) + 2 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The end pointer as a number. -/
theorem epm2_toNat {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o hi1 : Nat}
    (h : o + 2 * (hi1 + 1) ≤ 0x548) :
    (QS.ep t₀ o hi1 - 2#64).toNat = (t₀.regs.get64 .rsp).toNat - 0x578 + (o + 2 * hi1) := by
  have := ep_toNat hR h
  rw [BitVec.toNat_sub, this]; simp only [BitVec.toNat_ofNat]; omega

/-- `p - 2` as a number. -/
theorem sub2_toNat (x : BitVec 64) (h : 2 ≤ x.toNat) :
    (x + 18446744073709551614#64).toNat = x.toNat - 2 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

theorem ep_sub4 (t₀ : MachineData) (o hi1 : Nat) (h : 2 ≤ hi1) :
    QS.ep t₀ o hi1 - 2#64 + 18446744073709551614#64 = QS.ep t₀ o (hi1 - 2) := by
  have e : (18446744073709551614#64 : BitVec 64) = -2#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, ep_sub2 t₀ o hi1 (by omega), ep_sub2 t₀ o (hi1 - 1) (by omega)]
  rfl

/-- `ep lo + 2 m` is element `lo + m`. -/
theorem ep_add (t₀ : MachineData) (o lo m : Nat) :
    QS.ep t₀ o lo + BitVec.ofNat 64 m * 2#64 = QS.ep t₀ o (lo + m) := by
  simp only [QS.ep]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- Half the byte distance `end - start`, in elements (`sar $2`). -/
theorem ep_half {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o lo hi1 : Nat}
    (hl : lo + 1 ≤ hi1) (h : o + 2 * (hi1 + 1) ≤ 0x548) :
    (QS.ep t₀ o hi1 - 2#64 - QS.ep t₀ o lo).sshiftRight 2 = BitVec.ofNat 64 ((hi1 - 1 - lo) / 2)
      := by
  have e1 : QS.ep t₀ o hi1 - 2#64 - QS.ep t₀ o lo = BitVec.ofNat 64 (2 * (hi1 - 1 - lo)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, epm2_toNat hR h, ep_toNat hR (by omega), BitVec.toNat_ofNat]; omega
  rw [e1, BitVec.sshiftRight_eq_of_msb_false (by simp [BitVec.msb_eq_decide]; omega)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

/-! ## Values -/

/-- A 16-bit value read back from its two bytes. -/
theorem ofInt16_bytes (x : BitVec 16) :
    BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 x.toInt)) = x := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_toInt]

/-- `toInt` of a value in the `int16` range. -/
theorem toInt_ofInt16 {v : Int} (h1 : -2 ^ 15 ≤ v) (h2 : v < 2 ^ 15) :
    (BitVec.ofInt 16 v).toInt = v := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod_def]; split <;> omega

/-- An element is in the `int16` range. -/
theorem av_ofInt (fr : List UInt8) (o q : Nat) :
    BitVec.ofInt 16 (QS.av fr o q) = BitVec.ofInt 16 (Int.ofBytes (slice fr (o + 2 * (q + 1)) 2))
      := by
  simp only [QS.av, A2.fv, BitVec.ofInt_toInt]

/-! ## Signed 16-bit comparisons -/

theorem cc_le16 (a b : BitVec 16) (cf af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (a.toInt ≤ b.toInt) := by
  rw [CondCode.interp_le_cmp, BitVec.sle_eq_decide]

theorem cc_g16 (a b : BitVec 16) (cf af : Bool) :
    CondCode.g.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt < a.toInt) := by
  rw [CondCode.interp_g_cmp, BitVec.slt_eq_decide]

theorem cc_ge16 (a b : BitVec 16) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt ≤ a.toInt) := by
  rw [CondCode.interp_ge_cmp, BitVec.slt_eq_decide]
  by_cases h : a.toInt < b.toInt <;> simp [h] <;> omega

/-- `test ecx, ecx` on a small count: zero iff the count is. -/
theorem cc_z_test32 (n : Nat) (h : n < 2 ^ 32) (af : Bool) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 n) &&& BitVec.setWidth 32 (BitVec.ofNat 64 n))
      { cf := false, af := af, of := false }) = decide (n = 0) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self]
  by_cases h0 : n = 0
  · subst h0; rfl
  · have : BitVec.setWidth 32 (BitVec.ofNat 64 n) ≠ BitVec.zero 32 := fun e => h0 (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
      simp at this; omega)
    rw [show decide (n = 0) = false from by simp [h0]]
    exact beq_eq_false_iff_ne.mpr this

/-! ## Frame slices -/

section Slices

variable {fr : List UInt8}

/-- An element after a store to element `q`. -/
theorem av_wr (hF : FrOk fr) {o q : Nat} (h : o + 2 * (q + 1) + 2 ≤ 0x548) (x : BitVec 16)
    (r : Nat) :
    QS.av (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 x.toInt)) o r
      = Parse.Qsort.upd (QS.av fr o) q x.toInt r := by
  simp only [QS.av, A2.fv, Parse.Qsort.upd]
  split
  · subst_vars
    rw [slice_wr_toBytes hF h, ofInt16_bytes]
  · rw [slice_wr_other hF h _ (by omega)]

/-- A frame slot below `0x548` away from a write. -/
theorem slot_wr32 (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int) {d : Nat}
    (hd : o + n ≤ rb d ∨ rb d + 4 ≤ o) :
    frSlot32 (wr fr o (Int.toBytes n v)) d = frSlot32 fr d := by
  simp only [frSlot32]; rw [slice_wr_other hF h v (by omega)]

theorem slot_wr64 (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int) {d : Nat}
    (hd : o + n ≤ rb d ∨ rb d + 8 ≤ o) :
    frSlot64 (wr fr o (Int.toBytes n v)) d = frSlot64 fr d := by
  simp only [frSlot64]; rw [slice_wr_other hF h v (by omega)]

/-- The stack is unchanged by a write above it. -/
theorem stk_wr (hF : FrOk fr) {o' n : Nat} (h : o' + n ≤ 0x548) (v : Int) {t₀ : MachineData}
    {o : Nat} {S : List Iv} (hS : S.length ≤ 64) (ho : 0x400 ≤ o') :
    QS.StkRel (wr fr o' (Int.toBytes n v)) t₀ o S ↔ QS.StkRel fr t₀ o S := by
  unfold QS.StkRel
  constructor
  · intro H j hj
    have := H j hj
    rwa [slot_wr64 hF h v (by simp only [rb]; omega),
      slot_wr64 hF h v (by simp only [rb]; omega)] at this
  · intro H j hj
    rw [slot_wr64 hF h v (by simp only [rb]; omega), slot_wr64 hF h v (by simp only [rb]; omega)]
    exact H j hj

/-- The array is unchanged by a write below it. -/
theorem av_wr_other (hF : FrOk fr) {o' n : Nat} (h : o' + n ≤ 0x548) (v : Int) {o : Nat}
    (ho : o' + n ≤ o + 2) (r : Nat) :
    QS.av (wr fr o' (Int.toBytes n v)) o r = QS.av fr o r := by
  simp only [QS.av, A2.fv]
  by_cases hr : o + 2 * (r + 1) + 2 ≤ 0x548
  · rw [slice_wr_other hF h v (by omega)]
  · rw [slice_wr_other hF h v (by omega)]

end Slices

/-! ## The exit: range and sum -/

theorem ssum_av (fr : List UInt8) (o : Nat) :
    ∀ n, A2.ssum (A2.fv fr o) n = sumTo (QS.av fr o) n
  | 0 => rfl
  | n + 1 => by rw [A2.ssum, sumTo, ssum_av fr o n]

/-- At the end of a sort (no pending interval): the array is an `Arr`. -/
theorem arr_of_qw {fr : List UInt8} {o N : Nat} {A0 : Nat → Int} {B tot : Int}
    (hAB : QS.AB N A0 B tot) (hQ : QW N (QS.av fr o) A0 []) : A2.Arr fr o N B tot := by
  refine ⟨A2.fv fr o, fun i h1 h2 => ⟨rfl, ?_⟩, ?_⟩
  · have := hQ.2.bounds (P := fun v => -B ≤ v ∧ v ≤ B) hAB.1 (i - 1) (by omega)
    simp only [QS.av, show i - 1 + 1 = i by omega] at this
    exact this
  · rw [ssum_av, hQ.2.sum, hAB.2]

variable [CodeEnv]

/-! ## Loads and stores -/

section Mem

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

/-- A load of element `q`. -/
theorem av_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o q : Nat}
    (h : o + 2 * (q + 1) + 2 ≤ 0x548) :
    m.loadInt (QS.ep t₀ o q) 2 = some (Int.ofBytes (slice fr (o + 2 * (q + 1)) 2)) :=
  region_load (focus (Mm_fr ..) hm) (ep_fr ..) (by rw [hF]; omega) (by rw [hF]; decide)

/-- A store to element `q`. -/
theorem av_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o q : Nat}
    (h : o + 2 * (q + 1) + 2 ≤ 0x548) (v : Int) :
    m.storeInt (QS.ep t₀ o q) 2 v
      =⋆ Mm k e a ra t₀ st (wr fr (o + 2 * (q + 1)) (Int.toBytes 2 v)) :=
  Mm_upd_fr .. ▸ region_store (focus (Mm_fr ..) hm) (ep_fr ..) (by rw [hF]; omega)
    (by rw [hF]; decide) v

/-- An 8-byte load at frame offset `o` (a stack word). -/
theorem stk_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o : Nat} (h : o + 8 ≤ 0x548)
    {addr : BitVec 64} (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 o) :
    m.loadInt addr 8 = some (Int.ofBytes (slice fr o 8)) :=
  region_load (focus (Mm_fr ..) hm) ha (by rw [hF]; omega) (by rw [hF]; decide)

/-- An 8-byte store at frame offset `o` (a stack word). -/
theorem stk_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o : Nat} (h : o + 8 ≤ 0x548)
    {addr : BitVec 64} (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 o) (v : Int) :
    m.storeInt addr 8 v =⋆ Mm k e a ra t₀ st (wr fr o (Int.toBytes 8 v)) :=
  Mm_upd_fr .. ▸ region_store (focus (Mm_fr ..) hm) ha (by rw [hF]; omega) (by rw [hF]; decide) v

/-- A frame slot read through `rbp` (`LexVar.slot64`) is the frame view. -/
theorem slot64_fr {s : MachineData} (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    (hbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) {d : Nat} (hd : 0x30 ≤ d)
    (hd' : d ≤ 0x570) : slot64 s d = frSlot64 fr d := by
  rw [slot64_of_load (v := Int.ofBytes (slice fr (rb d) 8))]
  rw [hbp]; exact fr_load hm hF (by omega) hd'

end Mem

/-! ## The stack -/

omit [CodeEnv] in
theorem stk_addr0 (r : BitVec 64) (m : Nat) :
    r - 8#64 + BitVec.ofNat 64 (16 * m) + 18446744073709550224#64
      = r - 0x578#64 + BitVec.ofNat 64 (16 * m) := by bv_omega

omit [CodeEnv] in
theorem stk_addr1 (r : BitVec 64) (m : Nat) :
    r - 8#64 + BitVec.ofNat 64 (16 * m) + 18446744073709550232#64
      = r - 0x578#64 + BitVec.ofNat 64 (16 * m + 8) := by bv_omega

omit [CodeEnv] in
/-- A frame slot read back after an 8-byte store to it. -/
theorem slot_wr_same {fr : List UInt8} (hF : FrOk fr) {o d : Nat} (h : o + 8 ≤ 0x548)
    (hd : rb d = o) (v : Int) : frSlot64 (wr fr o (Int.toBytes 8 v)) d = BitVec.ofInt 64 v := by
  simp only [frSlot64]; rw [hd, slice_wr_toBytes hF h, BitVec.ofInt64_ofBytes_toBytes8]

omit [CodeEnv] in
theorem stkRel_pop {fr : List UInt8} {t₀ : MachineData} {o : Nat} {S : List Iv} {I : Iv}
    (h : QS.StkRel fr t₀ o (S ++ [I])) : QS.StkRel fr t₀ o S
      ∧ frSlot64 fr (0x570 - 16 * S.length) = QS.ep t₀ o I.1
      ∧ frSlot64 fr (0x568 - 16 * S.length) = QS.ep t₀ o I.2 - 2#64 := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · have := h S.length (by simp)
    simpa using this

omit [CodeEnv] in
theorem stkRel_push {fr : List UInt8} {t₀ : MachineData} {o : Nat} {S : List Iv} {I : Iv}
    (h : QS.StkRel fr t₀ o S) (h1 : frSlot64 fr (0x570 - 16 * S.length) = QS.ep t₀ o I.1)
    (h2 : frSlot64 fr (0x568 - 16 * S.length) = QS.ep t₀ o I.2 - 2#64) :
    QS.StkRel fr t₀ o (S ++ [I]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  by_cases e : j < S.length
  · rw [List.getElem_append_left e]; exact h j e
  · obtain rfl : j = S.length := by omega
    simpa using And.intro h1 h2

omit [CodeEnv] in
/-- The stack `S` is unchanged by a write at or above entry `|S|`. -/
theorem stk_wr_hi {fr : List UInt8} (hF : FrOk fr) {o' n : Nat} (h : o' + n ≤ 0x548) (v : Int)
    {t₀ : MachineData} {o : Nat} {S : List Iv} (ho : 16 * S.length ≤ o') :
    QS.StkRel (wr fr o' (Int.toBytes n v)) t₀ o S ↔ QS.StkRel fr t₀ o S := by
  unfold QS.StkRel
  constructor
  · intro H j hj
    have := H j hj
    rwa [slot_wr64 hF h v (by simp only [rb]; omega),
      slot_wr64 hF h v (by simp only [rb]; omega)] at this
  · intro H j hj
    rw [slot_wr64 hF h v (by simp only [rb]; omega), slot_wr64 hF h v (by simp only [rb]; omega)]
    exact H j hj

/-! ## The measure -/

omit [CodeEnv] in
theorem stkPhi_succ (s : MachineData) (n : Nat) :
    QS.stkPhi s (n + 1) = QS.stkPhi s n + wBn 2 (slot64 s (0x570 - 16 * n)).toNat
      (slot64 s (0x568 - 16 * n)).toNat := by
  simp [QS.stkPhi, List.range_succ, List.map_append, List.sum_append]

omit [CodeEnv] in
/-- `stkPhi` reads only memory and `rbp`. -/
theorem stkPhi_mk (s : MachineData) (R : Reg64s) (z) (st) (hb : R.get64 .rbp = s.regs.get64 .rbp)
    (n : Nat) : QS.stkPhi { regs := R, zmms := z, status := st, dmem := s.dmem } n
      = QS.stkPhi s n := by
  unfold QS.stkPhi slot64; simp only [hb]

omit [CodeEnv] in
/-- The byte weight of an interval given by its pointers. -/
theorem ep_wB {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o lo hi1 : Nat}
    (hl : lo ≤ hi1) (h : o + 2 * (hi1 + 1) ≤ 0x548) :
    wBn 2 (QS.ep t₀ o lo).toNat (QS.ep t₀ o hi1 - 2#64).toNat = wt (lo, hi1) := by
  have e1 := ep_toNat hR (o := o) (q := lo) (by omega)
  have e2 := ep_toNat hR (o := o) (q := hi1) h
  have e3 : (QS.ep t₀ o hi1 - 2#64).toNat = (QS.ep t₀ o hi1).toNat - 2 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  rw [e3, e1, e2]; unfold wBn wt; simp only
  split <;> omega

omit [CodeEnv] in
theorem phiI_eq {t₀ : MachineData} (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat) {o lo hi1 : Nat}
    (hl : lo ≤ hi1) (h : o + 2 * (hi1 + 1) ≤ 0x548) :
    wBn 2 (QS.ep t₀ o lo).toNat (QS.ep t₀ o hi1 - 2#64).toNat = phi [(lo, hi1)] := by
  rw [phi_one, ep_wB hR hl h]

section Phi

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8}

theorem stkPhi_take {s : MachineData} (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    (hbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat)
    {o N : Nat} (hoN : o + 2 * (N + 1) ≤ 0x548) {S : List Iv} (hS : QS.StkRel fr t₀ o S)
    (hW : Within N S) (hn : S.length ≤ 64) :
    ∀ n, n ≤ S.length → QS.stkPhi s n = phi (S.take n) := by
  intro n
  induction n with
  | zero => intro _; simp [QS.stkPhi, phi]
  | succ n ih =>
    intro hn1
    obtain ⟨r1, r2⟩ := hS n (by omega)
    have hw := hW S[n] (List.getElem_mem _)
    rw [stkPhi_succ, ih (by omega), slot64_fr hm hF hbp (by omega) (by omega),
      slot64_fr hm hF hbp (by omega) (by omega), r1, r2, ep_wB hR hw.1 (by omega),
        List.take_add_one,
      List.getElem?_eq_getElem (by omega), phi_append]
    simp [phi, Option.toList]

/-- The measure read from memory is `phi` of the pending intervals. -/
theorem stkPhi_eq {s : MachineData} (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    (hbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (hR : 0x578 ≤ (t₀.regs.get64 .rsp).toNat)
    {o N : Nat} (hoN : o + 2 * (N + 1) ≤ 0x548) {S : List Iv} (hS : QS.StkRel fr t₀ o S)
    (hW : Within N S) (hn : S.length ≤ 64) : QS.stkPhi s S.length = phi S := by
  rw [stkPhi_take hm hF hbp hR hoN hS hW hn S.length (Nat.le_refl _), List.take_length]

end Phi

/-- The stack need: no wrap below the frame. -/
theorem rsp_ok {a : RArgs} {t : MachineData} (hC : ResetCI a t) :
    resetStkMin ≤ (t.regs.get64 .rsp).toNat :=
  hC.rsp

omit [CodeEnv] in
/-- A variant step with an unchanged measure and a smaller phase. -/
theorem lex_phase {x a b p q d : Nat} (h : a = b) (hp : p % 2 ^ 64 < q % 2 ^ 64) :
    lex [x, a, p, d] ≤ lex [x, b, q, d] := by
  subst h; exact lex_cons_le_cons rfl (lex_cons_le_cons rfl (lex_cons_le_of_lt rfl hp))

omit [CodeEnv] in
/-- A variant step with a smaller measure. -/
theorem lex_head_lt {x a b p q d : Nat} (h : a < b) (hb : b < 2 ^ 64) :
    lex [x, a, p, d] < lex [x, b, q, d] := by
  refine lex_cons_lt_cons rfl (lex_cons_lt_of_lt rfl ?_)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]; exact h

/-! ## Register arithmetic -/

omit [CodeEnv] in
theorem qs_dec32 (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) - 1#32) = BitVec.ofNat 64 (n - 1)
      := by
  apply BitVec.eq_of_toNat_eq; simp; omega

omit [CodeEnv] in
theorem qs_shl4 (m : Nat) : BitVec.ofNat 64 m <<< 4 = BitVec.ofNat 64 (16 * m) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

omit [CodeEnv] in
theorem qs_nc32 (n c : Nat) (hn : n < 2 ^ 31) (hc : c < 2 ^ 31) (af ofl : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64 c))
      { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 n) - BitVec.setWidth 32 (BitVec.ofNat 64
        c)).unsigned
            != (BitVec.setWidth 32 (BitVec.ofNat 64 n)).unsigned
              - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned, af := af, of := ofl })
      = decide (c ≤ n) := by
  rw [cc_nc_sub _ _ _ _]; simp; omega

end Kraken.Examples.Sbr.Reset

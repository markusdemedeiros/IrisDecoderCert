import Kraken.X64.Examples.Sbr.Parse.TlimSpec
import Kraken.Rules.IntMisc
import Kraken.Rules.CallFrame
import Kraken.Rules.CfgList
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.Rules.SepStep

/-!
# `sbr_make_f_tablelim`: helpers

* Arrays of `uint16_t` and of 8-byte words held in one `List UInt8` cell, accessed at a
  variable index through `loadInt_slice`/`storeInt_slice` (no case split on the index): the
  element `q` read as `u16 l q` / `w8 l q`, a store as `setW2`/`setW8`.
* The flags of a 16-bit `cmp` between values below `2 ^ 15` (the code compares the table
  entries as `int16_t`) and of 64-bit unsigned `cmp`s, as orders of the values.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Tlim

/-! ## Little-endian elements of a byte list -/

theorem ofBytes_two (a b : UInt8) : Int.ofBytes [a, b] = (a.toNat + 256 * b.toNat : Nat) := by
  simp only [Int.ofBytes, List.foldr_cons, List.foldr_nil]; omega

theorem slice2 (l : List UInt8) (q : Nat) (h : 2 * q + 2 ≤ l.length) :
    (l.drop (2 * q)).take 2 = [l.getD (2 * q) 0, l.getD (2 * q + 1) 0] := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]; omega
  · intro i h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp [List.getElem?_eq_getElem (show 2 * q < l.length by omega)]
    · simp [List.getElem?_eq_getElem (show 2 * q + 1 < l.length by omega)]

/-- Element `q` of a `uint16_t` array, read whole. -/
theorem ofBytes_slice2 (l : List UInt8) (q : Nat) (h : 2 * q + 2 ≤ l.length) :
    Int.ofBytes ((l.drop (2 * q)).take 2) = (u16 l q : Int) := by
  rw [slice2 l q h, ofBytes_two]

theorem u16_lt (l : List UInt8) (q : Nat) : u16 l q < 65536 := by
  unfold u16 u8
  have := (l.getD (2 * q) 0).toNat_lt; have := (l.getD (2 * q + 1) 0).toNat_lt
  omega

/-- A store of `v` into element `q`. -/
def setW2 (l : List UInt8) (q : Nat) (v : Int) : List UInt8 :=
  l.take (2 * q) ++ Int.toBytes 2 v ++ l.drop (2 * q + 2)

theorem setW2_length (l : List UInt8) (q : Nat) (v : Int) (h : 2 * q + 2 ≤ l.length) :
    (setW2 l q v).length = l.length := by
  simp only [setW2, List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
  omega

theorem getD_setW2 (l : List UInt8) (q : Nat) (v : Int) (h : 2 * q + 2 ≤ l.length) (i : Nat) :
    (setW2 l q v).getD i 0 =
      if i = 2 * q then (Int.toBytes 2 v).getD 0 0
      else if i = 2 * q + 1 then (Int.toBytes 2 v).getD 1 0 else l.getD i 0 := by
  simp only [setW2, List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases h1 : i < 2 * q
  · rw [List.getElem?_append_left (by simp only [List.length_take]; omega)]
    simp only [List.getElem?_take, h1, ↓reduceIte, show i ≠ 2 * q by omega,
      show i ≠ 2 * q + 1 by omega]
  · rw [List.getElem?_append_right (by simp only [List.length_take]; omega)]
    simp only [List.length_take, show min (2 * q) l.length = 2 * q by omega]
    by_cases h2 : i < 2 * q + 2
    · rw [List.getElem?_append_left (by simp only [Int.toBytes_length]; omega)]
      rcases (by omega : i = 2 * q ∨ i = 2 * q + 1) with rfl | rfl
      · simp
      · simp only [show 2 * q + 1 - 2 * q = 1 by omega, show 2 * q + 1 ≠ 2 * q by omega,
          ↓reduceIte]
    · rw [List.getElem?_append_right (by simp only [Int.toBytes_length]; omega)]
      simp only [Int.toBytes_length, List.getElem?_drop, show i ≠ 2 * q by omega,
        show i ≠ 2 * q + 1 by omega, ↓reduceIte]
      congr 2; omega

theorem toBytes2_val (v : Int) :
    ((Int.toBytes 2 v).getD 0 0).toNat + 256 * ((Int.toBytes 2 v).getD 1 0).toNat
      = (v % 65536).toNat := by
  simp only [Int.toBytes, List.getD_cons_zero, List.getD_cons_succ, Int.take]
  simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
  omega

theorem u16_setW2 (l : List UInt8) (q : Nat) (v : Int) (h : 2 * q + 2 ≤ l.length) (r : Nat) :
    u16 (setW2 l q v) r = if r = q then (v % 65536).toNat else u16 l r := by
  unfold u16 u8
  rw [getD_setW2 l q v h, getD_setW2 l q v h]
  by_cases hr : r = q
  · subst hr; simp only [↓reduceIte, show 2 * r + 1 ≠ 2 * r by omega]; exact toBytes2_val v
  · simp only [hr, ↓reduceIte, show 2 * r ≠ 2 * q by omega, show 2 * r ≠ 2 * q + 1 by omega,
      show 2 * r + 1 ≠ 2 * q by omega, show 2 * r + 1 ≠ 2 * q + 1 by omega]

/-! ## 8-byte words (the `AV_QSORT` stack) -/

/-- Word `j` of a byte list. -/
def w8 (l : List UInt8) (j : Nat) : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes ((l.drop (8 * j)).take 8))

/-- A store of `v` into word `j`. -/
def setW8 (l : List UInt8) (j : Nat) (v : Int) : List UInt8 :=
  l.take (8 * j) ++ Int.toBytes 8 v ++ l.drop (8 * j + 8)

theorem setW8_length (l : List UInt8) (j : Nat) (v : Int) (h : 8 * j + 8 ≤ l.length) :
    (setW8 l j v).length = l.length := by
  simp only [setW8, List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
  omega

theorem w8_setW8 (l : List UInt8) (j : Nat) (v : BitVec 64) (h : 8 * j + 8 ≤ l.length) (i : Nat) :
    w8 (setW8 l j v.toInt) i = if i = j then v else w8 l i := by
  unfold w8 setW8
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, List.append_assoc]
    rw [List.drop_left' (by simp only [List.length_take]; omega),
      List.take_left' (Int.toBytes_length 8 _)]
    exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl v
  · simp only [hij, ↓reduceIte]
    congr 2
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_take, List.getElem?_drop, List.append_assoc]
    split
    · rename_i hk
      by_cases h1 : 8 * i + k < 8 * j
      · rw [List.getElem?_append_left (by simp only [List.length_take]; omega)]
        simp only [List.getElem?_take, h1, ↓reduceIte]
      · have h2 : 8 * j + 8 ≤ 8 * i + k := by omega
        rw [List.getElem?_append_right (by simp only [List.length_take]; omega),
          List.getElem?_append_right (by simp only [List.length_take, Int.toBytes_length]; omega)]
        simp only [List.length_take, Int.toBytes_length, List.getElem?_drop]
        congr 1; omega
    · rfl

/-! ## Loads and stores at a variable index -/

theorem ofNat_toNat_small (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; omega

/-- A 2-byte load of element `q` of the `uint16_t` array at `p`. -/
theorem ld16 {m : Mem 64} {l : List UInt8} {p addr : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ p ⋆ F) (q : Nat) (ha : addr = p + BitVec.ofNat 64 (2 * q))
    (hq : 2 * q + 2 ≤ l.length) (hl : l.length < 2 ^ 32) :
    m.loadInt addr 2 = some (u16 l q : Int) := by
  have e : (addr - p).toNat = 2 * q := by
    rw [ha, BitVec.add_comm, BitVec.add_sub_cancel, ofNat_toNat_small _ (by omega)]
  rw [loadInt_slice h (by rw [e]; omega) (by omega), e, ofBytes_slice2 l q hq]

/-- A 2-byte store into element `q`. -/
theorem st16 {m : Mem 64} {l : List UInt8} {p addr : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ p ⋆ F) (q : Nat) (ha : addr = p + BitVec.ofNat 64 (2 * q))
    (hq : 2 * q + 2 ≤ l.length) (hl : l.length < 2 ^ 32) (v : Int) :
    m.storeInt addr 2 v =⋆ setW2 l q v =@ p ⋆ F := by
  have e : (addr - p).toNat = 2 * q := by
    rw [ha, BitVec.add_comm, BitVec.add_sub_cancel, ofNat_toNat_small _ (by omega)]
  have := storeInt_slice h (by rw [e]; omega) (by omega) v
  rw [e] at this
  exact this

/-- An 8-byte load of word `j` of the list at `p`. -/
theorem ld64 {m : Mem 64} {l : List UInt8} {p addr : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ p ⋆ F) (j : Nat) (ha : addr = p + BitVec.ofNat 64 (8 * j))
    (hj : 8 * j + 8 ≤ l.length) (hl : l.length < 2 ^ 32) :
    ∃ v, m.loadInt addr 8 = some v ∧ BitVec.ofInt 64 v = w8 l j := by
  have e : (addr - p).toNat = 8 * j := by
    rw [ha, BitVec.add_comm, BitVec.add_sub_cancel, ofNat_toNat_small _ (by omega)]
  exact ⟨_, by rw [loadInt_slice h (by rw [e]; omega) (by omega), e], rfl⟩

/-- An 8-byte store into word `j`. -/
theorem st64 {m : Mem 64} {l : List UInt8} {p addr : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ p ⋆ F) (j : Nat) (ha : addr = p + BitVec.ofNat 64 (8 * j))
    (hj : 8 * j + 8 ≤ l.length) (hl : l.length < 2 ^ 32) (v : Int) :
    m.storeInt addr 8 v =⋆ setW8 l j v =@ p ⋆ F := by
  have e : (addr - p).toNat = 8 * j := by
    rw [ha, BitVec.add_comm, BitVec.add_sub_cancel, ofNat_toNat_small _ (by omega)]
  have := storeInt_slice h (by rw [e]; omega) (by omega) v
  rw [e] at this
  exact this

/-! ## Flags -/

/-- The 16-bit view of a loaded `uint16_t` kept in a 64-bit register. -/
theorem sw16 (x : Int) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 x)))
      = BitVec.ofInt 16 x := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem ofInt16_nat (n : Nat) : BitVec.ofInt 16 (n : Int) = BitVec.ofNat 16 n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem toInt16_small (n : Nat) (h : n < 2 ^ 15) : (BitVec.ofNat 16 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_ofNat]; omega
  · simp [BitVec.msb_eq_decide]; omega

theorem cc16_le (a b : Nat) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (cf af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.ofNat 16 a - BitVec.ofNat 16 b)
      { cf := cf, af := af, of := (BitVec.ofNat 16 a - BitVec.ofNat 16 b).signed
          != (BitVec.ofNat 16 a).signed - (BitVec.ofNat 16 b).signed }) = decide (a ≤ b) := by
  rw [CondCode.interp_le_cmp _ _ _ _ (by decide), BitVec.sle_eq_decide, toInt16_small a ha,
    toInt16_small b hb]
  simp

theorem cc16_g (a b : Nat) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (cf af : Bool) :
    CondCode.g.interp (StatusFlags.from_result (BitVec.ofNat 16 a - BitVec.ofNat 16 b)
      { cf := cf, af := af, of := (BitVec.ofNat 16 a - BitVec.ofNat 16 b).signed
          != (BitVec.ofNat 16 a).signed - (BitVec.ofNat 16 b).signed }) = decide (b < a) := by
  rw [CondCode.interp_g_cmp _ _ _ _ (by decide), BitVec.slt_eq_decide, toInt16_small a ha,
    toInt16_small b hb]
  simp

theorem cc16_ge (a b : Nat) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (BitVec.ofNat 16 a - BitVec.ofNat 16 b)
      { cf := cf, af := af, of := (BitVec.ofNat 16 a - BitVec.ofNat 16 b).signed
          != (BitVec.ofNat 16 a).signed - (BitVec.ofNat 16 b).signed }) = decide (b ≤ a) := by
  rw [CondCode.interp_ge_cmp _ _ _ _ (by decide), BitVec.slt_eq_decide, toInt16_small a ha,
    toInt16_small b hb]
  by_cases h : a < b <;> simp [h] <;> omega

theorem cc16_z (a b : Nat) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 16 a - BitVec.ofNat 16 b) f)
      = decide (a = b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result_sub]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 16 a ≠ BitVec.ofNat 16 b := fun e => h (by
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)
    simp [this, h]

theorem cc_nc_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.unsigned_eq]
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]; simp [h]; omega
  · rw [h₂ (by omega)]; simp [h]; omega

theorem cc_c_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  have := cc_nc_sub a b f hf
  rw [CondCode.interp_nc] at this
  rw [CondCode.interp_c]
  revert this
  cases (StatusFlags.from_result (a - b) f).cf <;> simp <;> omega

end Kraken.Examples.Sbr.Tlim

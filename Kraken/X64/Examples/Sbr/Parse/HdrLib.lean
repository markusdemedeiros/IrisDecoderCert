import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# Helpers for the `read_sbr_header` / `read_sbr_invf` proofs

* Byte regions (`l =@ a`): a load or store at a constant offset, through `loadInt_slice` /
  `storeInt_slice`; a 1-byte store is a `List.set`.
* The bit reader's index update: the carry flag of `cmp` and the clamp of `cmovb`.
* Byte round trips of the values the code loads and stores back.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP

namespace Kraken.Examples.Sbr.HdrLib

open Kraken.Examples.Sbr.ParseModel (mk old)

/-! ## Byte regions -/

theorem val_load {m : Mem 64} {l : List UInt8} {a : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ a ⋆ F) (o n : Nat) (hin : o + n ≤ l.length) (hl : l.length < 2 ^ 32) :
    m.loadInt (a + BitVec.ofNat 64 o) n = some (Int.ofBytes ((l.drop o).take n)) := by
  have e : (a + BitVec.ofNat 64 o - a).toNat = o := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have := loadInt_slice (addr := a + BitVec.ofNat 64 o) (n := n) h (by rw [e]; exact hin)
    (by omega)
  rw [e] at this; exact this

theorem val_store {m : Mem 64} {l : List UInt8} {a : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ a ⋆ F) (o n : Nat) (hin : o + n ≤ l.length) (hl : l.length < 2 ^ 32)
    (v : Int) :
    m.storeInt (a + BitVec.ofNat 64 o) n v
      =⋆ (l.take o ++ Int.toBytes n v ++ l.drop (o + n)) =@ a ⋆ F := by
  have e : (a + BitVec.ofNat 64 o - a).toNat = o := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have := storeInt_slice (addr := a + BitVec.ofNat 64 o) (n := n) h (by rw [e]; exact hin)
    (by omega) v
  rw [e] at this; exact this

/-- A 1-byte store is a `List.set`. -/
theorem toBytes1 (v : Int) : Int.toBytes 1 v = [UInt8.ofBitVec (BitVec.ofInt 8 v)] := by
  simp only [Int.toBytes, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  simp only [Int.take, Nat.toUInt8, UInt8.toNat_ofBitVec, BitVec.toNat_ofInt]
  simp [UInt8.toNat_ofNat']
  omega

/-- A 1-byte store is a `List.set`. -/
theorem slice1_set (l : List UInt8) (o : Nat) (v : Int) (ho : o < l.length) :
    l.take o ++ Int.toBytes 1 v ++ l.drop (o + 1) = l.set o (UInt8.ofBitVec (BitVec.ofInt 8 v)) := by
  simp only [List.set_eq_take_append_cons_drop, ho, ↓reduceIte, toBytes1, List.append_assoc,
    List.cons_append, List.nil_append]

theorem mk_length (k : Nat) (f : Nat → UInt8) : (mk k f).length = k := by
  simp [mk]

theorem mk_getD (k : Nat) (f : Nat → UInt8) (j : Nat) :
    (mk k f).getD j 0 = if j < k then f j else 0 := by
  simp only [mk, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · simp [*]
  · simp [*]

theorem mk_set (n k : Nat) (f : Nat → UInt8) (b : UInt8) :
    (mk n f).set k b = mk n (fun j => if j = k then b else f j) := by
  unfold mk; apply List.ext_getElem
  · simp
  · intro j h1 h2; simp only [List.getElem_set, List.getElem_map, List.getElem_range]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]


theorem cf_sub (a b : BitVec 32) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, BitVec.unsigned, BitVec.toNat_sub, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, BitVec.unsigned, BitVec.toNat_sub, bne_eq_false_iff_eq]; omega

/-- The reader's index after `get_bits(n)`: `min(index + n, size_in_bits_plus8)`. -/
theorem clamp (i p : BitVec 32) (n : Nat) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31)
    (hn : n < 32) :
    i.toNat ≤ (if p.toNat < (BitVec.ofNat 32 n + i).toNat then p else BitVec.ofNat 32 n + i).toNat
    ∧ (if p.toNat < (BitVec.ofNat 32 n + i).toNat then p else BitVec.ofNat 32 n + i).toNat
      ≤ p.toNat := by
  split
  · omega
  · rename_i h; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢; omega

theorem toBytes4_ofBytes (bs : List UInt8) (h : 4 ≤ bs.length) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs.take 4 :=
  UInt32.toBytes_ofBytes bs h

theorem toBytes1_ofBytes (bs : List UInt8) (h : 1 ≤ bs.length) :
    Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes bs)).toInt = bs.take 1 :=
  UInt8.toBytes_ofBytes bs h

theorem list10 (l : List UInt8) (h : l.length = 10) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl⟩

theorem shr30_lt (v : BitVec 32) : (v.ushiftRight 30).toNat < 4 := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]; have := v.isLt; omega

theorem rd_off (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    ((i.ushiftRight 3).setWidth 64).toNat + 4 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

end Kraken.Examples.Sbr.HdrLib

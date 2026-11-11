import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# Byte regions, adjacent cells, and small flag facts

Lemmas shared by the parser proofs (lifted from the `read_sbr_header` / `read_sbr_invf` proofs).

* Byte regions (`l =@ a`): a load or store at a constant offset (`val_load`, `val_store`), a
  load of the whole region (`val_load0`), a 1-byte store as a `List.set` (`slice1_set`), a store
  of a whole raw slot (`slot_set`), a region forgotten into a raw slot (`fg`).
* Two adjacent 4-byte cells as one 8-byte region (`cell44`, `cell44_store`, `cell44_ok`).
* Byte round trips (`toBytes1`, `toBytes1_ofBytes`, `toBytes4_ofBytes`) and `mk` lists.
* Flags and registers: `cf_sub`, `zf_sub`, `setl_val`, `low8`, `low16`, `and1_lt`,
  `or_xor_zero`; the bit reader's index update (`clamp`, `bit_idx`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP Kraken.Examples.Sbr

namespace Kraken.Examples.Sbr.Parse

open Kraken.Examples.Sbr.ParseModel (mk)

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

/-- A load of a whole byte region. -/
theorem val_load0 {m : Mem 64} {a : BitVec 64} {l : List UInt8} {F : Mem 64 → Prop}
    (h : m =⋆ (l =@ a) ⋆ F) (hl : l.length < 2 ^ 32) :
    m.loadInt a l.length = some (Int.ofBytes l) :=
  loadInt_sep _ _ _ F m h rfl (by omega)

theorem val_ok0 {m : Mem 64} {a : BitVec 64} {l : List UInt8} {F : Mem 64 → Prop}
    (h : m =⋆ (l =@ a) ⋆ F) (hl : l.length < 2 ^ 32) : (m.loadInt a l.length).isSome = true := by
  rw [val_load0 h hl]; rfl

/-- A store of the whole of a raw slot. -/
theorem slot_set {m : Mem 64} {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop}
    (h : m =⋆ n ?@ a ⋆ F) (v : Int) : m.storeInt a n v =⋆ (Int.toBytes n v =@ a) ⋆ F := by
  obtain ⟨_, bs, hlen, h'⟩ := Block.sep_elim h
  exact storeInt_sep a n bs F m ⟨h', hlen⟩ v

/-- A byte region forgotten into a raw slot. -/
theorem fg {m : Mem 64} {bs : List UInt8} {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop}
    (hl : bs.length = n) (hn : n ≤ 8) (h : m =⋆ (bs =@ a) ⋆ F) : m =⋆ (n ?@ a) ⋆ F :=
  Block.sep_intro hl (by omega) h

/-- A 1-byte value as a byte. -/
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

/-! ## Adjacent cells -/

/-- Two adjacent 4-byte cells as one 8-byte region. -/
theorem cell44 (a : BitVec 64) (u w : BitVec 32) :
    (cell4 a u ⋆ cell4 (a + 4#64) w : Mem 64 → Prop)
      = (Int.toBytes 4 u.toInt ++ Int.toBytes 4 w.toInt) =@ a := by
  simp only [cell4, Val]
  rw [At_append_sep _ _ _ (by simp [Int.toBytes_length]), Int.toBytes_length]

/-- An 8-byte store over two adjacent 4-byte cells. -/
theorem cell44_store {m : Mem 64} {a : BitVec 64} {u w : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ cell4 a u ⋆ (cell4 (a + 4#64) w ⋆ F)) (lo hi : BitVec 32) (V : Int)
    (hV : Int.toBytes 8 V = Int.toBytes 4 lo.toInt ++ Int.toBytes 4 hi.toInt) :
    m.storeInt a 8 V =⋆ cell4 a lo ⋆ (cell4 (a + 4#64) hi ⋆ F) := by
  rw [← Std.ExtHashMap.sep_assoc, cell44] at h ⊢
  have := storeInt_sep a 8 _ F m ⟨h, by simp [Int.toBytes_length]⟩ V
  rw [hV] at this
  exact this

theorem cell44_ok {m : Mem 64} {a : BitVec 64} {u w : BitVec 32} {F : Mem 64 → Prop}
    (h : m =⋆ cell4 a u ⋆ (cell4 (a + 4#64) w ⋆ F)) : (m.loadInt a 8).isSome = true := by
  rw [← Std.ExtHashMap.sep_assoc, cell44] at h
  have := val_ok0 h (by simp [Int.toBytes_length])
  simp only [List.length_append, Int.toBytes_length] at this
  exact this

/-! ## Flags and registers -/

/-- The carry flag of a 32-bit `cmp`/`sub`: unsigned `<`. -/
theorem cf_sub (a b : BitVec 32) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, BitVec.unsigned, BitVec.toNat_sub, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, BitVec.unsigned, BitVec.toNat_sub, bne_eq_false_iff_eq]; omega

/-- The zero flag of a 32-bit `cmp`/`sub`: equality. -/
theorem zf_sub (a b : BitVec 32) : (a - b == BitVec.zero 32) = true ↔ a = b := by
  rw [beq_iff_eq, show BitVec.zero 32 = 0#32 from rfl]
  constructor <;> intro h <;> bv_omega

/-- `xor r, r; …; setl r8`: the flag as a 32-bit value. -/
theorem setl_val (c : Bool) :
    BitVec.setWidth 32 ((0#64).replaceLow (BitVec.ofNat 8 c.toNat))
      = if c then 1#32 else 0#32 := by
  cases c <;> simp [BitVec.replaceLow] <;> decide

/-- A byte write into a 64-bit register, read back. -/
theorem low8 (r : BitVec 64) (b : BitVec 8) : BitVec.setWidth 8 (r.replaceLow b) = b := by
  simp only [BitVec.replaceLow]; exact BitVec.setWidth_append_eq_right

/-- A word write into a 64-bit register, read back. -/
theorem low16 (r : BitVec 64) (b : BitVec 16) : BitVec.setWidth 16 (r.replaceLow b) = b := by
  simp only [BitVec.replaceLow]; exact BitVec.setWidth_append_eq_right

theorem and1_lt (v : BitVec 32) : (v &&& 1#32).toNat < 2 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- `xor`, `xor`, `or` of a 16-bit and a 32-bit pair is zero only on equal pairs. -/
theorem or_xor_zero (A B : BitVec 16) (C D : BitVec 32)
    (h : (BitVec.setWidth 32 (A ^^^ B) ||| (C ^^^ D)) = 0#32) : A = B ∧ C = D := by
  constructor
  · ext i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero] at this
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    revert this
    cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;> cases D.getLsbD i <;>
      simp [show i < 32 by omega]
  · ext i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero] at this
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    revert this
    cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;> cases D.getLsbD i <;> simp

/-! ## The bit reader's index -/

/-- The reader's index after `get_bits(n)`: `min(index + n, size_in_bits_plus8)`. -/
theorem clamp (i p : BitVec 32) (n : Nat) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31)
    (hn : n < 32) :
    i.toNat ≤ (if p.toNat < (BitVec.ofNat 32 n + i).toNat then p else BitVec.ofNat 32 n + i).toNat
    ∧ (if p.toNat < (BitVec.ofNat 32 n + i).toNat then p else BitVec.ofNat 32 n + i).toNat
      ≤ p.toNat := by
  split
  · omega
  · rename_i h; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢; omega

/-- The index after `get_bits1`: `index + (index < size_in_bits_plus8)`. -/
theorem bit_idx (i p : BitVec 32) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    i.toNat ≤ (i + if ((i - p).msb != ((i - p).signed != i.signed - p.signed)) then 1#32 else 0#32).toNat
    ∧ (i + if ((i - p).msb != ((i - p).signed != i.signed - p.signed)) then 1#32 else 0#32).toNat
      ≤ p.toNat := by
  by_cases h : i = p
  · subst h; simp
  · have : i.toNat < p.toNat := by
      have : i.toNat ≠ p.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
      omega
    split <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

end Kraken.Examples.Sbr.Parse

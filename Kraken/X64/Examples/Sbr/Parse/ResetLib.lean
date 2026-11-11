import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# Byte regions accessed at computed offsets

A stack frame or a struct array held as one `List UInt8` cell `bs =@ a`: a load of `n` bytes
at `a + o` reads `slice bs o n`, a store writes `wr bs o (Int.toBytes n v)` (`loadInt_slice`,
`storeInt_slice` of `SeparationMem.lean`, restated at `a + o`). The offset `o` may be any term:
no case split over the positions.
-/

open Kraken Mem

namespace Kraken.Examples.Sbr.Parse

/-- The `n` bytes of `l` at offset `o`. -/
def slice (l : List UInt8) (o n : Nat) : List UInt8 := (l.drop o).take n

/-- `l` with the bytes `v` written at offset `o`. -/
def wr (l : List UInt8) (o : Nat) (v : List UInt8) : List UInt8 :=
  l.take o ++ v ++ l.drop (o + v.length)

theorem slice_length {l : List UInt8} {o n : Nat} (h : o + n ≤ l.length) :
    (slice l o n).length = n := by
  simp only [slice, List.length_take, List.length_drop]; omega

theorem wr_length {l : List UInt8} {o : Nat} {v : List UInt8} (h : o + v.length ≤ l.length) :
    (wr l o v).length = l.length := by
  simp only [wr, List.length_append, List.length_take, List.length_drop]; omega

theorem slice_wr_same {l : List UInt8} {o : Nat} {v : List UInt8}
    (h : o + v.length ≤ l.length) : slice (wr l o v) o v.length = v := by
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  simp only [slice, wr, List.append_assoc]
  rw [List.drop_left' h1, List.take_left' rfl]

theorem getElem?_wr_ne {l : List UInt8} {o : Nat} {v : List UInt8}
    (h : o + v.length ≤ l.length) {i : Nat} (hi : i < o ∨ o + v.length ≤ i) :
    (wr l o v)[i]? = l[i]? := by
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  simp only [wr, List.append_assoc]
  rcases hi with hi | hi
  · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
  · rw [List.getElem?_append_right (by omega), h1, List.getElem?_append_right (by omega),
      List.getElem?_drop]
    congr 1; omega

theorem slice_wr_disj {l : List UInt8} {o : Nat} {v : List UInt8}
    (h : o + v.length ≤ l.length) {o' n : Nat} (hd : o' + n ≤ o ∨ o + v.length ≤ o') :
    slice (wr l o v) o' n = slice l o' n := by
  apply List.ext_getElem?
  intro i
  simp only [slice, List.getElem?_take, List.getElem?_drop]
  split
  · exact getElem?_wr_ne h (by omega)
  · rfl

variable {m : Mem 64} {bs : List UInt8} {a addr : BitVec 64} {F : Mem 64 → Prop}

/-- A load of `n` bytes at offset `o` of a region reads its slice there. -/
theorem region_load (h : m =⋆ bs =@ a ⋆ F) {o n : Nat} (ho : addr = a + BitVec.ofNat 64 o)
    (hin : o + n ≤ bs.length) (hw : bs.length < 2 ^ 64) :
    m.loadInt addr n = some (Int.ofBytes (slice bs o n)) := by
  have hoff : (addr - a).toNat = o := by
    have e : addr - a = BitVec.ofNat 64 o := by subst ho; bv_omega
    rw [e, BitVec.toNat_ofNat]; omega
  have := loadInt_slice (bs := bs) (a := a) (addr := addr) (n := n) h (by omega) (by omega)
  rw [this, hoff]; rfl

/-- A store of `n` bytes at offset `o` of a region writes them into it. -/
theorem region_store (h : m =⋆ bs =@ a ⋆ F) {o n : Nat} (ho : addr = a + BitVec.ofNat 64 o)
    (hin : o + n ≤ bs.length) (hw : bs.length < 2 ^ 64) (v : Int) :
    m.storeInt addr n v =⋆ wr bs o (Int.toBytes n v) =@ a ⋆ F := by
  have hoff : (addr - a).toNat = o := by
    have e : addr - a = BitVec.ofNat 64 o := by subst ho; bv_omega
    rw [e, BitVec.toNat_ofNat]; omega
  have := storeInt_slice (bs := bs) (a := a) (addr := addr) (n := n) h (by omega) (by omega) v
  rw [hoff] at this
  rw [Val.eq]
  simpa only [wr, Int.toBytes_length] using this

end Kraken.Examples.Sbr.Parse

import Kraken.X64.Examples.Sbr.Parse.PsSpec

/-!
# `ff_ps_read_data`: byte-list cells

`*ps` (764 bytes) and the 0x78 bytes of locals are each one list cell `l =@ a`. An access of
`n` bytes at `a + o` reads `rd l o n` and a store writes `wr l o n v`, at any offset, without a
case split (`loadInt_slice`, `storeInt_slice`). The read-after-write lemmas below keep the
lists symbolic.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP

namespace Kraken.Examples.Sbr.Ps

/-- The `n` bytes at offset `o` of `l`, as an integer (little-endian, signed). -/
abbrev rd (l : List UInt8) (o n : Nat) : Int := Int.ofBytes ((l.drop o).take n)

/-- `l` with the `n` bytes of `v` written at offset `o`. -/
def wr (l : List UInt8) (o n : Nat) (v : Int) : List UInt8 :=
  l.take o ++ Int.toBytes n v ++ l.drop (o + n)

theorem wr_length (l : List UInt8) (o n : Nat) (v : Int) (h : o + n ≤ l.length) :
    (wr l o n v).length = l.length := by
  simp only [wr, List.length_append, List.length_take, List.length_drop, Int.toBytes_length]
  omega

theorem wr_drop_take_same (l : List UInt8) (o n : Nat) (v : Int) (h : o + n ≤ l.length) :
    ((wr l o n v).drop o).take n = Int.toBytes n v := by
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  simp only [wr, List.append_assoc]
  rw [List.drop_left' h1, List.take_left' (Int.toBytes_length n v)]

theorem wr_drop_take_disj (l : List UInt8) (o n o' n' : Nat) (v : Int) (h : o + n ≤ l.length)
    (hd : o' + n' ≤ o ∨ o + n ≤ o') :
    ((wr l o n v).drop o').take n' = (l.drop o').take n' := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · rename_i hj
    simp only [wr, List.append_assoc]
    rcases hd with hd | hd
    · rw [List.getElem?_append_left (by simp only [List.length_take]; omega),
        List.getElem?_take_of_lt (by omega)]
    · rw [List.getElem?_append_right (by simp only [List.length_take]; omega),
        List.getElem?_append_right (by simp only [List.length_take, Int.toBytes_length]; omega),
        List.getElem?_drop]
      simp only [List.length_take, Int.toBytes_length]
      congr 1
      omega
  · rfl

theorem rd_wr_same (l : List UInt8) (o n : Nat) (v : Int) (h : o + n ≤ l.length) :
    rd (wr l o n v) o n = Int.ofBytes (Int.toBytes n v) := by
  simp only [rd, wr_drop_take_same l o n v h]

theorem rd_wr_disj (l : List UInt8) (o n o' n' : Nat) (v : Int) (h : o + n ≤ l.length)
    (hd : o' + n' ≤ o ∨ o + n ≤ o') :
    rd (wr l o n v) o' n' = rd l o' n' := by
  simp only [rd, wr_drop_take_disj l o n o' n' v h hd]

/-- A load at offset `o` of a list cell. -/
theorem lc_load {m : Mem 64} {l : List UInt8} {a : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ a ⋆ F) (o n : Nat) (hin : o + n ≤ l.length) (hw : l.length < 2 ^ 32) :
    m.loadInt (a + BitVec.ofNat 64 o) n = some (rd l o n) := by
  have ho : (a + BitVec.ofNat 64 o - a).toNat = o := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have := loadInt_slice (addr := a + BitVec.ofNat 64 o) h (by rw [ho]; exact hin) (by omega)
  rw [ho] at this
  exact this

/-- A store at offset `o` of a list cell. -/
theorem lc_store {m : Mem 64} {l : List UInt8} {a : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ a ⋆ F) (o n : Nat) (hin : o + n ≤ l.length) (hw : l.length < 2 ^ 32)
    (v : Int) :
    m.storeInt (a + BitVec.ofNat 64 o) n v =⋆ wr l o n v =@ a ⋆ F := by
  have ho : (a + BitVec.ofNat 64 o - a).toNat = o := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  have := storeInt_slice (addr := a + BitVec.ofNat 64 o) h (by rw [ho]; exact hin) (by omega) v
  rw [ho] at this
  exact this

end Kraken.Examples.Sbr.Ps

import Kraken.SepCells

/-!
Exercises for `Kraken.SepCells`: memory stated as a `⋆`-tree of `=@` and `?@`
cells, with the stack-frame shapes a procedure proof meets. Each example is a
pure memory fact, independent of any program, so a regression here points at
the cell lemmas and not at an instruction rule. `grind_cells` is `grind` with
the E-matching budget the cell rules' demand chains need.
-/

open Std.ExtHashMap Mem

set_option grind.warning false

namespace Kraken.Examples.SepCells

/-- A frame: return address at `r`, slot for the saved frame pointer at `r-8`,
a 4-byte local at `r-16`. The two stores find their cells, the loads read
through them, and the alias `rbp = r - 8` is resolved by `grind`. -/
example (m : Mem 64) (r : BitVec 64) (ra : List UInt8) (R : Mem 64 → Prop)
    (hra : ra.length = 8)
    (h : m =⋆ ra =@ r ⋆ (8 ?@ (r - 8) ⋆ (4 ?@ (r - 16) ⋆ R)))
    (v n : Int) (rbp : BitVec 64) (hrbp : rbp = r - 8) :
    ((m.storeInt (r - 8) 8 v).storeInt (rbp - 8) 4 n).loadInt (rbp - 8) 4
        = some (Int.ofBytes (Int.toBytes 4 n))
    ∧ ((m.storeInt (r - 8) 8 v).storeInt (rbp - 8) 4 n).loadInt (r - 8) 8
        = some (Int.ofBytes (Int.toBytes 8 v))
    ∧ ((m.storeInt (r - 8) 8 v).storeInt (rbp - 8) 4 n).loadInt r 8
        = some (Int.ofBytes ra)
    ∧ (((m.storeInt (r - 8) 8 v).storeInt (rbp - 8) 4 n).loadInt (rbp - 8) 4).isSome = true := by
  grind_cells

/-- A byte store into its own cell, by alias, keeps the other cells readable. -/
example (m : Mem 64) (r : BitVec 64) (ra : List UInt8) (R : Mem 64 → Prop)
    (hra : ra.length = 8)
    (h : m =⋆ ra =@ r ⋆ (8 ?@ (r - 8) ⋆ (4 ?@ (r - 16) ⋆ (1 ?@ (r - 9) ⋆ R))))
    (b : Int) (rbp : BitVec 64) (hrbp : rbp = r - 8) :
    (m.storeInt (rbp - 1) 1 b).loadInt r 8 = some (Int.ofBytes ra)
    ∧ ((m.storeInt (rbp - 1) 1 b).loadInt (rbp - 8) 4).isSome = true
    ∧ (m.storeInt (rbp - 1) 1 b).loadInt (rbp - 1) 1 = some (Int.ofBytes (Int.toBytes 1 b)) := by
  grind_cells

/-- Giving a frame back: a known cell is forgotten, two adjacent blocks are
one, and the cells are read in the order the caller states them. -/
example (m : Mem 64) (r : BitVec 64) (ra bs : List UInt8) (R : Mem 64 → Prop)
    (hbs : bs.length = 8)
    (h : m =⋆ ra =@ r ⋆ (bs =@ (r - 8) ⋆ (16 ?@ (r - 24) ⋆ R))) :
    m =⋆ ra =@ r ⋆ (24 ?@ (r - 24) ⋆ R) := by
  have h1 := Val.forget h (Split.right (Split.here _ _) _) (by omega)
  rw [hbs] at h1
  rw [Block.split_at _ 24 16 (by omega) (by omega),
    show r - 24 + BitVec.ofNat 64 16 = r - 8 by bv_decide]
  exact Mem.ac h1

end Kraken.Examples.SepCells

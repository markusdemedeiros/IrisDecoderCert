import Kraken.MachineWP

/-!
# Address normalisation for frame- and structure-relative accesses

The operands of a procedure with a frame pointer reach the frame as
`rsp₀ - 8 + (-o)` (`rbp = rsp₀ - 8`, a negative displacement), and the
structure fields as `p + c` with literal `c`; the separation-logic lemmas match
addresses syntactically, so these are brought to one form `rsp₀ - c'`:

* `BitVec.sub_add_ofNat_wrap`: `a - c + d = a - (c + (2^64 - d))`, for the
  normalised negative displacement `d = 2^64 - o` (`Int64.toBitVec_neg_ofNat_norm`);
* `BitVec.sub_sub_ofNat`: `a - b - c = a - (b + c)` (pushes, `sub $n, %rsp`).

Both have literal arguments in use; `Nat.reduceAdd`/`Nat.reduceSub` then compute the
offset.
-/

theorem BitVec.sub_add_ofNat_wrap (a : BitVec 64) (c d : Nat) (h : d ≤ 2 ^ 64) :
    a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c + (2 ^ 64 - d)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem BitVec.sub_sub_ofNat (a : BitVec 64) (b c : Nat) :
    a - BitVec.ofNat 64 b - BitVec.ofNat 64 c = a - BitVec.ofNat 64 (b + c) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

/-- `rsp` after a call returns: `a - c + d` with `d ≤ c` (the pushed slot popped). -/
theorem BitVec.sub_add_ofNat_cancel (a : BitVec 64) (c d : Nat) (h : d ≤ c) (h' : c ≤ 2 ^ 64) :
    a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `sub_add_ofNat_cancel` at the literal `8` of `CallPost`. -/
theorem BitVec.sub_ofNat_add_eight (a : BitVec 64) (c : Nat) (h : 8 ≤ c) (h' : c ≤ 2 ^ 64) :
    a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) :=
  BitVec.sub_add_ofNat_cancel a c 8 h h'

/-- An address without index register: `b + offset64 none + d` is `b + d`. -/
theorem BitVec.add_zero' (a : BitVec 64) : a + 0 = a := BitVec.add_zero a

import Kraken.X64.Examples.Sbr.Parse.ResetA1F1

/-!
# `sbr_reset`: wide stores into `f_master` read back as `int16` words (shard A1)

A store of `2 n` bytes at word `j` of `f_master` (`vmovd`, `vmovdqu`): word `j + t` (`t < n`) of
the result is the `t`-th 16-bit digit of the stored value; the other words are unchanged.
-/

open Kraken Kraken.SysV Mem
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

theorem a1_getElem?_wr_in {l v : List UInt8} {o : Nat} (h : o + v.length ≤ l.length) {i : Nat}
    (hi1 : o ≤ i) (hi2 : i < o + v.length) : (wr l o v)[i]? = v[i - o]? := by
  have e1 : (l.take o).length = o := by simp only [List.length_take]; omega
  simp only [wr, List.append_assoc]
  rw [List.getElem?_append_right (by omega), e1, List.getElem?_append_left (by omega)]

/-- `wr` of a concatenation: the two parts written one after the other. -/
theorem a1_wr_append {l A B : List UInt8} {o : Nat} (h : o + A.length + B.length ≤ l.length) :
    wr l o (A ++ B) = wr (wr l o A) (o + A.length) B := by
  apply List.ext_getElem?
  intro i
  have hl1 : (wr l o A).length = l.length := wr_length (by omega)
  have hAB : (A ++ B).length = A.length + B.length := List.length_append
  rcases (show i < o ∨ (o ≤ i ∧ i < o + A.length) ∨ (o + A.length ≤ i ∧ i < o + A.length + B.length)
      ∨ o + A.length + B.length ≤ i by omega) with hi | ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ | hi
  · rw [getElem?_wr_ne (by omega) (by omega),
      getElem?_wr_ne (by omega) (by omega), getElem?_wr_ne (by omega) (by omega)]
  · rw [a1_getElem?_wr_in (l := l) (v := A ++ B) (by omega) hi1 (by omega),
      getElem?_wr_ne (l := wr l o A) (v := B) (by omega) (by omega),
      a1_getElem?_wr_in (l := l) (v := A) (by omega) hi1 hi2, List.getElem?_append_left (by omega)]
  · rw [a1_getElem?_wr_in (l := l) (v := A ++ B) (o := o) (by omega) (by omega) (by omega),
      a1_getElem?_wr_in (l := wr l o A) (v := B) (o := o + A.length) (by omega) (by omega) (by omega),
      List.getElem?_append_right (by omega)]
    congr 1; omega
  · rw [getElem?_wr_ne (by omega) (by omega),
      getElem?_wr_ne (by omega) (by omega), getElem?_wr_ne (by omega) (by omega)]

/-- Word `j + t` after a `2 n`-byte store at word `j`: digit `t` of the value. -/
theorem a1_u16_wr_words : ∀ (n : Nat) {l : List UInt8} {j : Nat} (v : Int),
    2 * j + 2 * n ≤ l.length → ∀ t, t < n →
    (u16 (wr l (2 * j) (Int.toBytes (2 * n) v)) (j + t) : Int) = (v / 65536 ^ t) % 65536
  | 0, _, _, _, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, l, j, v, hl, t, ht => by
    have hb2 : (Int.toBytes 2 v).length = 2 := Int.toBytes_length ..
    have hbn : (Int.toBytes (2 * n) (v / 256 ^ 2)).length = 2 * n := Int.toBytes_length ..
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, Int.toBytes_add,
      a1_wr_append (by rw [hb2, hbn]; omega), hb2,
      show 2 * j + 2 = 2 * (j + 1) by omega]
    have hl' : (wr l (2 * j) (Int.toBytes 2 v)).length = l.length := wr_length (by omega)
    rcases t with _ | t
    · simp only [Nat.add_zero]
      rw [a1_u16_wr_ne (by rw [hbn, hl']; omega) (by omega)]
      rw [← Int.toBytes_emod]
      have h0 : 0 ≤ v.take (8 * 2) := by simp only [Int.take]; omega
      have h1 : v.take (8 * 2) < 65536 := by simp only [Int.take]; omega
      rw [a1_u16_wr_int (by omega) h0 h1]
      simp only [Int.take]; omega
    · have := a1_u16_wr_words n (l := wr l (2 * j) (Int.toBytes 2 v)) (j := j + 1) (v / 256 ^ 2)
        (by rw [hl']; omega) t (by omega)
      rw [show j + (t + 1) = j + 1 + t by omega, this]
      congr 1
      rw [Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ, Int.mul_comm]; rfl

end Kraken.Examples.Sbr.Reset

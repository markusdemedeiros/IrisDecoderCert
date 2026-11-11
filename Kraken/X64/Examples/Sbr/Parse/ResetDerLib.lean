import Kraken.X64.Examples.Sbr.Parse.ResetLib
import Kraken.X64.Examples.Sbr.ParseModel

/-!
# `sbr_reset`: byte facts of `sbr_make_f_derived`

The `memcpy` of `f_master[xover ..= n_master]` into `f_tablehigh` is `derived1`'s table
(`ftHigh_copy`): a `uint16_t` array is determined by its elements (`eq_of_u16`).
-/

open Kraken Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.Parse

theorem u8_eq_get? (l : List UInt8) (i : Nat) : u8 l i = (l[i]?.getD 0).toNat := by
  simp only [u8, List.getD_eq_getElem?_getD]

theorem u8_wr_out {l : List UInt8} {o : Nat} {v : List UInt8} (h : o + v.length ≤ l.length)
    {i : Nat} (hi : i < o ∨ o + v.length ≤ i) : u8 (wr l o v) i = u8 l i := by
  rw [u8_eq_get?, u8_eq_get?, getElem?_wr_ne h hi]

theorem u8_wr_in {l : List UInt8} {o : Nat} {v : List UInt8} (h : o + v.length ≤ l.length)
    {i : Nat} (hi : o ≤ i) (hi' : i < o + v.length) : u8 (wr l o v) i = u8 v (i - o) := by
  have h1 : (l.take o).length = o := by simp only [List.length_take]; omega
  rw [u8_eq_get?, u8_eq_get?]
  simp only [wr, List.append_assoc]
  rw [List.getElem?_append_right (by omega), h1, List.getElem?_append_left (by omega)]

theorem u8_slice {l : List UInt8} {o n i : Nat} (hi : i < n) : u8 (slice l o n) i = u8 l (o + i) := by
  rw [u8_eq_get?, u8_eq_get?]
  simp only [slice, List.getElem?_take, List.getElem?_drop, hi, ↓reduceIte]

theorem u8_lt (l : List UInt8) (i : Nat) : u8 l i < 256 := (l.getD i 0).toNat_lt

/-- Two byte lists of length `2k` with the same `uint16_t` elements are equal. -/
theorem eq_of_u16 {a b : List UInt8} {k : Nat} (ha : a.length = 2 * k) (hb : b.length = 2 * k)
    (h : ∀ i, i < k → u16 a i = u16 b i) : a = b := by
  apply List.ext_getElem (by omega)
  intro j hja hjb
  have hj := h (j / 2) (by omega)
  have e : u8 a j = u8 b j := by
    unfold u16 at hj
    have := u8_lt a (2 * (j / 2)); have := u8_lt a (2 * (j / 2) + 1)
    have := u8_lt b (2 * (j / 2)); have := u8_lt b (2 * (j / 2) + 1)
    rcases Nat.mod_two_eq_zero_or_one j with hp | hp
    · rw [show j = 2 * (j / 2) by omega]; omega
    · rw [show j = 2 * (j / 2) + 1 by omega]; omega
  rw [u8_eq_get?, u8_eq_get?, List.getElem?_eq_getElem hja, List.getElem?_eq_getElem hjb] at e
  exact UInt8.toNat_inj.mp e

/-- `memcpy(f_tablehigh, f_master + xover, 2 (n_master - xover + 1))` is `derived1`'s table. -/
theorem ftHigh_copy {fm fh : List UInt8} {nm xo : Nat} (hfm : fm.length = 98) (hfh : fh.length = 98)
    (hnm : nm ≤ 48) (hxo : xo ≤ nm) :
    wr fh 0 (slice fm (2 * xo) (2 * (nm - xo + 1)))
      = mk16 49 (fun i => if i ≤ nm - xo then u16 fm (xo + i) else u16 fh i) := by
  have hsl : (slice fm (2 * xo) (2 * (nm - xo + 1))).length = 2 * (nm - xo + 1) :=
    slice_length (by omega)
  apply eq_of_u16 (k := 49) (by rw [wr_length (by omega)]; omega) (mk16_length _ _)
  intro i hi
  rw [u16_mk16 hi]
  by_cases hc : i ≤ nm - xo
  · simp only [hc, ↓reduceIte]
    unfold u16
    rw [u8_wr_in (by omega) (by omega) (by omega), u8_wr_in (by omega) (by omega) (by omega),
      u8_slice (by omega), u8_slice (by omega)]
    have := u8_lt fm (2 * xo + (2 * i - 0)); have := u8_lt fm (2 * xo + (2 * i + 1 - 0))
    rw [show 2 * xo + (2 * i - 0) = 2 * (xo + i) by omega,
      show 2 * xo + (2 * i + 1 - 0) = 2 * (xo + i) + 1 by omega] at *
    omega
  · simp only [hc, ↓reduceIte]
    unfold u16
    rw [u8_wr_out (by omega) (by omega), u8_wr_out (by omega) (by omega)]
    have := u8_lt fh (2 * i); have := u8_lt fh (2 * i + 1)
    omega

end Kraken.Examples.Sbr.Parse

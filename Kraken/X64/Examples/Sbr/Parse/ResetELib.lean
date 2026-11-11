import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetDerLib

/-!
# `sbr_reset`: byte facts of the `f_tablelow` copy (`derived2`, shard B, env)

`LowM x xo f m` is `f_tablelow` with entry `0` and the entries `1..m` copied; a 2-byte store of
entry `m + 1` steps it (`rsE_LowM_step`).
-/

open Kraken Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

theorem rsE_u16_lt (l : List UInt8) (i : Nat) : u16 l i < 65536 := by
  have := (l.getD (2 * i) 0).toNat_lt; have := (l.getD (2 * i + 1) 0).toNat_lt
  unfold u16 u8; omega

/-- The two bytes of a 2-byte store, as a `uint16_t`. -/
theorem rsE_u16_toBytes2 (v : Int) : u16 (Int.toBytes 2 v) 0 = (v % 65536).toNat := by
  have h := ofBytes_toBytes 2 v
  obtain ⟨b0, b1, hb⟩ : ∃ b0 b1, Int.toBytes 2 v = [b0, b1] := ⟨_, _, rfl⟩
  rw [hb] at h ⊢
  rw [Int.ofBytes_cons, Int.ofBytes_cons] at h
  simp only [show Int.ofBytes [] = 0 from rfl, Int.take] at h
  unfold u16 u8
  simp only [List.getD_cons_zero, Nat.mul_zero, Nat.zero_add, List.getD_cons_succ]
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt
  omega

/-- A 2-byte store at entry `j` of a `uint16_t` array. -/
theorem rsE_u16_wr2 {l : List UInt8} {j : Nat} (v : Int) (h : 2 * j + 2 ≤ l.length) (i : Nat) :
    u16 (wr l (2 * j) (Int.toBytes 2 v)) i = if i = j then (v % 65536).toNat else u16 l i := by
  have hl : (Int.toBytes 2 v).length = 2 := Int.toBytes_length 2 v
  split
  · subst i
    rw [← rsE_u16_toBytes2 v]
    unfold u16
    rw [u8_wr_in (by omega) (by omega) (by omega), u8_wr_in (by omega) (by omega) (by omega)]
    simp only [Nat.sub_self, show 2 * j + 1 - 2 * j = 1 by omega, Nat.mul_zero, Nat.zero_add]
  · unfold u16
    rw [u8_wr_out (by omega) (by omega), u8_wr_out (by omega) (by omega)]

/-- Entry `m + 1` stored: `m + 1` entries copied. -/
theorem rsE_LowM_step (x : Args) (xo : Nat) (f : Nat → Nat) {m : Nat} (hm : m + 1 < 25) (v : Int)
    (hv : (v % 65536).toNat = f (xo + (2 * (m + 1) - x.n1 % 2)) % 65536) :
    wr (LowM x xo f m) (2 * (m + 1)) (Int.toBytes 2 v) = LowM x xo f (m + 1) := by
  have hl : (LowM x xo f m).length = 50 := by simp [LowM]
  apply eq_of_u16 (k := 25) (by rw [wr_length (by rw [Int.toBytes_length]; omega), hl])
    (by simp [LowM])
  intro i hi
  rw [rsE_u16_wr2 v (by omega), LowM, LowM, u16_mk16 hi]
  by_cases h1 : i = m + 1
  · subst h1; simp only [↓reduceIte, hv]; rw [u16_mk16 hi]; simp
  · simp only [h1, ↓reduceIte]
    rw [u16_mk16 hi]
    by_cases h0 : i = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      by_cases h2 : i ≤ m
      · simp [h2, show i ≤ m + 1 by omega]
      · simp [h2, show ¬ i ≤ m + 1 by omega]

/-- Entry `0` stored into `f_tablelow`: `0` entries copied. -/
theorem rsE_LowM_zero (x : Args) (xo : Nat) (f : Nat → Nat) (hl : x.ftLow.length = 50) (v : Int)
    (hv : (v % 65536).toNat = f xo % 65536) :
    wr x.ftLow 0 (Int.toBytes 2 v) = LowM x xo f 0 := by
  apply eq_of_u16 (k := 25) (by rw [wr_length (by rw [Int.toBytes_length]; omega), hl])
    (by simp [LowM])
  intro i hi
  rw [show (0 : Nat) = 2 * 0 from rfl, rsE_u16_wr2 v (by omega), LowM, u16_mk16 hi]
  by_cases h0 : i = 0
  · simp [h0, hv]
  · simp only [h0, ↓reduceIte, show ¬ i ≤ 0 by omega]
    exact (Nat.mod_eq_of_lt (rsE_u16_lt _ _)).symm

/-- All `n0` entries copied: `derived2`. -/
theorem rsE_dLw_n0 (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) :
    dLw a k0 nm f ((nm - xoOf a + 1) / 2) = dD2 a k0 nm f := rfl

end Kraken.Examples.Sbr.Reset

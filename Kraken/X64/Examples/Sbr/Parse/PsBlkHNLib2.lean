import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib
import Kraken.Rules.ScalarFloat

/-!
# `ff_ps_read_data` PS H: lemmas for `0x22d`–`0x715` (the class-0 border fill)

No `decide`/`rfl` on `Int64` literals: they are normalized by `simp` (`Int64.toBitVec_ofNat`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option grind.warning false

namespace Kraken.Examples.Sbr.Ps

theorem hn_c32 (a b : BitVec 32) (af o : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := o })
      = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

theorem hn_c8 (a b : BitVec 8) (af o : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := o })
      = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

/-- `lea -6(%rcx),%eax; cmp $-5,%eax; jb` with `rcx = num_env ∈ [1, 4]`: not taken. -/
theorem hn_trap (v : Nat) (h1 : 1 ≤ v) (h4 : v ≤ 4) :
    ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofInt 64 (v : Int) + (-6 : Int64).toBitVec)))).toNat
      < (BitVec.setWidth 32 (Int64.toBitVec 4294967291)).toNat := by
  have : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp

/-- `cmp $4,%r10b; jb` on `r10 ≤ 4`. -/
theorem hn_r10_4 (r : BitVec 64) (h : r.toNat ≤ 4) :
    (BitVec.setWidth 8 r).toNat < (BitVec.setWidth 8 (Int64.toBitVec 4)).toNat ↔ r.toNat < 4 := by
  have e : (BitVec.setWidth 8 (Int64.toBitVec 4)).toNat = 4 := by simp
  rw [e, BitVec.toNat_setWidth]; omega

theorem hn_eax_v (v : Nat) (h : v < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 64 (v : Int))) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofInt 64 (v : Int)).toNat = v := by rw [BitVec.toNat_ofInt]; omega
  simp only [BitVec.toNat_setWidth, e1, BitVec.toNat_ofNat]; omega

/-- `movzbl ff_log2_tab(v)`: `log2 v` for `v ∈ {1, 2}`. -/
theorem hn_lg (v : Nat) (h : v = 1 ∨ v = 2) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (rd [0, 0, 1, 1, 2, 2] v 1)))
      = BitVec.ofNat 64 (v - 1) := by
  rcases h with rfl | rfl <;> simp [rd, Int.ofBytes]

theorem hn_lg4 :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (rd [0, 0, 1, 1, 2, 2] 4 1))) = 2#64 := by
  simp [rd, Int.ofBytes]

theorem hn_one32 : BitVec.setWidth 64 (BitVec.setWidth 32 (Int64.toBitVec 1)) = 1#64 := by simp

theorem hn_i64z : Int64.toBitVec 0 = 0#64 := by simp

/-! ## `0x700`: the scalar fill loop -/

theorem hn_nz64 (a b : BitVec 64) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = !decide (a = b) := by
  rw [CondCode.interp_nz, StatusFlags.zf_from_result]
  have e : (a - b == 0#64) = decide (a = b) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by have := congrArg (· + b) h; simpa [BitVec.sub_add_cancel] using this,
      fun h => by subst h; simp⟩
  simpa using congrArg Bool.not e

/-- `mov %esi,%edi; shr %cl,%edi; dec %edi` with `esi = 32 j`, `cl = log2 v`. -/
theorem hn_fill (rsi rcx : BitVec 64) (j v : Nat) (hsi : rsi.toNat = 32 * j) (hj1 : 1 ≤ j)
    (hjv : j ≤ v) (hv : v = 1 ∨ v = 2) (hcx : rcx = BitVec.ofNat 64 (v - 1)) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (if rcx.toNat % 256 % 32 = 0 then BitVec.setWidth 64 (BitVec.setWidth 32 rsi)
       else BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 rsi))).ushiftRight
          (rcx.toNat % 256 % 32))) - 1))).toInt
      = (((j * 32) >>> (v - 1) : Nat) : Int) - 1 := by
  have e : rsi = BitVec.ofNat 64 (32 * j) := by
    apply BitVec.eq_of_toNat_eq; rw [hsi, BitVec.toNat_ofNat]; omega
  subst e hcx
  rcases hv with rfl | rfl
  · obtain rfl : j = 1 := by omega
    decide
  · have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl <;> decide

theorem hn_rsi_step (rsi : BitVec 64) (j : Nat) (hsi : rsi.toNat = 32 * j) (hj : j ≤ 4) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (Int64.toBitVec 32) + BitVec.setWidth 32 rsi)).toNat
      = 32 * (j + 1) := by
  have e : (BitVec.setWidth 32 (Int64.toBitVec 32)).toNat = 32 := by simp
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, e, BitVec.toNat_setWidth, hsi]
  omega

section
variable [CodeEnv]

theorem hn_fixed_step {c : List UInt8} {lg j : Nat} (hl : c.length = 764) (hfx : Fixed c lg j)
    (hj5 : j < 5) (w : BitVec 32) (hw : w.toInt = (((j * 32) >>> lg : Nat) : Int) - 1) :
    Fixed (wr c (52 + 4 * j) 4 w.toInt) lg (j + 1) := by
  intro e h1 h2
  by_cases h : e = j
  · subst h
    show i32 _ _ = _
    rw [i32_wr_same c _ w (by omega)]; exact hw
  · show i32 _ _ = _
    rw [i32_wr c _ 4 _ _ (by omega) (by omega)]; exact hfx e h1 (by omega)

theorem hn_bord0_wr {c : List UInt8} {j : Nat} (hl : c.length = 764) (hj : 1 ≤ j) (hj5 : j < 5)
    (w : Int) (hb0 : bord c 0 = -1) : bord (wr c (52 + 4 * j) 4 w) 0 = -1 := by
  show i32 _ _ = _
  rw [i32_wr c _ 4 _ _ (by omega) (by omega)]; exact hb0

end

theorem hn_bordTo_fin {c : List UInt8} {v : Nat} (hb0 : bord c 0 = -1) (hfx : Fixed c (v - 1) (v + 1))
    (hv : v = 1 ∨ v = 2) : BordTo c v := by
  rcases hv with rfl | rfl
  · have f1 : bord c 1 = 31 := by rw [hfx 1 (by omega) (by omega)]; decide
    refine ⟨hb0, fun e he => ?_, fun e he => ?_⟩
    · obtain rfl : e = 0 := by omega
      simp only [Nat.zero_add, hb0, f1]; omega
    · have : e = 0 ∨ e = 1 := by omega
      rcases this with rfl | rfl
      · simp only [hb0]; omega
      · simp only [f1]; omega
  · have f1 : bord c 1 = 15 := by rw [hfx 1 (by omega) (by omega)]; decide
    have f2 : bord c 2 = 31 := by rw [hfx 2 (by omega) (by omega)]; decide
    refine ⟨hb0, fun e he => ?_, fun e he => ?_⟩
    · have : e = 0 ∨ e = 1 := by omega
      rcases this with rfl | rfl
      · simp only [Nat.zero_add, hb0, f1]; omega
      · simp only [Nat.reduceAdd, f1, f2]; omega
    · have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
      rcases this with rfl | rfl | rfl
      · simp only [hb0]; omega
      · simp only [f1]; omega
      · simp only [f2]; omega

/-! ## `0x259`: `cmpb $0x10,-0x48(%rbp)` on `num_env = 4` -/

theorem hn_ofBytes_nonneg (l : List UInt8) : 0 ≤ Int.ofBytes l := by
  induction l with
  | nil => simp [Int.ofBytes]
  | cons b l ih => rw [Int.ofBytes_cons]; omega

/-- The low byte of a small 8-byte value. -/
theorem hn_byte0 (l : List UInt8) (n : Int) (hl : 8 ≤ l.length) (h : Int.ofBytes (List.take 8 l) = n)
    (hn : n < 256) : Int.ofBytes (List.take 1 l) = n := by
  match l, hl with
  | b :: rest, hl =>
    rw [List.take_succ_cons, Int.ofBytes_cons] at h
    rw [List.take_succ_cons, List.take_zero, Int.ofBytes_cons]
    have := hn_ofBytes_nonneg (List.take 7 rest)
    have h0 : Int.ofBytes (List.take 7 rest) = 0 := by omega
    rw [h0] at h
    simp only [Int.ofBytes, List.foldr_nil]
    omega

theorem hn_nc8 (a b : BitVec 8) (af o : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := o })
      = !decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

theorem hn_lt16 : (BitVec.ofInt 8 (4 : Int)).toNat < (BitVec.setWidth 8 (Int64.toBitVec 16)).toNat := by
  simp

end Kraken.Examples.Sbr.Ps

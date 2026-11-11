import Kraken.X64.Semantics

/-!
# `sbr_reset`, shard A2: lanes of the packed float results

The 32-bit lanes (`extractLsb' (32 * i) 32`) of `packedBinOp`, `packedBinOpIdx`, `insertps` and
the scalar-op shape `src1[127:32] ++ v`, for the `make_bands` blocks.
-/

namespace Kraken.Examples.Sbr.Reset

theorem ln_ex_ex {w : Nat} (x : BitVec w) (n m k l : Nat) (h : k + l ≤ m) :
    (x.extractLsb' n m).extractLsb' k l = x.extractLsb' (n + k) l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  simp only [show k + i < m from by omega, decide_true, Bool.true_and, Nat.add_assoc]

theorem ln_pk_step {c w : Nat} (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w)
    (h : ¬(c = 0 ∨ w < c)) : BitVec.packedBinOp c op a b
      = (BitVec.append (BitVec.packedBinOp c op (a.drop c) (b.drop c)) (op (a.take c) (b.take c))).setWidth w := by
  rw [BitVec.packedBinOp.eq_1, dif_neg h]

theorem ln_pk_base {c w : Nat} (op : BitVec c → BitVec c → BitVec c) (a b : BitVec w)
    (h : c = 0 ∨ w < c) : BitVec.packedBinOp c op a b = a := by
  rw [BitVec.packedBinOp.eq_1, dif_pos h]

theorem ln_pki_step {c w : Nat} (op : Nat → BitVec c → BitVec c → BitVec c) (a b : BitVec w) (i : Nat)
    (h : ¬(c = 0 ∨ w < c)) : BitVec.packedBinOpIdx c op a b i
      = (BitVec.append (BitVec.packedBinOpIdx c op (a.drop c) (b.drop c) (i + 1))
          (op i (a.take c) (b.take c))).setWidth w := by
  rw [BitVec.packedBinOpIdx.eq_1, dif_neg h]

theorem ln_pki_base {c w : Nat} (op : Nat → BitVec c → BitVec c → BitVec c) (a b : BitVec w) (i : Nat)
    (h : c = 0 ∨ w < c) : BitVec.packedBinOpIdx c op a b i = a := by
  rw [BitVec.packedBinOpIdx.eq_1, dif_pos h]

local macro "lane_fin" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.append_eq,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  simp (disch := omega) only [if_pos, if_neg, decide_eq_true, Bool.true_and, Nat.reduceMul, Nat.sub_sub,
    Nat.reduceAdd, Nat.add_sub_cancel_left, Nat.zero_add]))

/-- Lane `i` of a lanewise 32-bit operation on 128 bits. -/
theorem ln_pk32 (op : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) (i : Nat) (hi : i < 4) :
    (BitVec.packedBinOp 32 op a b).dw i = op (a.dw i) (b.dw i) := by
  simp (disch := decide) only [ln_pk_step, ln_pk_base, BitVec.take, BitVec.drop]
  simp (disch := omega) only [ln_ex_ex]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.dw]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals lane_fin

/-- Lane `i` of an indexed lanewise 32-bit operation on 128 bits. -/
theorem ln_pki32 (op : Nat → BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) (i : Nat) (hi : i < 4) :
    (BitVec.packedBinOpIdx 32 op a b).dw i = op i (a.dw i) (b.dw i) := by
  simp (disch := decide) only [ln_pki_step, ln_pki_base, BitVec.take, BitVec.drop]
  simp (disch := omega) only [ln_ex_ex]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.dw]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals lane_fin

/-- A 128-bit operation applied as one chunk. -/
theorem ln_pk128 (op : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 128) :
    BitVec.packedBinOp 128 op a b = op a b := by
  simp (disch := decide) only [ln_pk_step, ln_pk_base, BitVec.take, BitVec.drop]
  have ha : a.extractLsb' 0 128 = a := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
  have hb : b.extractLsb' 0 128 = b := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
  rw [ha, hb]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.append_eq, BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, if_true]

theorem ln_dw4 (x3 x2 x1 x0 : BitVec 32) :
    (x3 ++ x2 ++ x1 ++ x0).dw 0 = x0 ∧ (x3 ++ x2 ++ x1 ++ x0).dw 1 = x1
    ∧ (x3 ++ x2 ++ x1 ++ x0).dw 2 = x2 ∧ (x3 ++ x2 ++ x1 ++ x0).dw 3 = x3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [BitVec.dw]; lane_fin)

/-- The scalar-op result shape `src1[127:32] ++ v`. -/
theorem ln_lo_app (x : BitVec 128) (v : BitVec 32) (i : Nat) (hi : i < 4) :
    (x.extractLsb' 32 96 ++ v).dw i = if i = 0 then v else x.dw i := by
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals (simp only [BitVec.dw, ↓reduceIte, reduceCtorEq]; lane_fin)
  all_goals (congr 1; omega)

/-! Literal-offset forms for `simp` (lane `i` is `extractLsb' (32 * i) 32`). -/

theorem ln_sw (x : BitVec 128) : x.setWidth 32 = x.extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

theorem ln_pk_l0 (op : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOp 32 op a b).extractLsb' 0 32 = op (a.extractLsb' 0 32) (b.extractLsb' 0 32) :=
  ln_pk32 op a b 0 (by decide)
theorem ln_pk_l1 (op : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOp 32 op a b).extractLsb' 32 32 = op (a.extractLsb' 32 32) (b.extractLsb' 32 32) :=
  ln_pk32 op a b 1 (by decide)
theorem ln_pk_l2 (op : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOp 32 op a b).extractLsb' 64 32 = op (a.extractLsb' 64 32) (b.extractLsb' 64 32) :=
  ln_pk32 op a b 2 (by decide)
theorem ln_pk_l3 (op : BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOp 32 op a b).extractLsb' 96 32 = op (a.extractLsb' 96 32) (b.extractLsb' 96 32) :=
  ln_pk32 op a b 3 (by decide)

theorem ln_pki_l0 (op : Nat → BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOpIdx 32 op a b).extractLsb' 0 32 = op 0 (a.extractLsb' 0 32) (b.extractLsb' 0 32) :=
  ln_pki32 op a b 0 (by decide)
theorem ln_pki_l1 (op : Nat → BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOpIdx 32 op a b).extractLsb' 32 32 = op 1 (a.extractLsb' 32 32) (b.extractLsb' 32 32) :=
  ln_pki32 op a b 1 (by decide)
theorem ln_pki_l2 (op : Nat → BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOpIdx 32 op a b).extractLsb' 64 32 = op 2 (a.extractLsb' 64 32) (b.extractLsb' 64 32) :=
  ln_pki32 op a b 2 (by decide)
theorem ln_pki_l3 (op : Nat → BitVec 32 → BitVec 32 → BitVec 32) (a b : BitVec 128) :
    (BitVec.packedBinOpIdx 32 op a b).extractLsb' 96 32 = op 3 (a.extractLsb' 96 32) (b.extractLsb' 96 32) :=
  ln_pki32 op a b 3 (by decide)

theorem ln_d4_l0 (x3 x2 x1 x0 : BitVec 32) : (x3 ++ x2 ++ x1 ++ x0).extractLsb' 0 32 = x0 := (ln_dw4 x3 x2 x1 x0).1
theorem ln_d4_l1 (x3 x2 x1 x0 : BitVec 32) : (x3 ++ x2 ++ x1 ++ x0).extractLsb' 32 32 = x1 :=
  (ln_dw4 x3 x2 x1 x0).2.1
theorem ln_d4_l2 (x3 x2 x1 x0 : BitVec 32) : (x3 ++ x2 ++ x1 ++ x0).extractLsb' 64 32 = x2 :=
  (ln_dw4 x3 x2 x1 x0).2.2.1
theorem ln_d4_l3 (x3 x2 x1 x0 : BitVec 32) : (x3 ++ x2 ++ x1 ++ x0).extractLsb' 96 32 = x3 :=
  (ln_dw4 x3 x2 x1 x0).2.2.2

theorem ln_la_l0 (x : BitVec 128) (v : BitVec 32) : (x.extractLsb' 32 96 ++ v).extractLsb' 0 32 = v :=
  ln_lo_app x v 0 (by decide)
theorem ln_la_l1 (x : BitVec 128) (v : BitVec 32) :
    (x.extractLsb' 32 96 ++ v).extractLsb' 32 32 = x.extractLsb' 32 32 := ln_lo_app x v 1 (by decide)
theorem ln_la_l2 (x : BitVec 128) (v : BitVec 32) :
    (x.extractLsb' 32 96 ++ v).extractLsb' 64 32 = x.extractLsb' 64 32 := ln_lo_app x v 2 (by decide)
theorem ln_la_l3 (x : BitVec 128) (v : BitVec 32) :
    (x.extractLsb' 32 96 ++ v).extractLsb' 96 32 = x.extractLsb' 96 32 := ln_lo_app x v 3 (by decide)

/-- `insertps $0x10`: lane 1 replaced. -/
theorem ln_ins16 (a : BitVec 128) (v : BitVec 32) :
    BitVec.insertps 16 a v = a.extractLsb' 96 32 ++ a.extractLsb' 64 32 ++ v ++ a.extractLsb' 0 32 := by
  simp only [BitVec.insertps]
  rfl

end Kraken.Examples.Sbr.Reset

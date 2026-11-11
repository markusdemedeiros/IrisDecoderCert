import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable
import Kraken.X64.Examples.Sbr.Apply.DqCpl

/-! # `ff_aac_sbr_apply`: blocks of shard `GainAsm` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]


/-! ## GainAsm helper lemmas (apply-dqcpl) -/

omit [CodeEnv] in
theorem ga_sw64 (n : Nat) (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_c4 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int)))) = BitVec.ofNat 64 n := by
  rw [dq_c4_val, ga_sw64 n h]

/-- The facts of the started decoder that gain_calc needs. -/
theorem ga_facts {y : Args} {t : MachineData} (h : ApplyC y t) (hs : y.start ≠ 0) (ch : Nat)
    (hlive : ch ≠ 0 → y.idAac = 1) :
    y.nlim ≤ 29 ∧ y.kx1 ≤ 32 ∧ y.m1 ≤ 48 ∧ y.limGains ≤ 3 ∧ (y.d ch).nenv ≤ 8 ∧ 1 ≤ (y.d ch).nenv
      ∧ y.ftLim.length = 60
      ∧ (∀ i, i ≤ y.nlim → y.kx1 ≤ u16 y.ftLim i ∧ u16 y.ftLim i ≤ y.kx1 + y.m1)
      ∧ (∀ i, i < y.nlim → u16 y.ftLim i ≤ u16 y.ftLim (i + 1))
      ∧ (y.d ch).ypos ≤ 1 := by
  obtain ⟨⟨-, hk1, -, -, hm1, -, hlg, -, -, -, hnl, -, hT, hd0, hd1, -⟩, -⟩ := h
  obtain ⟨-, -, -, hfl, -, -, -, -, -, -, hlim, -, -, -, hlimm, -, -⟩ := hT hs
  have hd : DWF True (y.d ch) := by
    unfold Args.d; split
    · exact hd0.mono fun _ => hs
    · rename_i hc; exact hd1.mono fun _ => ⟨hs, hlive hc⟩
  obtain ⟨-, -, -, -, hne, -, -, -, hyp, -, -, -, -, -, -, hlv⟩ := hd
  exact ⟨hnl, hk1, hm1, hlg, hne, (hlv trivial).1, hfl, hlim, hlimm, hyp⟩

omit [CodeEnv] in
theorem ga_fr (a c : BitVec 64) : a - 8#64 + c = a - (8#64 - c) := by
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

/-- `dq_var` that does not require `lex_var` progress (measures pre-unfolded by the caller). -/
syntax "ga_var" : tactic
macro_rules
  | `(tactic| ga_var) => `(tactic| (
      try simp only [lex_var]
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, dq_one64]
      first
      | done
      | (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)
         refine Kraken.lex_cons_lt_of_lt (by rfl) ?_
         try simp (disch := omega) only [Nat.mod_eq_of_lt]
         omega)
      | (repeat (refine Kraken.lex_cons_le_cons (by rfl) ?_)
         first
         | exact Nat.le_refl _
         | (refine Kraken.lex_cons_le_of_lt (by rfl) ?_
            try simp (disch := omega) only [Nat.mod_eq_of_lt]
            omega))))

theorem ga_u16 (bs : List UInt8) (i : Nat) (h : 2 * i + 1 < bs.length) :
    Int.ofBytes ((bs.drop (2 * i)).take 2) = ((u16 bs i : Nat) : Int) := by
  have h1 : (bs.drop (2 * i)).take 2 = [bs[2 * i], bs[2 * i + 1]] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]; rfl
  rw [h1, Int.ofBytes_cons, Int.ofBytes_cons]
  simp only [u16, u8, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 2 * i < bs.length),
    List.getElem?_eq_getElem h, Option.getD_some]
  simp [Int.ofBytes]; omega

/-- A load `d` bytes below `r` is untouched by an `n`-byte store `c` bytes below it (disjoint). -/
theorem ga_ld_st (m : Mem 64) (r : BitVec 64) (c d n k : Nat) (v : Int)
    (h : c + k ≤ d ∨ d + n ≤ c) (hc : c < 2 ^ 63) (hd : d < 2 ^ 63) (hk : k ≤ 64) (hn : n ≤ 64) (hk0 : 0 < k) :
    (m.storeInt (r - BitVec.ofNat 64 c) n v).loadInt (r - BitVec.ofNat 64 d) k
      = m.loadInt (r - BitVec.ofNat 64 d) k := by
  rcases h with h | h
  · -- load below the store: wraps; use the generic lemma on the swapped difference
    apply Mem.loadInt_storeInt_of_above
    · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (2 ^ 64 - (d - c)) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega, BitVec.toNat_ofNat]
      omega
    · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (2 ^ 64 - (d - c)) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega, BitVec.toNat_ofNat]
      omega
  · apply Mem.loadInt_storeInt_of_above
    · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (c - d) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega, BitVec.toNat_ofNat]
      omega
    · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (c - d) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega, BitVec.toNat_ofNat]
      omega

theorem ga_w16 (n : Nat) (h : n < 2 ^ 15) :
    (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (n : Int))))).toInt = (n : Int) := by
  have e : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (n : Int)))) = BitVec.ofNat 16 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

theorem ga_s98_0 (t : MachineData) (ch : Nat) :
    t.regs.get64 .rsi + (252416#64 + BitVec.ofNat 64 (88768 * ch))
      = dA t ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (0 + 1)) := by
  simp only [dA, sbrA, arg1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ga_split (a : BitVec 64) (c d : Nat) (h : d ≤ c) :
    a + BitVec.ofNat 64 c = (a + BitVec.ofNat 64 (c - d)) + BitVec.ofNat 64 d := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.sub_add_cancel h]

theorem ga_off (a : BitVec 64) (c d : Nat) (h : d ≤ c) (hc : c < 2 ^ 64) :
    (a + BitVec.ofNat 64 c - (a + BitVec.ofNat 64 d)).toNat = c - d := by
  rw [show a + BitVec.ofNat 64 c - (a + BitVec.ofNat 64 d) = BitVec.ofNat 64 (c - d) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]
  simp only [BitVec.toNat_ofNat]; omega

theorem ga_lea192 (ee : Nat) (h : ee < 2 ^ 32) :
    (BitVec.ofNat 64 ee <<< 6) + (BitVec.ofNat 64 ee <<< 6) * 2#64 = BitVec.ofNat 64 (192 * ee) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ga_lea192c (ee : Nat) (h : ee < 2 ^ 32) (c d : BitVec 64) :
    (BitVec.ofNat 64 ee <<< 6) + ((BitVec.ofNat 64 ee <<< 6) * 2#64 + (c + d))
      = c + (d + BitVec.ofNat 64 (192 * ee)) := by
  rw [← BitVec.add_assoc, ga_lea192 ee h, BitVec.add_comm, BitVec.add_assoc]

theorem ga_c192 (ee : Nat) (c d : BitVec 64) :
    BitVec.ofNat 64 (192 * ee) + (c + d) = c + (d + BitVec.ofNat 64 (192 * ee)) := by
  rw [BitVec.add_comm, BitVec.add_assoc]

theorem ga_r16 (n : Nat) (h : n < 2 ^ 15) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 (n : Int))))))) = BitVec.ofNat 64 n := by
  rw [Int.ofBytes_toBytes_of_lt 2 (n : Int) (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_sub32 (a b : Nat) (ha : a < 2 ^ 16) (hb : b ≤ a) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 16 (BitVec.ofNat 64 a)))) - BitVec.setWidth 32 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_subz (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = 0 ↔ a = b := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_inc (n : Nat) (h : n + 1 < 2 ^ 64) : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, dq_one64]
  omega

omit [CodeEnv] in
theorem ga_sub32b (a b : Nat) (ha : a < 2 ^ 16) (hb : b ≤ a) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 a)) - BitVec.setWidth 32 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_off2 (a c : BitVec 64) (i : Nat) (h : 2 * i < 2 ^ 64) :
    (a + (BitVec.ofNat 64 i * 2#64 + c) - (a + c)).toNat = 2 * i := by
  have : a + (BitVec.ofNat 64 i * 2#64 + c) - (a + c) = BitVec.ofNat 64 i * 2#64 := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add]; omega
  rw [this, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_mz (n : Nat) (h : n < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (n : Int))) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_sub32c (a b : Nat) (ha : a < 2 ^ 16) (hb : b ≤ a) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 a) - BitVec.setWidth 32 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_mz32 (n : Nat) (h : n < 2 ^ 16) :
    BitVec.setWidth 32 (BitVec.ofInt 16 (n : Int)) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_sub32n (a b : Nat) (ha : a < 2 ^ 32) (hb : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

open Lean Elab Tactic Meta in
/-- revert all hypotheses mentioning `CondCode.interp` (branch conditions) so they can be simplified with the
register equations without `simp ... at *` (which loses the register hypotheses). -/
elab "ga_revert_conds" : tactic => withMainContext do
  let mut fvs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConst && e.constName!.toString.endsWith "CondCode.interp").isSome then
      fvs := fvs.push d.fvarId
  if fvs.isEmpty then throwError "ga_revert_conds: none"
  let (_, g) ← (← getMainGoal).revert fvs
  replaceMainGoal [g]

omit [CodeEnv] in
theorem ga_sx (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem ga_zx32 (a : Nat) (h : a < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 a) = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_sx32 (n : Nat) (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact ga_zx32 n (by omega)
  · simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem ga_fold_aux (a x y : BitVec 64) (c d : Nat) :
    a + (BitVec.ofNat 64 c + (x + (y + BitVec.ofNat 64 d)))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + (x + y)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_fold1_aux (a y : BitVec 64) (c d : Nat) :
    a + (BitVec.ofNat 64 c + (y + BitVec.ofNat 64 d))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- fold a trailing negative constant of an indexed address into the leading one (sep_mem picks the region
by it); use with `disch := decide` so only literal `d` qualify. -/
theorem ga_foldn (a x y : BitVec 64) (c d : Nat) (hc : c < 2 ^ 63) (hd : 2 ^ 63 ≤ d) :
    a + (BitVec.ofNat 64 c + (x + (y + BitVec.ofNat 64 d)))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + (x + y)) := ga_fold_aux a x y c d

omit [CodeEnv] in
theorem ga_fold1n (a y : BitVec 64) (c d : Nat) (hc : c < 2 ^ 63) (hd : 2 ^ 63 ≤ d) :
    a + (BitVec.ofNat 64 c + (y + BitVec.ofNat 64 d))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + y) := ga_fold1_aux a y c d

omit [CodeEnv] in
theorem ga_sub32d (a b : Nat) (ha : a < 2 ^ 16) (hb : b ≤ a) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 a)) - BitVec.ofNat 32 b)
      = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_sub32e (a b : Nat) (ha : a < 2 ^ 16) (hb : b ≤ a) :
    BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 a)) - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

open Lean Elab Tactic Meta in
/-- succeed iff the goal mentions the constant `Kraken.lex` (variant goals). -/
elab "ga_is_lex" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless (tgt.find? fun e => e.isConstOf ``Kraken.lex).isSome do throwError "ga_is_lex: no"

omit [CodeEnv] in
theorem ga_zx16 (a : Nat) (h : a < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 16 (BitVec.ofNat 64 a))) = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_add0 (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

omit [CodeEnv] in
theorem ga_offL (a c : BitVec 64) : (2 ^ 64 - a.toNat + (a + c).toNat) % 2 ^ 64 = c.toNat := by
  rw [BitVec.toNat_add]; have := a.isLt; have := c.isLt; omega

omit [CodeEnv] in
theorem ga_subL (a c : BitVec 64) : a + c - a = c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add]
  have := a.isLt; have := c.isLt; omega

omit [CodeEnv] in
theorem ga_s48 (n : Nat) : BitVec.ofNat 64 (48 * n) + 48#64 = BitVec.ofNat 64 (48 * (n + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_s192 (n : Nat) : BitVec.ofNat 64 (192 * n) + 192#64 = BitVec.ofNat 64 (192 * (n + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_foldp (a x y : BitVec 64) (c d : Nat) (hc : c < 2 ^ 63) (hd : d < 2 ^ 16) :
    a + (BitVec.ofNat 64 c + (x + (y + BitVec.ofNat 64 d)))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + (x + y)) := ga_fold_aux a x y c d

omit [CodeEnv] in
theorem ga_fold1p (a y : BitVec 64) (c d : Nat) (hc : c < 2 ^ 63) (hd : d < 2 ^ 16) :
    a + (BitVec.ofNat 64 c + (y + BitVec.ofNat 64 d))
      = a + (BitVec.ofNat 64 ((c + d) % 2 ^ 64) + y) := ga_fold1_aux a y c d

omit [CodeEnv] in
theorem ga_and7 (n : Nat) : (BitVec.ofNat 32 n &&& 7#32).toNat = n % 8 := by
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (7 % 2 ^ 32 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

omit [CodeEnv] in
theorem ga_and7w (n : Nat) : BitVec.setWidth 64 (BitVec.ofNat 32 n &&& 7#32) = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, ga_and7, BitVec.toNat_ofNat]
  try omega


omit [CodeEnv] in
theorem ga_t9m (m : Nat) (h : m ≤ 48) :
    ((m % 18446744073709551616 + 18446744073709551567) % 18446744073709551616) % 4294967296 = 4294967247 + m := by
  omega

omit [CodeEnv] in
/-- L93f0 trap L9bc5 (`lea -0x31(%r13)`): rw-only (simp `BitVec.toNat_add` on the 2^64-49 literal OOMs). -/
theorem ga_t9bc5 (a b k : Nat) (h0 : k ≤ a) (h01 : a < b) (h1 : b ≤ k + 48) (hk : k ≤ 32) :
    (BitVec.ofNat 64 (a - k) + 0 + BitVec.ofNat 64 (2 ^ 64 - 49 % 2 ^ 64)).toNat % 4294967296 <
      (4294967296 - b % 4294967296 + a % 4294967296) % 4294967296 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (0 : BitVec 64).toNat = 0 from BitVec.toNat_zero]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.add_zero, Nat.mod_mod]
  rw [ga_t9m (a - k) (by omega), Nat.mod_eq_of_lt (show a < 4294967296 by omega),
    Nat.mod_eq_of_lt (show b < 4294967296 by omega),
    Nat.mod_eq_of_lt (show 4294967296 - b + a < 4294967296 by omega)]
  omega

omit [CodeEnv] in
theorem ga_dec (n : Nat) (h : 1 ≤ n) (h2 : n < 2 ^ 64) : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, dq_one64]
  omega

omit [CodeEnv] in
theorem ga_r15 (a k : Nat) (h : k ≤ a) (ha : a < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (-BitVec.ofNat 32 k).toInt)) + BitVec.ofNat 32 a)
      = BitVec.ofNat 64 (a - k) := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_toInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega

omit [CodeEnv] in
theorem ga_add8 (n : Nat) : 8#64 + BitVec.ofNat 64 n = BitVec.ofNat 64 (n + 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_s48c (a : BitVec 64) (n : Nat) : 48#64 + (a + BitVec.ofNat 64 (48 * n)) = a + BitVec.ofNat 64 (48 * (n + 1)) := by
  rw [BitVec.add_comm, BitVec.add_assoc, ga_s48]

omit [CodeEnv] in
theorem ga_s192c (a c : BitVec 64) (n : Nat) :
    192#64 + (a + (c + BitVec.ofNat 64 (192 * n))) = a + (c + BitVec.ofNat 64 (192 * (n + 1))) := by
  rw [BitVec.add_comm, BitVec.add_assoc, BitVec.add_assoc, ga_s192]

omit [CodeEnv] in
theorem ga_c4n (n : Nat) (h : n < 2 ^ 32) : (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int)))).toNat = n := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ga_aa (a X : BitVec 64) (c d : Nat) :
    a + (BitVec.ofNat 64 c + (BitVec.ofNat 64 d + X)) = a + (BitVec.ofNat 64 (c + d) + X) := by
  rw [← BitVec.add_assoc (BitVec.ofNat 64 c), BitVec.ofNat_add]

omit [CodeEnv] in
theorem ga_s48cc (a c : BitVec 64) (n : Nat) :
    48#64 + (a + (c + BitVec.ofNat 64 (48 * n))) = a + (c + BitVec.ofNat 64 (48 * (n + 1))) := by
  rw [BitVec.add_comm, BitVec.add_assoc, BitVec.add_assoc, ga_s48]

/-! ## GainAsm tail helper lemmas (apply-dqsce) -/

omit [CodeEnv] in
theorem gq_off2 (a c : BitVec 64) (i : Nat) (h : 2 * i < 2 ^ 64) :
    (a + (BitVec.ofNat 64 i * 2#64 + c) - (a + c)).toNat = 2 * i := by
  have : a + (BitVec.ofNat 64 i * 2#64 + c) - (a + c) = BitVec.ofNat 64 i * 2#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add]
    omega
  rw [this, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem gq_u16 (bs : List UInt8) (i : Nat) (h : 2 * i + 1 < bs.length) :
    some ((u16 bs i : Nat) : Int) = some (Int.ofBytes (List.take 2 (List.drop (2 * i) bs))) := by
  rw [ga_u16 bs i h]



omit [CodeEnv] in
theorem gq_nz (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a + 18446744073709551615#64 - BitVec.ofNat 64 b == BitVec.zero 64) = decide (a = b + 1) := by
  rw [show BitVec.zero 64 = 0#64 from rfl, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  have hM : (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have hB : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_sub, BitVec.toNat_add, hA, hB, hM] at h2
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h2
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, hA, hB, hM]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

omit [CodeEnv] in
theorem gq_sub16 (bs : List UInt8) (i b : Nat) (ha : u16 bs i < 2 ^ 16) (hb : b ≤ u16 bs i) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofInt 16 (((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat : Nat) : Int))))))
      - BitVec.setWidth 32 (BitVec.ofNat 64 b)) = BitVec.ofNat 64 (u16 bs i - b) := by
  simp only [u16, u8] at ha hb ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem gq_z16 (bs : List UInt8) (i : Nat) (ha : u16 bs i < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat : Nat) : Int)))
      = BitVec.ofNat 64 (u16 bs i) := by
  simp only [u16, u8] at ha ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem gq_add2 (n : Nat) (h : n + 2 < 2 ^ 64) : BitVec.ofNat 64 n + 2#64 = BitVec.ofNat 64 (n + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem gq_sw3264 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem gq_yp {y : Args} {t : MachineData} (h : ApplyC y t) (ch : Nat) : (y.d ch).ypos ≤ 1 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd0, hd1, -⟩, -⟩ := h
  unfold Args.d; split
  · exact hd0.2.2.2.2.2.2.2.2.1
  · exact hd1.2.2.2.2.2.2.2.2.1

omit [CodeEnv] in
/-- Re-base `a + (c + X)` to the containing block base `a + c0` (array inside a merged ArrW block). -/
theorem gq_rb (a X : BitVec 64) (c c0 d : Nat) (h : c0 + d = c) :
    a + (BitVec.ofNat 64 c + X) = a + BitVec.ofNat 64 c0 + (BitVec.ofNat 64 d + X) := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

open Lean Elab Tactic Meta in
/-- succeed iff the goal is `Kraken.lex _ ≤ _` (cheap syntactic check, no unfolding). -/
elab "gq_le_lex" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let ok := tgt.isAppOfArity ``LE.le 4 && (tgt.getArg! 2).isAppOf ``Kraken.lex
  unless ok do throwError "gq_le_lex: no"

omit [CodeEnv] in
theorem gq_two : (2#64 : BitVec 64).toNat = 2 := by
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

omit [CodeEnv] in
theorem gq_two' : (2 : BitVec 64).toNat = 2 := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]

open Lean Elab Tactic Meta in
/-- succeed iff the goal is `_ % _ = _` (cheap syntactic check). -/
elab "gq_is_mod" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let ok := tgt.isAppOfArity ``Eq 3 && (tgt.getArg! 1).isAppOf ``HMod.hMod
  unless ok do throwError "gq_is_mod: no"

/-- rax readback of a 4-byte ypos cell (L9927). -/
theorem gq_rax4 (v : Nat) (h : v ≤ 1) :
    (Int.ofBytes (Int.toBytes 4 (v:Int)) % ((2 ^ 32 : Nat) : Int)).toNat % 2 ^ 64 % 2 ^ 32 = v := by
  rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by omega)]
  omega

open Lean Elab Tactic Meta in
/-- succeed iff the goal mentions `%` or `BitVec.toNat` (cheap guard for NATC). -/
elab "gq_natg" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let natRel := (tgt.isAppOfArity ``LE.le 4 || tgt.isAppOfArity ``LT.lt 4 || tgt.isAppOfArity ``Eq 3 || tgt.isAppOfArity ``Ne 3) &&
    (tgt.getArg! 0).isConstOf ``Nat
  let big := (tgt.find? fun e => e.isAppOf ``MachineData.mk).isSome
  unless natRel && !big do throwError "gq_natg: no"

open Lean Elab Tactic Meta in
/-- log just the main target (debug). -/
elab "gq_show" : tactic => withMainContext do
  logInfo m!"GQT: {← getMainTarget}"

omit [CodeEnv] in
/-- L96d3 L97b7-exit condition: `rsi-1 ≠ rax` as 64-bit words gives `a - b ≠ 1`. -/
theorem gq_ne1 (a b : Nat)
    (h : (!(BitVec.ofNat 64 a + 18446744073709551615#64 - BitVec.ofNat 64 b == BitVec.zero 64)) = true)
    (ha : a < 2 ^ 64) (hb : b < a) : a - b ≠ 1 := by
  intro h1
  obtain rfl : a = b + 1 := by omega
  have : BitVec.ofNat 64 (b + 1) + 18446744073709551615#64 - BitVec.ofNat 64 b = BitVec.zero 64 := by
    rw [← BitVec.ofNat_add_ofNat]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.sub_self]
    rfl
  simp only [this, beq_self_eq_true, Bool.not_true, Bool.false_eq_true] at h

open Lean Elab Tactic Meta in
/-- fail if the goal mentions the memory predicate `Mm` (keeps register simps off sep goals). -/
elab "gq_nomm" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let big := (tgt.find? fun e => match e with
    | .const n _ => n.getString! == "Mm"
    | _ => false).isSome
  if big then throwError "gq_nomm: Mm"

omit [CodeEnv] in
/-- `a + b - a = b` (sep_mem block-offset side goals, L9617_1). -/
theorem gq_asc {w : Nat} (a b : BitVec w) : a + b - a = b := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]
/-! ### GainAsm call blocks L98e0 / L9934_1 (apply-anahf) -/

omit [CodeEnv] in
theorem gn_call_res_n (k need : Nat) {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat)
    (hn : need ≤ 0x290 + k) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) (r₀ - 0x1c8#64) ⋆ K
      = 8 ?@ (r₀ - 0x1c8#64 - 8#64) ⋆ (Reserve need (r₀ - 0x1c8#64 - 8#64)
        ⋆ ((0x290 + k - need) ?@ (r₀ - 0x1c8#64 - BitVec.ofNat 64 (0x298 + k)) ⋆ K)) := by
  have hr : 0x298 + k ≤ (r₀ - 0x1c8#64).toNat := by bv_omega
  generalize r₀ - 0x1c8#64 = r at hr ⊢
  rw [show 0x298 + k = 8 + (0x290 + k) by omega, Reserve_split 8 (0x290 + k) r (by omega),
    Reserve.excess need (0x290 + k) (r - BitVec.ofNat 64 8) hn (by bv_omega), BitVec.sub_sub_ofNat]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem gn_carve_at (a : BitVec 64) (len m n : Nat) (h : m + n ≤ len) (hw : len < 2 ^ 64) :
    len ?@ a = n ?@ (a + BitVec.ofNat 64 m)
      ⋆ (m ?@ a ⋆ (len - m - n) ?@ (a + BitVec.ofNat 64 m + BitVec.ofNat 64 n)) := by
  have e : (a + BitVec.ofNat 64 m - a).toNat = m := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have c := Mem.Block.carve (a := a) (b := a + BitVec.ofNat 64 m) (len := len) (n := n)
    (by rw [e]; exact h) (by omega)
  rw [e] at c
  exact c

omit [CodeEnv] in
theorem gn_byte_split (l : List UInt8) (a : BitVec 64) (j : Nat) (hj : j < l.length) (hw : l.length ≤ 2 ^ 64) :
    l =@ a = l.take j =@ a ⋆ ([l.getD j 0] =@ (a + BitVec.ofNat 64 j) ⋆
      l.drop (j + 1) =@ (a + BitVec.ofNat 64 j + 1#64)) := by
  have e : l = l.take j ++ ([l.getD j 0] ++ l.drop (j + 1)) := by
    have h1 := (List.take_append_drop j l).symm
    rw [List.drop_eq_getElem_cons hj] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact h1
  have hl : (l.take j).length = j := by simp only [List.length_take]; omega
  rw [show (l =@ a) = ((l.take j ++ ([l.getD j 0] ++ l.drop (j + 1))) =@ a) from by rw [← e]]
  rw [Mem.Val.append_eq (l.take j) _ a (a + BitVec.ofNat 64 j) (by rw [hl])
      (by simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, List.length_drop]; omega),
    Mem.Val.append_eq [l.getD j 0] _ (a + BitVec.ofNat 64 j) (a + BitVec.ofNat 64 j + 1#64) (by simp)
      (by simp only [List.length_cons, List.length_nil, List.length_drop]; omega)]


omit [CodeEnv] in
/-- `Y[38][64][2]` of both halves, half `p` first. -/
theorem gn_y2 (a : BitVec 64) (p : Nat) (hp : p ≤ 1) (K : Mem 64 → Prop) :
    38912 ?@ a ⋆ K = 19456 ?@ (a + BitVec.ofNat 64 (0x4c00 * p))
      ⋆ (19456 ?@ (a + BitVec.ofNat 64 (0x4c00 * (1 - p))) ⋆ K) := by
  have e := Block.split a 19456 19456 (by decide)
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  · simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at e ⊢
    rw [e, Std.ExtHashMap.sep_assoc]
  · simp only [Nat.mul_zero, Nat.sub_self, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceAdd] at e ⊢
    rw [e]; ac_rfl

omit [CodeEnv] in
theorem gn_c4 (n : Nat) (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem gn_tb1 (b : UInt8) (h : b.toNat < 128) : Int.toBytes 1 (BitVec.ofNat 8 b.toNat).toInt = [b] := by
  have e : (BitVec.ofNat 8 b.toNat).toInt = Int.ofBytes [b] := by
    rw [BitVec.toInt_eq_toNat_of_msb]
    · simp only [BitVec.toNat_ofNat, Int.ofBytes, List.foldr]; omega
    · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [e]; exact Int.toBytes_ofBytes_all [b]

omit [CodeEnv] in
theorem gn_rax (r : BitVec 64) (p : Nat) (h : r.toNat % 2 ^ 32 = p) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r) * 19456#64 = BitVec.ofNat 64 (19456 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  have : r.toNat % 4294967296 % 18446744073709551616 = p := by rw [Nat.mod_eq_of_lt (by omega)]; exact h
  rw [this]; omega

omit [CodeEnv] in
theorem gn_m19 (q : Nat) : BitVec.ofNat 64 q * 19456#64 = BitVec.ofNat 64 (19456 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

omit [CodeEnv] in
theorem gn_r9 (ch : Nat) (h : ch < 2) : (BitVec.ofNat 64 ch).toNat % 2 ^ 32 = ch := by
  simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem gn_te (r : BitVec 64) (ch : Nat) :
    r + (166176#64 + BitVec.ofNat 64 (88869 + 88768 * ch))
      = r + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64)) := by
  have e : BitVec.ofNat 64 (88869 + 88768 * ch) = BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  rw [e]

/-! L98e0 (sbr_hf_assemble call) -/

omit [CodeEnv] in
theorem gn_tb4 (l : List UInt8) (hl : l.length = 4) :
    Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes l)).toInt = l := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod]
  have h : (Int.ofBytes l).bmod (2 ^ 32) % (2 ^ (8 * 4) : Int) = Int.ofBytes l % 2 ^ (8 * 4) := Int.bmod_emod
  rw [show ((Int.ofBytes l).bmod (2 ^ 32)).take (8 * 4) = (Int.ofBytes l).bmod (2 ^ 32) % 2 ^ (8 * 4) from rfl, h,
    show Int.ofBytes l % 2 ^ (8 * 4) = (Int.ofBytes l).take (8 * 4) from rfl, Int.toBytes_emod]
  have := Int.toBytes_ofBytes_all l
  rw [hl] at this
  exact this

omit [CodeEnv] in
theorem gn_ea {m : Mem 64} {a : BitVec 64} {K : Mem 64 → Prop} (h : m =⋆ (8 ?@ a ⋆ K)) :
    ∃ v0 v1 : BitVec 32, m =⋆ (Int.toBytes 4 v0.toInt =@ a ⋆ (Int.toBytes 4 v1.toInt =@ (a + 4#64) ⋆ K)) := by
  obtain ⟨-, bs, hlen, h'⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes (bs.take 4)), BitVec.ofInt 32 (Int.ofBytes (bs.drop 4)), ?_⟩
  rw [gn_tb4 _ (by simp only [List.length_take]; omega), gn_tb4 _ (by simp only [List.length_drop]; omega),
    ← Std.ExtHashMap.sep_assoc,
    ← Val.append_eq (bs.take 4) (bs.drop 4) a (a + 4#64) (by simp only [List.length_take]; rw [Nat.min_eq_left (by omega)])
      (by simp only [List.length_take, List.length_drop]; omega), List.take_append_drop]
  exact h'

omit [CodeEnv] in
theorem gn_tb1n (b : UInt8) : Int.toBytes 1 ((b.toNat : Nat) : Int) = [b] := by
  have e : ((b.toNat : Nat) : Int) = Int.ofBytes [b] := by
    simp only [Int.ofBytes, List.foldr]; omega
  rw [e]; exact Int.toBytes_ofBytes_all [b]

omit [CodeEnv] in
theorem gn_cons2 (b b' : UInt8) (l : List UInt8) (a a' : BitVec 64) (ha : a' = a + 1#64)
    (hw : l.length + 2 ≤ 2 ^ 64) :
    (b :: b' :: l) =@ a = [b] =@ a ⋆ (b' :: l) =@ a' := by
  rw [show b :: b' :: l = [b] ++ (b' :: l) from rfl]
  exact Val.append_eq [b] (b' :: l) a a' ha (by simp only [List.length_cons, List.length_nil]; omega)

omit [CodeEnv] in
theorem gn_te10 (l : List UInt8) (h : l.length = 10) (a : BitVec 64) (K : Mem 64 → Prop) :
    l =@ a ⋆ K = Int.toBytes 1 ((l.getD 0 0).toNat : Int) =@ a
      ⋆ (Int.toBytes 1 ((l.getD 1 0).toNat : Int) =@ (a + 1#64)
      ⋆ (Int.toBytes 1 ((l.getD 2 0).toNat : Int) =@ (a + 2#64)
      ⋆ (Int.toBytes 1 ((l.getD 3 0).toNat : Int) =@ (a + 3#64)
      ⋆ (Int.toBytes 1 ((l.getD 4 0).toNat : Int) =@ (a + 4#64)
      ⋆ (Int.toBytes 1 ((l.getD 5 0).toNat : Int) =@ (a + 5#64)
      ⋆ (Int.toBytes 1 ((l.getD 6 0).toNat : Int) =@ (a + 6#64)
      ⋆ (Int.toBytes 1 ((l.getD 7 0).toNat : Int) =@ (a + 7#64)
      ⋆ (Int.toBytes 1 ((l.getD 8 0).toNat : Int) =@ (a + 8#64)
      ⋆ (Int.toBytes 1 ((l.getD 9 0).toNat : Int) =@ (a + 9#64) ⋆ K))))))))) := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9], _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ, gn_tb1n]
    rw [gn_cons2 _ _ _ a (a + 1#64) rfl (by simp),
      gn_cons2 _ _ _ (a + 1#64) (a + 2#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 2#64) (a + 3#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 3#64) (a + 4#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 4#64) (a + 5#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 5#64) (a + 6#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 6#64) (a + 7#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 7#64) (a + 8#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
      gn_cons2 _ _ _ (a + 8#64) (a + 9#64) (by rw [BitVec.add_assoc]; rfl) (by simp)]
    simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem gn_al_rsp (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 464#64 + 8#64) = true := by
  simp only [isAligned, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at *
  omega

omit [CodeEnv] in
theorem gn_al16 {a : BitVec 64} (h : isAligned 32 a = true) : isAligned 16 a = true := by
  simp only [isAligned, beq_iff_eq] at *; omega

/-- `HfIdxOut t` at its address (G1): the returned `f_indexnoise`/`f_indexsine` pair, bounded. -/
def gnIdx (a : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ i : BitVec 64, i.toNat % 2 ^ 32 ≤ 515 ∧ i.toNat / 2 ^ 32 < 4 ∧ (Int.toBytes 8 i.toInt =@ a) m

theorem gn_hio (t : MachineData) : HfIdxOut t = gnIdx (arg3 t + 0x15aac#64) := rfl

omit [CodeEnv] in
theorem gn_idx {m : Mem 64} {a : BitVec 64} {K : Mem 64 → Prop} (h : m =⋆ (gnIdx a ⋆ K)) :
    ∃ i : BitVec 64, i.toNat % 2 ^ 32 ≤ 515 ∧ i.toNat / 2 ^ 32 < 4
      ∧ m =⋆ (Int.toBytes 8 i.toInt =@ a ⋆ K) := by
  obtain ⟨m₁, m₂, hd, hm, ⟨i, h1, h2, h₁⟩, h₂⟩ := h
  exact ⟨i, h1, h2, m₁, m₂, hd, hm, h₁, h₂⟩

theorem gn_applyC_idx0 {y : Args} {t : MachineData} (h : ApplyC y t) (i : BitVec 64)
    (h1 : i.toNat % 2 ^ 32 ≤ 515) (h2 : i.toNat / 2 ^ 32 < 4) :
    ApplyC { y with d0 := { y.d0 with idx := i } } t := by
  unfold ApplyC SbrWF DWF at *
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hd0, hd1, hps⟩, hL⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, -, b14, b15, b16⟩ := hd0
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, h1, h2, b14, b15, b16⟩, hd1, hps⟩, hL⟩

theorem gn_applyC_idx1 {y : Args} {t : MachineData} (h : ApplyC y t) (i : BitVec 64)
    (h1 : i.toNat % 2 ^ 32 ≤ 515) (h2 : i.toNat / 2 ^ 32 < 4) :
    ApplyC { y with d1 := { y.d1 with idx := i } } t := by
  unfold ApplyC SbrWF DWF at *
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hd0, hd1, hps⟩, hL⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -, -, b14, b15, b16⟩ := hd1
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hd0,
    ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, h1, h2, b14, b15, b16⟩, hps⟩, hL⟩

omit [CodeEnv] in
theorem gn_m38 (r : BitVec 64) (K : Mem 64 → Prop) :
    8 ?@ (r - 56#64) ⋆ K = 4 ?@ (r - 56#64) ⋆ (4 ?@ (r - 52#64) ⋆ K) := by
  have e := Block.split (r - 56#64) 4 4 (by decide)
  have h : r - 56#64 + BitVec.ofNat 64 4 = r - 52#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [h] at e
  rw [show (8 : Nat) = 4 + 4 from rfl, e, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem gn_alD0 (s : BitVec 64) (ch : Nat) (h : isAligned 32 s = true) :
    isAligned 16 (s + BitVec.ofNat 64 (128 + 88768 * ch)) = true := by
  simp only [isAligned, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

omit [CodeEnv] in
theorem gn_alD (r : BitVec 64) (ch : Nat) (h : isAligned 32 (r + 166176#64) = true) :
    isAligned 16 (r + (166176#64 + BitVec.ofNat 64 (128 + 88768 * ch))) = true := by
  rw [← BitVec.add_assoc]; exact gn_alD0 _ ch h

omit [CodeEnv] in
theorem gn_sw (p : Nat) (h : p < 2 ^ 31) : BitVec.setWidth 64 (BitVec.ofInt 32 (p : Int)) = BitVec.ofNat 64 p := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem gn_rdi (r : BitVec 64) (ch p : Nat) :
    31024#64 + (r + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + BitVec.ofNat 64 (19456 * p))))
      = r + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + (31024#64 + BitVec.ofNat 64 (19456 * p)))) := by
  ac_rfl

omit [CodeEnv] in
theorem gn_split44 (a : BitVec 64) (K : Mem 64 → Prop) :
    8 ?@ a ⋆ K = 4 ?@ a ⋆ (4 ?@ (a + 4#64) ⋆ K) := by
  rw [show (8 : Nat) = 4 + 4 from rfl, Block.split a 4 4 (by decide), Std.ExtHashMap.sep_assoc]

/-! ### M4b layout (apply-mapb): Y / X views at the hf_assemble and x_gen calls -/

omit [CodeEnv] in
/-- The `hf_assemble` call's view of `Y[2] ++ g_temp ++ q_temp` (`d = &sbr->data[ch]`,
`p = ypos`, the frame blocks of `DArrW`): `Y[p]` (19456 bytes), the 24 bytes after it
(`HfData`, see `a2_row_spill`), `g_temp ++ q_temp` from byte `24·p` (16128 − 24·p bytes),
and the rest (`Y[1 − p]`, without the 24 bytes after `Y[0]` when `p = 0`). -/
theorem gn_hfY (d : BitVec 64) (p : Nat) (hp : p ≤ 1) (K : Mem 64 → Prop) :
    38936 ?@ (d + 0x7930#64) ⋆ (8040 ?@ (d + 0x11148#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ K))
      = 19456 ?@ (d + 0x7930#64 + BitVec.ofNat 64 (19456 * p))
        ⋆ (24 ?@ (d + 0x7930#64 + BitVec.ofNat 64 (19456 * p) + 19456#64)
        ⋆ ((16128 - 24 * p) ?@ (d + 0x11130#64 + BitVec.ofNat 64 (24 * p))
        ⋆ ((19432 + 24 * p) ?@ (d + 0x7930#64 + BitVec.ofNat 64 ((1 - p) * 19480)) ⋆ K))) := by
  have e1 := Block.split (d + 0x7930#64) 19456 19480 (by decide)
  have e5 := Block.split (d + 0x11148#64) 8040 8064 (by decide)
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  · have e2 := Block.split (d + 0xc530#64) 24 19456 (by decide)
    have e3 := Block.split (d + 0xc548#64) 19432 24 (by decide)
    have e4 := Block.split (d + 0x11130#64) 24 16104 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at e1 e2 e3 e4 e5
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    rw [e1, e2, e3, e4, e5]
    ac_rfl
  · have e2 := Block.split (d + 0xc530#64) 19456 24 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at e1 e2 e5
    simp only [Nat.mul_one, Nat.sub_self, Nat.zero_mul, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    rw [e1, e2, e5]
    ac_rfl

omit [CodeEnv] in
/-- `Y[2]` plus the 24 bytes after it (`DArrW`'s 38936-byte block at `d + 0x7930`), half `p`
first (the `sbr_x_gen` call's `Y0`/`Y1`). -/
theorem gn_y3 (a : BitVec 64) (p : Nat) (hp : p ≤ 1) (K : Mem 64 → Prop) :
    38936 ?@ a ⋆ K = 19456 ?@ (a + BitVec.ofNat 64 (0x4c00 * p))
      ⋆ (19456 ?@ (a + BitVec.ofNat 64 (0x4c00 * (1 - p))) ⋆ (24 ?@ (a + 38912#64) ⋆ K)) := by
  have e := Block.split a 38912 24 (by decide)
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at e
  rw [e, Std.ExtHashMap.sep_assoc, gn_y2 a p hp, ← Std.ExtHashMap.sep_assoc (19456 ?@ _),
    Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- The two halves of `X` (`ArrW`, `r = rsi`, `sbr = r + 166176`), half `p` first. -/
theorem gn_x2 (r : BitVec 64) (p : Nat) (hp : p ≤ 1) (K : Mem 64 → Prop) :
    19456 ?@ (r + 509024#64) ⋆ (19456 ?@ (r + 528480#64) ⋆ K)
      = 19456 ?@ (r + (509024#64 + BitVec.ofNat 64 (19456 * p)))
        ⋆ (19456 ?@ (r + (509024#64 + BitVec.ofNat 64 (19456 * (1 - p)))) ⋆ K) := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  · simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd]
  · simp only [Nat.mul_one, Nat.sub_self, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd]
    ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9146 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9146" ⟨"ff_aac_sbr_apply.L9146", B.L9146, some "ff_aac_sbr_apply.L914e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrax, hrbx, hm⟩ := T.L9146.mp hs
  dsimp only
  simp only [B.L9146]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try (goal_has_str "ff_aac_sbr_apply.L98e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L98e0") ?_; refine ⟨isSome_at L.L98e0, ?_, ?_⟩; rw [T.L98e0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e])
  all_goals try edge_step
  all_goals try (left; dq_var)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx]; done)
  all_goals try (simp only [Mm, FrX, FrGA]; sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L914e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e" ⟨"ff_aac_sbr_apply.L914e", B.L914e, some "ff_aac_sbr_apply.L914e_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hm⟩ := T.L914e.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, FrX, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 4 (y.nlim : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 477964#64) 4 := by
    sep_mem hm; rfl
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.nlim < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.nlim < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L98e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L98e0") ?_; refine ⟨isSome_at L.L98e0, ?_, ?_⟩; rw [T.L98e0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e_1])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [loadInt_storeInt_sub_lo, loadInt_storeInt_sub_hi])
  all_goals try (left; ga_var)
  all_goals try (right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, (?_ : 1 ≤ _), ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp]; done)
  all_goals try omega
  all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, FrX, FrGA, FrGa1, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L914e_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e_1" ⟨"ff_aac_sbr_apply.L914e_1", B.L914e_1, some "ff_aac_sbr_apply.L914e_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hnl1, hm⟩ := T.L914e_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa1, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 4 (y.kx1 : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 166264#64) 4 := by
    sep_mem hm; rfl
  have hL0b : u16 y.ftLim 0 < 2 ^ 15 := by have := hlim 0 (by omega); omega
  have l3 : some ((u16 y.ftLim 0 : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 478226#64) 2 := by
    sep_mem hm
    all_goals simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, hfl, Nat.reducePow, List.drop_zero]
    all_goals first | omega | (have := ga_u16 y.ftLim 0 (by omega); simp only [Nat.mul_zero, List.drop_zero] at this; rw [this])
  generalize hL0 : u16 y.ftLim 0 = L0 at l3 hL0b ⊢
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.kx1 < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.kx1 < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try simp only [ga_w16 _ hL0b]
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e_2])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (left; ga_var)
  all_goals try (right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, arg1]; done)
  all_goals try ((try subst hL0); (try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa1, FrGa2, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
  all_goals ((try subst hL0); (try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa1, FrGa2, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L914e_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e_2" ⟨"ff_aac_sbr_apply.L914e_2", B.L914e_2, some "ff_aac_sbr_apply.L914e_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hnl1, hr10, hrcx, hm⟩ := T.L914e_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa2, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (88768 * ch)).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 160#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 252416#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 360#64) 8 := by
    sep_mem hm; rfl
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.kx1 < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.kx1 < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try simp only [dq_sw32, dq_sw3264]
  all_goals try simp only [ga_s98_0]
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e_3])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (left; ga_var)
  all_goals try (right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr10, hrcx, arg1]; done)
  all_goals ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa2, FrGe0, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L914e_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e_3" ⟨"ff_aac_sbr_apply.L914e_3", B.L914e_3, some "ff_aac_sbr_apply.L91c0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hnl1, hr10, hrcx, hm⟩ := T.L914e_3.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e_3]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 557028#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 352#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 553952#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 272#64) 8 := by
    sep_mem hm; rfl
  have l3 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 548960#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 216#64) 8 := by
    sep_mem hm; rfl
  have l4 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 557024#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 264#64) 8 := by
    sep_mem hm; rfl
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, ← l4, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, ← l4, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, ← l3, ← l4, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.kx1 < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.kx1 < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try simp only [dq_sw32, dq_sw3264]
  all_goals try (goal_has_str "ff_aac_sbr_apply.L91f7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L91f7") ?_; refine ⟨isSome_at L.L91f7, ?_, ?_⟩; rw [T.L91f7])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L91f7])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals try (dq_guard_or; left; ga_var)
  all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, 0, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Args.d] at hne1 ⊢; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr10, hrcx, arg1, sbrA, Nat.mul_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceOfNat, BitVec.add_zero, BitVec.xor_self]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]; rfl)
  all_goals ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L91c0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L91c0" ⟨"ff_aac_sbr_apply.L91c0", B.L91c0, some "ff_aac_sbr_apply.L91f7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L91c0.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L91c0]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    first
    | (guard_hyp hne : y.d0.nenv ≤ 8; have lne : some (Int.ofBytes (Int.toBytes 4 ((y.d0.nenv : Nat) : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 166312#64) 4 := (by sep_mem hm; rfl); have l98 : some (Int.ofBytes (Int.toBytes 8 (dA t₀ 0 + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1))).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 160#64) 8 := (by sep_mem hm; simp only [dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]))
    | (guard_hyp hne : y.d1.nenv ≤ 8; have lne : some (Int.ofBytes (Int.toBytes 4 ((y.d1.nenv : Nat) : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 255080#64) 4 := (by sep_mem hm; rfl); have l98 : some (Int.ofBytes (Int.toBytes 8 (dA t₀ 1 + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1))).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 160#64) 8 := (by sep_mem hm; simp only [dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]))
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← lne, ← l98, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← lne, ← l98, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← lne, ← l98, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hrcx, hrbx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec, ga_c4n, ga_inc]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp only [ga_s48cc, ga_s48, ga_s192, BitVec.add_assoc]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L98e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L98e0") ?_; refine ⟨isSome_at L.L98e0, ?_, ?_⟩; rw [T.L98e0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L91f7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L91f7") ?_; refine ⟨isSome_at L.L91f7, ?_, ?_⟩; rw [T.L91f7]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee + 1, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee + 1, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L91f7]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee + 1, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee + 1, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try simp (disch := omega) only [ga_c4, ga_inc]
    all_goals try simp only [ga_s48, ga_s192, BitVec.add_assoc]
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, ite_true, ite_false]; omega)
    all_goals try (simp only [ga_s48c, ga_s192c, ga_aa, sbrA, arg1, BitVec.add_assoc, Nat.reduceAdd]; done)
    all_goals try (ga_is_lex; simp -implicitDefEqProofs (disch := omega) only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; first | ga_var | (apply Nat.le_of_lt; ga_var))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGA, FrGb, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L91f7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L91f7" ⟨"ff_aac_sbr_apply.L91f7", B.L91f7, some "ff_aac_sbr_apply.L9206"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L91f7.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L91f7]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9206"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9206") ?_; refine ⟨isSome_at L.L9206, ?_, ?_⟩; rw [T.L9206]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215") ?_; refine ⟨isSome_at L.L9215, ?_, ?_⟩; rw [T.L9215]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9206 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9206" ⟨"ff_aac_sbr_apply.L9206", B.L9206, some "ff_aac_sbr_apply.L9215"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9206.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9206]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215") ?_; refine ⟨isSome_at L.L9215, ?_, ?_⟩; rw [T.L9215]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215" ⟨"ff_aac_sbr_apply.L9215", B.L9215, some "ff_aac_sbr_apply.L9215_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 548960#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 216#64) 8 := by
      sep_mem hm; rfl
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215_1") ?_; refine ⟨isSome_at L.L9215_1, ?_, ?_⟩; rw [T.L9215_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe0, FrGe1, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215_1" ⟨"ff_aac_sbr_apply.L9215_1", B.L9215_1, some "ff_aac_sbr_apply.L9215_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe1, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 553952#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 272#64) 8 := by
      sep_mem hm; rfl
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp only [ga_c192]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215_2"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215_2") ?_; refine ⟨isSome_at L.L9215_2, ?_, ?_⟩; rw [T.L9215_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe1, FrGe2, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215_2" ⟨"ff_aac_sbr_apply.L9215_2", B.L9215_2, some "ff_aac_sbr_apply.L9215_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe2, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 555488#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 376#64) 8 := by
      sep_mem hm; rfl
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp only [ga_c192]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215_3"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215_3") ?_; refine ⟨isSome_at L.L9215_3, ?_, ?_⟩; rw [T.L9215_3]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215_3]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe2, FrGe3, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215_3" ⟨"ff_aac_sbr_apply.L9215_3", B.L9215_3, some "ff_aac_sbr_apply.L9215_4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215_3.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe3, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215_3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 552416#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 384#64) 8 := by
      sep_mem hm; rfl
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp only [ga_c192]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215_4"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215_4") ?_; refine ⟨isSome_at L.L9215_4, ?_, ?_⟩; rw [T.L9215_4]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215_4]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe3, FrGe4, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215_4" ⟨"ff_aac_sbr_apply.L9215_4", B.L9215_4, some "ff_aac_sbr_apply.L9215_5"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215_4.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe4, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215_4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 557024#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 264#64) 8 := by
      sep_mem hm; rfl
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp only [ga_c192]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9215_5"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9215_5") ?_; refine ⟨isSome_at L.L9215_5, ?_, ?_⟩; rw [T.L9215_5]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9215_5]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe4, FrGe5, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9215_5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9215_5" ⟨"ff_aac_sbr_apply.L9215_5", B.L9215_5, some "ff_aac_sbr_apply.L9290"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, hK, hCy, hc0, hst, hch, he, hnl1, hrbx, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L9215_5.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe5, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9215_5]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 2 ((u16 y.ftLim 0 : Nat) : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 138#64) 2 := by
      sep_mem hm; rfl
    have hL0b : u16 y.ftLim 0 < 2 ^ 15 := by have := hlim 0 (by omega); omega
    simp only [u16, u8, Nat.mul_zero, Nat.zero_add] at hL0b
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L929e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L929e") ?_; refine ⟨isSome_at L.L929e, ?_, ?_⟩; rw [T.L929e]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, 0, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, 0, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try ((try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [ga_r16 _ (by omega)]; try rfl)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr12, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGe5, FrGk, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9290 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9290" ⟨"ff_aac_sbr_apply.L9290", B.L9290, some "ff_aac_sbr_apply.L929e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi, hm⟩ := T.L9290.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9290]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hrcx, hrdx, hrsi, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L91c0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L91c0") ?_; refine ⟨isSome_at L.L91c0, ?_, ?_⟩; rw [T.L91c0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L929e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L929e") ?_; refine ⟨isSome_at L.L929e, ?_, ?_⟩; rw [T.L929e]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk + 1, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk + 1, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L929e]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk + 1, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk + 1, hK, hCy, hc0, hst, hch, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (show 1 ≤ y.nlim; omega)
    all_goals try (show kk + 1 < y.nlim; omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, FrGk, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L929e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L929e" ⟨"ff_aac_sbr_apply.L929e", B.L929e, some "ff_aac_sbr_apply.L929e_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L929e.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGk, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L929e]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L929e_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L929e_1") ?_; refine ⟨isSome_at L.L929e_1, ?_, ?_⟩; rw [T.L929e_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L929e_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L99fd"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hrdx, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp -implicitDefEqProofs only [hrdx, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, FrGk, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L929e_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L929e_1" ⟨"ff_aac_sbr_apply.L929e_1", B.L929e_1, some "ff_aac_sbr_apply.L9300"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hm⟩ := T.L929e_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L929e_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l1 : some ((u16 y.ftLim (kk + 1) : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk + 1) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp (disch := omega) only [ga_off2, hfl]
      all_goals first | omega | (rw [ga_u16 y.ftLim (kk + 1) (by omega)])
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L93d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L93d0") ?_; refine ⟨isSome_at L.L93d0, ?_, ?_⟩; rw [T.L93d0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9300"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9300") ?_; refine ⟨isSome_at L.L9300, ?_, ?_⟩; rw [T.L9300]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9300]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L98bc"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hr12, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a50"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hr13, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9300 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9300" ⟨"ff_aac_sbr_apply.L9300", B.L9300, some "ff_aac_sbr_apply.L9300_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hrsi, hm⟩ := T.L9300.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9300]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9300_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9300_1") ?_; refine ⟨isSome_at L.L9300_1, ?_, ?_⟩; rw [T.L9300_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9300_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9300_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9300_1" ⟨"ff_aac_sbr_apply.L9300_1", B.L9300_1, some "ff_aac_sbr_apply.L9300_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hrsi, hm⟩ := T.L9300_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9300_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9300_2"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9300_2") ?_; refine ⟨isSome_at L.L9300_2, ?_, ?_⟩; rw [T.L9300_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9300_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9300_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9300_2" ⟨"ff_aac_sbr_apply.L9300_2", B.L9300_2, some "ff_aac_sbr_apply.L9370"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hm⟩ := T.L9300_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9300_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9370"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9370") ?_; refine ⟨isSome_at L.L9370, ?_, ?_⟩; rw [T.L9370]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9386"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9386") ?_; refine ⟨isSome_at L.L9386, ?_, ?_⟩; rw [T.L9386]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9370 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9370" ⟨"ff_aac_sbr_apply.L9370", B.L9370, some "ff_aac_sbr_apply.L9386"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hm⟩ := T.L9370.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9370]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9386"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9386") ?_; refine ⟨isSome_at L.L9386, ?_, ?_⟩; rw [T.L9386]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9386]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9386 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9386" ⟨"ff_aac_sbr_apply.L9386", B.L9386, some "ff_aac_sbr_apply.L9386_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hm⟩ := T.L9386.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9386]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9386_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9386_1") ?_; refine ⟨isSome_at L.L9386_1, ?_, ?_⟩; rw [T.L9386_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9386_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp -implicitDefEqProofs only [hrax, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9386_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9386_1" ⟨"ff_aac_sbr_apply.L9386_1", B.L9386_1, some "ff_aac_sbr_apply.L93d0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hml, hmh, hrbx, hr12, hr13, hrax, hm⟩ := T.L9386_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9386_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l1 : some ((u16 y.ftLim (kk + 1) : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk + 1) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp (disch := omega) only [ga_off2, hfl]
      all_goals first | omega | (rw [ga_u16 y.ftLim (kk + 1) (by omega)])
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, hrax, hrbx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L93f0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L93f0") ?_; refine ⟨isSome_at L.L93f0, ?_, ?_⟩; rw [T.L93f0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9300"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9300") ?_; refine ⟨isSome_at L.L9300, ?_, ?_⟩; rw [T.L9300]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a50"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hrax, hrbx, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr13, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L93d0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L93d0" ⟨"ff_aac_sbr_apply.L93d0", B.L93d0, some "ff_aac_sbr_apply.L93f0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hle, hr12, hr13, hrsi, hm⟩ := T.L93d0.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L93d0]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9530"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9530") ?_; refine ⟨isSome_at L.L9530, ?_, ?_⟩; rw [T.L9530]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L93f0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L93f0" ⟨"ff_aac_sbr_apply.L93f0", B.L93f0, some "ff_aac_sbr_apply.L93f0_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr14, hr15, hrsi, hm⟩ := T.L93f0.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L93f0]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have l1 : some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 kk).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 88#64) 8 := by
      sep_mem hm; rfl
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l2 : some ((u16 y.ftLim kk : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 kk * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp (disch := omega) only [ga_off2, hfl]
      all_goals first | omega | (rw [ga_u16 y.ftLim kk (by omega)])
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr14, hr15, hrcx, hrdx, hrsi, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9520"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9520") ?_; refine ⟨isSome_at L.L9520, ?_, ?_⟩; rw [T.L9520]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L93f0_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L93f0_1") ?_; refine ⟨isSome_at L.L93f0_1, ?_, ?_⟩; rw [T.L93f0_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L93f0_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9bc5"; exfalso; rename_i hT; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Int.reduceNeg, u16, u8] at hT hLk hLk1 ⊢; exact hT (ga_t9bc5 _ _ _ (by omega) (by omega) (by omega) (by omega)))
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr14, hr15, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L93f0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L93f0_1" ⟨"ff_aac_sbr_apply.L93f0_1", B.L93f0_1, some "ff_aac_sbr_apply.L9440"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hrbx, hr12, hr14, hr15, hr13, hrsi, hm⟩ := T.L93f0_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L93f0_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrbx, hr14, hr15, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9458"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9458") ?_; refine ⟨isSome_at L.L9458, ?_, ?_⟩; rw [T.L9458]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9440"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9440") ?_; refine ⟨isSome_at L.L9440, ?_, ?_⟩; rw [T.L9440]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), ((u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), ((u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9440]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), ((u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), ((u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [hrbx]; congr 1; simp only [u16, u8]; omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9440 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9440" ⟨"ff_aac_sbr_apply.L9440", B.L9440, some "ff_aac_sbr_apply.L9458"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, cc, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hc1, hjc, hmj, hrbx, hr12, hr14, hr15, hr13, hrsi, hm⟩ := T.L9440.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9440]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have hjj : jj < 48 := by omega
    have hee : ee < 8 := by omega
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hrbx, hr12, hr14, hr15, hr13, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9440"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9440") ?_; refine ⟨isSome_at L.L9440, ?_, ?_⟩; rw [T.L9440]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj + 1, cc - 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj + 1, cc - 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9458"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9458") ?_; refine ⟨isSome_at L.L9458, ?_, ?_⟩; rw [T.L9458]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9458]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (show 1 ≤ cc - 1; omega)
    all_goals try (show BitVec.ofNat 64 (jj + 1) = _; first | (congr 1; omega) | (simp only [u16, u8] at hjc ⊢; congr 1; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hr14, hr15, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9458 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9458" ⟨"ff_aac_sbr_apply.L9458", B.L9458, some "ff_aac_sbr_apply.L9470"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hrbx, hr14, hr15, hr13, hrsi, hm⟩ := T.L9458.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9458]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hrbx, hr14, hr15, hr13, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9504"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9504") ?_; refine ⟨isSome_at L.L9504, ?_, ?_⟩; rw [T.L9504]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9470"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9470") ?_; refine ⟨isSome_at L.L9470, ?_, ?_⟩; rw [T.L9470]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1 + (u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1 + (u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9470]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1 + (u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1 + (u16 y.ftLim (kk + 1) - y.kx1 - (u16 y.ftLim kk - y.kx1)) % 8), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (rename_i hT; simp -implicitDefEqProofs only [Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hT; simp only [u16, u8] at hT hLk hLk1 hlt ⊢; omega)
    all_goals try (simp only [u16, u8] at hLk1 ⊢; rw [ga_r15 _ _ (by omega) (by omega)])
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr14, hr15, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9470 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9470" ⟨"ff_aac_sbr_apply.L9470", B.L9470, some "ff_aac_sbr_apply.L9470_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hmj, hjm, hj8, hrbx, hr15, hr13, hrsi, hm⟩ := T.L9470.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9470]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have hjj : jj + 8 ≤ 48 := by omega
    have hee : ee < 8 := by omega
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9470_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9470_1") ?_; refine ⟨isSome_at L.L9470_1, ?_, ?_⟩; rw [T.L9470_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9470_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9470_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9470_1" ⟨"ff_aac_sbr_apply.L9470_1", B.L9470_1, some "ff_aac_sbr_apply.L9504"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hmj, hjm, hj8, hrbx, hr15, hr13, hrsi, hm⟩ := T.L9470_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9470_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have hjj : jj + 8 ≤ 48 := by omega
    have hee : ee < 8 := by omega
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n, ga_foldp, ga_fold1p]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hrbx, hr15, hr13, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec, ga_c4n, ga_inc]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9470"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9470") ?_; refine ⟨isSome_at L.L9470, ?_, ?_⟩; rw [T.L9470]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj + 8, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj + 8, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9504"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9504") ?_; refine ⟨isSome_at L.L9504, ?_, ?_⟩; rw [T.L9504]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9504]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (show jj + 8 < _; simp -implicitDefEqProofs only [ga_add8, BitVec.toNat_ofNat] at *; simp only [u16, u8] at hj8 hjm ⊢; omega)
    all_goals try (dsimp only; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, ga_add8])
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr15, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9504 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9504" ⟨"ff_aac_sbr_apply.L9504", B.L9504, some "ff_aac_sbr_apply.L9520"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr13, hrsi, hm⟩ := T.L9504.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9504]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L952c"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L952c") ?_; refine ⟨isSome_at L.L952c, ?_, ?_⟩; rw [T.L952c]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, FrGb68, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9520 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9520" ⟨"ff_aac_sbr_apply.L9520", B.L9520, some "ff_aac_sbr_apply.L952c"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, hm⟩ := T.L9520.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9520]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L952c"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L952c") ?_; refine ⟨isSome_at L.L952c, ?_, ?_⟩; rw [T.L952c]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L952c]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L952c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L952c" ⟨"ff_aac_sbr_apply.L952c", B.L952c, some "ff_aac_sbr_apply.L9530"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, hm⟩ := T.L952c.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L952c]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9530"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9530") ?_; refine ⟨isSome_at L.L9530, ?_, ?_⟩; rw [T.L9530]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9530]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9530 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9530" ⟨"ff_aac_sbr_apply.L9530", B.L9530, some "ff_aac_sbr_apply.L9530_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, hm⟩ := T.L9530.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9530]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have l1 : some (Int.ofBytes (Int.toBytes 4 (↑y.limGains : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 166224#64) 4 := by
      sep_mem hm; rfl
    have lg : (loadInt s₀.dmem (lab "limgain" + BitVec.ofNat 64 y.limGains * 4#64) 4).isSome = true := by
      simp only [lab]
      rcases (by omega : y.limGains = 0 ∨ y.limGains = 1 ∨ y.limGains = 2 ∨ y.limGains = 3) with h | h | h | h <;> simp only [h, BitVec.ofNat_eq_ofNat, BitVec.reduceMul, BitVec.add_zero] <;> sep_mem hm <;> (simp -implicitDefEqProofs only [lab, ga_subL, ga_offL, BitVec.toNat_ofNat]; omega)
    simp only [lab] at lg
    obtain ⟨vlg, hvlg⟩ := Option.isSome_iff_exists.mp lg
    try simp only [lab] at hm
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (dq_revert_loads; simp (disch := omega) only [ga_c4]; intros)
    all_goals try (dq_revert_loads; simp only [hvlg, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (simp (disch := omega) only [ga_c4, lg]; done)
    all_goals try (simp only [lg]; done)
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, hrsi, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (simp (disch := omega) only [ga_c4, lg]; done)
    all_goals try (simp only [lg]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9617"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9617") ?_; refine ⟨isSome_at L.L9617, ?_, ?_⟩; rw [T.L9617]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9530_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9530_1") ?_; refine ⟨isSome_at L.L9530_1, ?_, ?_⟩; rw [T.L9530_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9530_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9b72"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hr12, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9b81"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hr12, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (intro; exfalso; simp only [u16, u8] at *; omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9530_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9530_1" ⟨"ff_aac_sbr_apply.L9530_1", B.L9530_1, some "ff_aac_sbr_apply.L95a0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hlt, hrsi, hm⟩ := T.L9530_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9530_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L95a0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L95a0") ?_; refine ⟨isSome_at L.L95a0, ?_, ?_⟩; rw [T.L95a0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L95a0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a55"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hr13, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L95a0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L95a0" ⟨"ff_aac_sbr_apply.L95a0", B.L95a0, some "ff_aac_sbr_apply.L95a0_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hlt, hml, hmh, hr14, hrax, hrsi, hm⟩ := T.L95a0.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L95a0]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L95a0_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L95a0_1") ?_; refine ⟨isSome_at L.L95a0_1, ?_, ?_⟩; rw [T.L95a0_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L95a0_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L95a0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L95a0_1" ⟨"ff_aac_sbr_apply.L95a0_1", B.L95a0_1, some "ff_aac_sbr_apply.L95a0_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hlt, hml, hmh, hr14, hrax, hrsi, hm⟩ := T.L95a0_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L95a0_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L95a0_2"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L95a0_2") ?_; refine ⟨isSome_at L.L95a0_2, ?_, ?_⟩; rw [T.L95a0_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L95a0_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp -implicitDefEqProofs only [hrax, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L95a0_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L95a0_2" ⟨"ff_aac_sbr_apply.L95a0_2", B.L95a0_2, some "ff_aac_sbr_apply.L9600"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hlt, hml, hmh, hr14, hrax, hm⟩ := T.L95a0_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L95a0_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l1 : some ((u16 y.ftLim (kk + 1) : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk + 1) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp (disch := omega) only [ga_off2, hfl]
      all_goals first | omega | (rw [ga_u16 y.ftLim (kk + 1) (by omega)])
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, hrax, hr14, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9600"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9600") ?_; refine ⟨isSome_at L.L9600, ?_, ?_⟩; rw [T.L9600]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L95a0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L95a0") ?_; refine ⟨isSome_at L.L95a0, ?_, ?_⟩; rw [T.L95a0]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a55"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hrax, hr14, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9600 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9600" ⟨"ff_aac_sbr_apply.L9600", B.L9600, some "ff_aac_sbr_apply.L9617"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, hm⟩ := T.L9600.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9600]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have l1 : some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 kk).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 88#64) 8 := by
      sep_mem hm; rfl
    have l2 : some (((u16 y.ftLim (kk) : Nat) : Int)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp only [gq_off2 _ _ _ (show 2 * (kk) < 2 ^ 64 by omega), hfl]
      all_goals first | omega | exact gq_u16 _ _ (by omega)
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (rename_i hx1 hx2 hx3; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2 hx3); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2 hx3)
    all_goals try (rename_i hx1 hx2; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2)
    all_goals try (rename_i hx1; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9617"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9617") ?_; refine ⟨isSome_at L.L9617, ?_, ?_⟩; rw [T.L9617])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9617])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_sub16 y.ftLim (kk) y.kx1 (by (try simp only [u16, u8]); omega) (by (try simp only [u16, u8]); omega)])
    all_goals try (intro; (try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_z16 y.ftLim (kk) (by (try simp only [u16, u8]); omega)])
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_z16 y.ftLim (kk) (by (try simp only [u16, u8]); omega)])
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9617 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9617" ⟨"ff_aac_sbr_apply.L9617", B.L9617, some "ff_aac_sbr_apply.L9617_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, himp, hrsi, hm⟩ := T.L9617.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
  try dsimp only
  simp only [B.L9617]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hLk := hlim kk (by omega)
  have hLk1 := hlim (kk + 1) (by omega)
  by_cases hlt : (u16 y.ftLim kk - y.kx1) < (u16 y.ftLim (kk + 1) - y.kx1)
  all_goals first | (have hrax := himp hlt) | (have hrax : True := trivial)
  all_goals (have phm : PLift _ := ⟨hm⟩; clear hm)
  all_goals vcgen
  all_goals (have hm := phm.down; clear phm)
  all_goals try subst s₀
  all_goals try (rename_i hx1 hx2 hx3; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2 hx3); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2 hx3)
  all_goals try (rename_i hx1 hx2; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2)
  all_goals try (rename_i hx1; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (simp (disch := decide) only [ga_off]; decide)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax]
  all_goals try (sep_mem hm; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
  all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
  all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9b90"; exfalso; clear hm; (try simp only [u16, u8] at hlt hLk hLk1); simp -implicitDefEqProofs (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_not, CondCode.interp_nc, StatusFlags.cf_from_result, dq_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow, Nat.mod_eq_of_lt] at hx3; (try split at hx3) <;> (try simp -implicitDefEqProofs (disch := omega) only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_not, CondCode.interp_nc, StatusFlags.cf_from_result, dq_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow, Nat.mod_eq_of_lt] at hx3) <;> omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9820"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9820") ?_; refine ⟨isSome_at L.L9820, ?_, ?_⟩; rw [T.L9820])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9617_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9617_1") ?_; refine ⟨isSome_at L.L9617_1, ?_, ?_⟩; rw [T.L9617_1])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L9617_1])
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
  all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
  all_goals try simp only [hr12, BitVec.ofInt_toInt]
  all_goals try exact Nat.le_refl _
  all_goals try (dq_guard_or; left; ga_var)
  all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
  all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
  all_goals try exact hnl1
  all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx]; simp (disch := ((try simp only [u16, u8]); omega)) only [gq_sw3264])
  all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrbx, hrsi, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9617_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9617_1" ⟨"ff_aac_sbr_apply.L9617_1", B.L9617_1, some "ff_aac_sbr_apply.L968d"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr13, hr12, hrsi, hm⟩ := T.L9617_1.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
  try dsimp only
  simp only [B.L9617_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + (555488#64 + BitVec.ofNat 64 (192 * ee))).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 232#64) 8 := by
    sep_mem hm; first | rfl | simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hLk := hlim kk (by omega)
  have hLk1 := hlim (kk + 1) (by omega)
  all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  all_goals vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try simp only [MachineData.dmem_mk, MachineData.regs_mk, MachineData.status_mk]
  all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
  all_goals try (dq_revert_loads; (try simp only [MachineData.dmem_mk, MachineData.regs_mk, MachineData.status_mk]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [MachineData.dmem_mk, MachineData.regs_mk, MachineData.status_mk]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [MachineData.dmem_mk, MachineData.regs_mk, MachineData.status_mk]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (simp (disch := decide) only [ga_off]; decide)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]
  all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
  all_goals try ((try simp (disch := ((try simp only [u16, u8]); omega)) only [gq_sw3264]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); (try simp only [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]); sep_mem hm; all_goals (simp -implicitDefEqProofs only [gq_asc, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega))
  all_goals try (sep_mem hm; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
  all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
  all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
  all_goals try (goal_has_str "ff_aac_sbr_apply.L96d3"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L96d3") ?_; refine ⟨isSome_at L.L96d3, ?_, ?_⟩; rw [T.L96d3])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L968d"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L968d") ?_; refine ⟨isSome_at L.L968d, ?_, ?_⟩; rw [T.L968d])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L968d])
  all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
  all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
  all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
  all_goals try simp only [hr12, BitVec.ofInt_toInt]
  all_goals try exact Nat.le_refl _
  all_goals try (dq_guard_or; left; ga_var)
  all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
  all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
  all_goals try exact hnl1
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); (try subst n); right; exact ⟨rfl, by omega⟩)
  all_goals try (gq_nomm; (try simp only [MachineData.regs_mk]); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]; simp (disch := ((try simp only [u16, u8]); omega)) only [gq_sw3264])
  all_goals try (gq_natg; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try (gq_nomm; (try simp only [MachineData.regs_mk]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try (gq_nomm; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr13, hr12, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try ((try simp only [MachineData.dmem_mk, MachineData.regs_mk]); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L968d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L968d" ⟨"ff_aac_sbr_apply.L968d", B.L968d, some "ff_aac_sbr_apply.L96d3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hpar, hrax, hr12, hr13, hrsi, hm⟩ := T.L968d.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch (by omega)] at hm
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
  try dsimp only
  simp only [B.L968d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hLk := hlim kk (by omega)
  have hLk1 := hlim (kk + 1) (by omega)
  all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  all_goals vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (simp (disch := decide) only [ga_off]; decide)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]
  all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
  all_goals try (sep_mem hm; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
  all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
  all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
  all_goals try (goal_has_str "ff_aac_sbr_apply.L96d3"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L96d3") ?_; refine ⟨isSome_at L.L96d3, ?_, ?_⟩; rw [T.L96d3])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L96d3])
  all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
  all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
  all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
  all_goals try simp only [hr12, BitVec.ofInt_toInt]
  all_goals try exact Nat.le_refl _
  all_goals try (dq_guard_or; left; ga_var)
  all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
  all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
  all_goals try exact hnl1
  all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try ((try dsimp only); (try (simp only [Mm, ApplyF]; rw [applyF_dpair y t₀ ch (by omega)])); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false,  Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L96d3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L96d3" ⟨"ff_aac_sbr_apply.L96d3", B.L96d3, some "ff_aac_sbr_apply.L96e1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hrax, hrbx, hr12, hr13, hrsi, hm⟩ := T.L96d3.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L96d3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L97b7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L97b7") ?_; refine ⟨isSome_at L.L97b7, ?_, ?_⟩; rw [T.L97b7])
    all_goals try (goal_has_str "ff_aac_sbr_apply.L96e1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L96e1") ?_; refine ⟨isSome_at L.L96e1, ?_, ?_⟩; rw [T.L96e1])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L96e1])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, ((u16 y.ftLim kk - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim kk - y.kx1)) % 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, ((u16 y.ftLim kk - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim kk - y.kx1)) % 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (gq_natg; clear hm; (try simp only [u16, u8] at hLk hLk1 hlt ⊢); omega)
    all_goals try (gq_natg; clear hm; have h1 := gq_ne1 _ _ (by assumption) (by omega) (by omega); (try simp only [u16, u8] at hLk hLk1 hlt ⊢); omega)
    all_goals try (gq_nomm; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try simp only [MachineData.dmem_mk, MachineData.regs_mk]); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L96e1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L96e1" ⟨"ff_aac_sbr_apply.L96e1", B.L96e1, some "ff_aac_sbr_apply.L9720"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hrax, hr13, hrsi, hm⟩ := T.L96e1.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L96e1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi]
    all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9290"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9290") ?_; refine ⟨isSome_at L.L9290, ?_, ?_⟩; rw [T.L9290]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L983f"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L983f") ?_; refine ⟨isSome_at L.L983f, ?_, ?_⟩; rw [T.L983f]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try dsimp only
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9720 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9720" ⟨"ff_aac_sbr_apply.L9720", B.L9720, some "ff_aac_sbr_apply.L9731"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hj1, hj2, hjp, hrbx, hr12, hrax, hr13, hrsi, hm⟩ := T.L9720.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9720]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9731"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9731") ?_; refine ⟨isSome_at L.L9731, ?_, ?_⟩; rw [T.L9731]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9731])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9731 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9731" ⟨"ff_aac_sbr_apply.L9731", B.L9731, some "ff_aac_sbr_apply.L9731_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hj1, hj2, hjp, hrbx, hr12, hrax, hr13, hrsi, hm⟩ := T.L9731.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9731]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals ((try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]))
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9731_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9731_1") ?_; refine ⟨isSome_at L.L9731_1, ?_, ?_⟩; rw [T.L9731_1])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9731_1])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9731_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9731_1" ⟨"ff_aac_sbr_apply.L9731_1", B.L9731_1, some "ff_aac_sbr_apply.L97b7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hj1, hj2, hjp, hrbx, hr12, hrax, hr13, hrsi, hm⟩ := T.L9731_1.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    try dsimp only
    simp only [B.L9731_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try simp only [Mm, ApplyF, FrX, FrGb, DdA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L96e1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L96e1") ?_; refine ⟨isSome_at L.L96e1, ?_, ?_⟩; rw [T.L96e1])
    all_goals try (goal_has_str "ff_aac_sbr_apply.L97b7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L97b7") ?_; refine ⟨isSome_at L.L97b7, ?_, ?_⟩; rw [T.L97b7])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L97b7])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (jj + 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (jj + 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, FrX, FrGb, DdA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L97b7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L97b7" ⟨"ff_aac_sbr_apply.L97b7", B.L97b7, some "ff_aac_sbr_apply.L97f0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hj1, hj2, hjp, hrbx, hr12, hrax, hr13, hrsi, hm⟩ := T.L97b7.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch (by omega)] at hm
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
  try dsimp only
  simp only [B.L97b7]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hLk := hlim kk (by omega)
  have hLk1 := hlim (kk + 1) (by omega)
  all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  all_goals vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (simp (disch := decide) only [ga_off]; decide)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
  all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
  all_goals try (sep_mem hm; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
  all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
  all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
  all_goals try (goal_has_str "ff_aac_sbr_apply.L97f0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L97f0") ?_; refine ⟨isSome_at L.L97f0, ?_, ?_⟩; rw [T.L97f0]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9731"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9731") ?_; refine ⟨isSome_at L.L9731, ?_, ?_⟩; rw [T.L9731]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9720"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9720") ?_; refine ⟨isSome_at L.L9720, ?_, ?_⟩; rw [T.L9720]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
  all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
  all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
  all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
  all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
  all_goals try simp only [hr12, BitVec.ofInt_toInt]
  all_goals try exact Nat.le_refl _
  all_goals try (dq_guard_or; left; ga_var)
  all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
  all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
  all_goals try exact hnl1
  all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try ((try dsimp only); (try (simp only [Mm, ApplyF]; rw [applyF_dpair y t₀ ch (by omega)])); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false,  Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L97f0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L97f0" ⟨"ff_aac_sbr_apply.L97f0", B.L97f0, some "ff_aac_sbr_apply.L9820"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hj1, hj2, hjp, hrbx, hr12, hrax, hr13, hrsi, hm⟩ := T.L97f0.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L97f0]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); (try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]
    all_goals try ((try simp only [gq_rb _ _ 555488 555488 0 rfl, gq_rb _ _ 555492 555488 4 rfl, gq_rb _ _ 557024 557024 0 rfl, gq_rb _ _ 557028 557024 4 rfl, gq_rb _ _ 553956 553952 4 rfl, gq_rb _ _ 552420 552416 4 rfl, gq_rb _ _ 548964 548960 4 rfl]); sep_mem hm; done)
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9731"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9731") ?_; refine ⟨isSome_at L.L9731, ?_, ?_⟩; rw [T.L9731]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9720"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9720") ?_; refine ⟨isSome_at L.L9720, ?_, ?_⟩; rw [T.L9720]; first | (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) | (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, jj, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrbx, hr12, hrax, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9820 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9820" ⟨"ff_aac_sbr_apply.L9820", B.L9820, some "ff_aac_sbr_apply.L983f"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hge, hrsi, hm⟩ := T.L9820.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9820]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (rename_i hx1 hx2 hx3; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2 hx3); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2 hx3)
    all_goals try (rename_i hx1 hx2; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2)
    all_goals try (rename_i hx1; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9290"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9290") ?_; refine ⟨isSome_at L.L9290, ?_, ?_⟩; rw [T.L9290])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, Nat.mod_eq_of_lt, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L983f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L983f" ⟨"ff_aac_sbr_apply.L983f", B.L983f, some "ff_aac_sbr_apply.L9860"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr12, hrax, hrsi, hm⟩ := T.L983f.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L983f]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (rename_i hx1 hx2 hx3; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2 hx3); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2 hx3)
    all_goals try (rename_i hx1 hx2; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2)
    all_goals try (rename_i hx1; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9860"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9860") ?_; refine ⟨isSome_at L.L9860, ?_, ?_⟩; rw [T.L9860])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9860])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, (u16 y.ftLim kk - y.kx1), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, Nat.mod_eq_of_lt, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, CondCode.interp_nc, CondCode.interp_c, StatusFlags.cf_from_result, dq_cf64, dq_cf32]; split <;> (rename_i hc; first | rfl | (exfalso; clear hm; (try simp only [u16, u8] at *); simp -implicitDefEqProofs (disch := omega) only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt, Nat.reducePow] at hc; omega)))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9860 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9860" ⟨"ff_aac_sbr_apply.L9860", B.L9860, some "ff_aac_sbr_apply.L9860_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr12, hml, hmh, hrbx, hrax, hrsi, hm⟩ := T.L9860.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9860]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9860_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9860_1") ?_; refine ⟨isSome_at L.L9860_1, ?_, ?_⟩; rw [T.L9860_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9860_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9860_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9860_1" ⟨"ff_aac_sbr_apply.L9860_1", B.L9860_1, some "ff_aac_sbr_apply.L9860_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr12, hml, hmh, hrbx, hrax, hrsi, hm⟩ := T.L9860_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9860_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9860_2"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9860_2") ?_; refine ⟨isSome_at L.L9860_2, ?_, ?_⟩; rw [T.L9860_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9860_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9860_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9860_2" ⟨"ff_aac_sbr_apply.L9860_2", B.L9860_2, some "ff_aac_sbr_apply.L9860_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr12, hml, hmh, hrbx, hrax, hrsi, hm⟩ := T.L9860_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9860_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9860_3"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9860_3") ?_; refine ⟨isSome_at L.L9860_3, ?_, ?_⟩; rw [T.L9860_3]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9860_3]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp -implicitDefEqProofs only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp -implicitDefEqProofs only [hrax, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9860_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9860_3" ⟨"ff_aac_sbr_apply.L9860_3", B.L9860_3, some "ff_aac_sbr_apply.L98bc"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hr12, hml, hmh, hrbx, hrax, hm⟩ := T.L9860_3.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9860_3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l1 : some ((u16 y.ftLim (kk + 1) : Nat) : Int) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk + 1) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp (disch := omega) only [ga_off2, hfl]
      all_goals first | omega | (rw [ga_u16 y.ftLim (kk + 1) (by omega)])
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hrcx, hrdx, hrax, hrbx, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec, ga_c4n, ga_inc]); (try simp -implicitDefEqProofs only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9290"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9290") ?_; refine ⟨isSome_at L.L9290, ?_, ?_⟩; rw [T.L9290]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9860"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9860") ?_; refine ⟨isSome_at L.L9860, ?_, ?_⟩; rw [T.L9860]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm + 1, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a5a"; exfalso; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs only [hrax, hrbx, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp -implicitDefEqProofs only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp -implicitDefEqProofs only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hrbx, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L98bc (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L98bc" ⟨"ff_aac_sbr_apply.L98bc", B.L98bc, some "ff_aac_sbr_apply.L98e0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  exact (T.L98bc.mp hs).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L98e0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L98e0" ⟨"ff_aac_sbr_apply.L98e0", B.L98e0, some "ff_aac_sbr_apply.L9927"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, hae, hHA, -⟩ := hc
  have hHA' := PLift.up hHA
  clear hHA
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hbx, hm⟩ := T.L98e0.mp hs
  clear hs
  have hlv : ch ≠ 0 → y.idAac = 1#32 := hK.2.live hst
  have hdc : (y.d ch).ypos ≤ 1 ∧ (y.d ch).te.length = 10 ∧ (y.d ch).nenv ≤ 8
      ∧ (∀ e, e ≤ (y.d ch).nenv → u8 (y.d ch).te e ≤ 19) ∧ u8 (y.d ch).te 9 ≤ 19
      ∧ (y.d ch).idx.toNat % 2 ^ 32 ≤ 515 ∧ (y.d ch).idx.toNat / 2 ^ 32 < 4 := by
    unfold Args.d; split
    · obtain ⟨-, -, h3, -, h5, -, -, -, h9, h10, -, h12, h13, -, -, h16⟩ :=
        hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h5, (h16 hst).2.1, h10, h12, h13⟩
    · obtain ⟨-, -, h3, -, h5, -, -, -, h9, h10, -, h12, h13, -, -, h16⟩ :=
        hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h5, (h16 ⟨hst, hlv (by assumption)⟩).2.1, h10, h12, h13⟩
  clear hlv
  have hyp : (y.d ch).ypos ≤ 1 := hdc.1
  have htl : (y.d ch).te.length = 10 := hdc.2.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  rw [gn_hfY (dA t₀ ch) (y.d ch).ypos hyp] at hm
  simp only [DScW] at hm
  rw [gn_te10 (y.d ch).te htl] at hm
  simp only [Mm, ApplyF, FrGA, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
    arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rw [gn_call_res_n k (0x290 + k) hSt (by omega)] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14596#64)))] as Re hRe
  obtain ⟨v0, v1, hm⟩ := gn_ea hm
  subst hRe
  simp only [BitVec.add_assoc, BitVec.reduceAdd, cell4] at hm
  simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hbx
  have hsw := gn_sw _ (show (y.d ch).ypos < 2 ^ 31 by omega)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L98e0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  all_goals try simp only [hsw, gn_m19, gn_rdi] at *
  -- the `jae` trap branch: ypos ≤ 1 < 3
  all_goals try (
    rename_i hnc
    rw [CondCode.interp_nc_sub64 _ _ _ rfl] at hnc
    simp -implicitDefEqProofs only [BitVec.toNat_ofNat, decide_eq_true_eq, Nat.reducePow, Nat.reduceMod] at hnc
    omega)
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, hbx⟩ := hR.down
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (656 + k) (t₀.regs.get64 .rsp - 464#64),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      24 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + (BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos) + 19456#64))))),
      (16128 - 24 * (if ch = 0 then y.d0 else y.d1).ypos) ?@ (t₀.regs.get64 .rsi + (166176#64 +
        (BitVec.ofNat 64 (128 + 88768 * ch) + (69936#64 + BitVec.ofNat 64 (24 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      20480 ?@ (t₀.regs.get64 .rsi + 488544#64),
      1536 ?@ (t₀.regs.get64 .rsi + 553952#64), 1536 ?@ (t₀.regs.get64 .rsi + 555488#64),
      1536 ?@ (t₀.regs.get64 .rsi + 557024#64),
      4160 ?@ ((_root_.Executable.labels cenv).label "ff_sbr_noise_table").toBitVec, 16 ?@ ((_root_.Executable.labels cenv).label "ps_noise0").toBitVec,
      48 ?@ ((_root_.Executable.labels cenv).label "ps_noise13").toBitVec, 16 ?@ ((_root_.Executable.labels cenv).label "ps_noise2").toBitVec,
      4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_6").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_7").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_8").toBitVec,
      4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_9").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_10").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_12").toBitVec,
      Int.toBytes 16 0x3000001ff =@ ((_root_.Executable.labels cenv).label "LCPI17_11").toBitVec,
      Int.toBytes 4 y.reset.toInt =@ (t₀.regs.get64 .rsi + 166200#64),
      Int.toBytes 4 y.smooth.toInt =@ (t₀.regs.get64 .rsi + 166232#64),
      Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64),
      Int.toBytes 4 (y.m1 : Int) =@ (t₀.regs.get64 .rsi + 166272#64),
      Int.toBytes 8 e.fs.hfs.gfilt.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559944#64),
      Int.toBytes 8 e.fs.hfs.noise0.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559952#64),
      Int.toBytes 8 e.fs.hfs.noise1.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559960#64),
      Int.toBytes 8 e.fs.hfs.noise2.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559968#64),
      Int.toBytes 8 e.fs.hfs.noise3.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559976#64),
      Int.toBytes 4 ((if ch = 0 then y.d0 else y.d1).nenv : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 8#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88732#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 1 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88733#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 2 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88734#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 3 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88735#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 4 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88736#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 5 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88737#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 6 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88738#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 7 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88739#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 8 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88740#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64))),
      Int.toBytes 4 v0.toInt =@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14596#64))),
      Int.toBytes 4 v1.toInt =@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14600#64))),
      Int.toBytes 8 (if ch = 0 then y.d0 else y.d1).idx.toInt =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88748#64)))] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  rw [hae]
  refine MachineWP.CallsTo.of_procSpec
    (⟨Rc, y.reset, y.smooth, y.kx1, y.m1, (if ch = 0 then y.d0 else y.d1).nenv,
      fun i => ((if ch = 0 then y.d0 else y.d1).te.getD i 0).toNat, v0, v1,
      (if ch = 0 then y.d0 else y.d1).idx, (if ch = 0 then y.d0 else y.d1).ypos⟩ : HfArgs) hHA'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks]
    sep_mem hm
    sep_close hm
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks])
  · exact gn_al_rsp _ hCy.2.2.2.2.2.1
  · exact gn_al16 hCy.2.2.1
  · exact gn_alD _ ch hCy.2.2.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2
  · exact (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.2.2.2.2.1
  · exact hCy.1.2.2.2.2.1
  · exact hCy.1.2.2.2.1
  · exact hdc.2.2.1
  · exact hdc.2.2.2.1
  · exact hdc.2.2.2.2.1
  · exact hdc.2.2.2.2.2.1
  · exact hdc.2.2.2.2.2.2
  · exact hyp
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks, gn_hio, arg3] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    -- G1: the post's `f_indexnoise`/`f_indexsine` cell comes back bounded (`HfIdxOut`)
    sep_pull hm' [gnIdx (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88748#64)))] as Ri hRi
    obtain ⟨i, hi1, hi2, hm'⟩ := gn_idx hm'
    subst hRi
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L9927]
      refine ⟨hC, ⟨hrsp', hrbp'⟩, ch, c0, hch, hc0, ?_, ?_⟩
      · rw [hbx']
        simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
        · have hyp0 : y.d0.ypos ≤ 1 := by simpa using hyp
          have htl0 : y.d0.te.length = 10 := by simpa using htl
          refine ⟨{ y with d0 := { y.d0 with idx := i } }, hK, gn_applyC_idx0 hCy i hi1 hi2, ?_⟩
          simp only [Mm, ApplyF, DArrW, Blocks]
          rw [gn_hfY (dA t₀ 0) y.d0.ypos hyp0]
          simp only [DScW]
          rw [gn_te10 _ htl0]
          simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, cell4, sbrA, arg0,
            arg1, arg3, arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd]
          rw [gn_call_res_n k (0x290 + k) hSt (by omega)]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self, dA, Args.d, Nat.reducePow, Nat.reduceSub,
            Nat.reduceMod, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte,
            Nat.one_ne_zero] at hm' ⊢
          simp only [AcW, OutW, dsN] at hm' ⊢
          rw [gn_m38, gn_split44 (t₀.regs.get64 .rsi + 180900#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          sep_close hm'
        · have hyp0 : y.d1.ypos ≤ 1 := by simpa using hyp
          have htl0 : y.d1.te.length = 10 := by simpa using htl
          refine ⟨{ y with d1 := { y.d1 with idx := i } }, hK, gn_applyC_idx1 hCy i hi1 hi2, ?_⟩
          simp only [Mm, ApplyF, DArrW, Blocks]
          rw [gn_hfY (dA t₀ 1) y.d1.ypos hyp0]
          simp only [DScW]
          rw [gn_te10 _ htl0]
          simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, cell4, sbrA, arg0,
            arg1, arg3, arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd]
          rw [gn_call_res_n k (0x290 + k) hSt (by omega)]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self, dA, Args.d, Nat.reducePow, Nat.reduceSub,
            Nat.reduceMod, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte,
            Nat.one_ne_zero] at hm' ⊢
          simp only [AcW, OutW, dsN] at hm' ⊢
          rw [gn_m38, gn_split44 (t₀.regs.get64 .rsi + 269668#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          sep_close hm'
    · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9927 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9927" ⟨"ff_aac_sbr_apply.L9927", B.L9927, some "ff_aac_sbr_apply.L9934"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ch, c0, hch, hc0, hrbx, y, hK, hCy, hm⟩ := T.L9927.mp hs
  clear hs
  have hyp := gq_yp hCy ch
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9927]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrbx]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9934"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9934") ?_; refine ⟨isSome_at L.L9934, ?_, ?_⟩; rw [T.L9934])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9934])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrbx] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrbx] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrbx] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, ?_, ?_⟩)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (gq_is_mod; (try dsimp only); (try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); (try rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by omega)]); (try simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]); (try omega); (try exact gq_rax4 _ hyp))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrbx, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9934 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934" ⟨"ff_aac_sbr_apply.L9934", B.L9934, some "ff_aac_sbr_apply.L9934_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, hr12, y, hK, hCy, hrax, hm⟩ := T.L9934.mp hs
  clear hs
  have dqs_sete1 : ∀ r d : BitVec 64, (r.replaceLow (BitVec.ofNat 8 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (BitVec.setWidth 32 d).toInt)) - 1#32 == BitVec.zero 32).toNat)).toNat % 256 = if BitVec.setWidth 32 d = 1#32 then 1 else 0 := by
    intro r d
    rw [BitVec.toNat_replaceLow8_mod, BitVec.toNat_ofNat, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    generalize BitVec.setWidth 32 d = a
    by_cases h1 : a = 1#32
    · subst h1; decide
    · rw [if_neg h1, show (a - 1#32 == BitVec.zero 32) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; intro h2; apply h1; have h3 := congrArg (· + 1#32) h2; simp only [BitVec.sub_add_cancel, BitVec.zero_eq, BitVec.zero_add] at h3; exact h3]; rfl
  have hyp := gq_yp hCy ch
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9934]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9934_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9934_1") ?_; refine ⟨isSome_at L.L9934_1, ?_, ?_⟩; rw [T.L9934_1])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9934_1])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sbrA, arg1, dA, BitVec.reduceMul, BitVec.reduceAdd, BitVec.zero_add, BitVec.add_zero, BitVec.reduceOfNat]; first | (with_reducible rfl) | ac_rfl)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr12]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp -implicitDefEqProofs (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (exfalso; rename_i hcc; simp -implicitDefEqProofs only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Nat.not_lt, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.reduceToNat, BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ite_true, ite_false, Nat.one_ne_zero, reduceIte] at hcc hrax; omega)
    all_goals try (dsimp only; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false])
    all_goals try (simp only [sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.zero_mul, BitVec.one_mul, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try (rw [BitVec.add_comm (31024#64)]; simp only [dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try (simp only [Args.d, ite_true, ite_false, Nat.one_ne_zero, reduceIte] at hrax ⊢; exact hrax)
    all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Args.d, ite_true, ite_false, Nat.one_ne_zero, reduceIte, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod] at hrax ⊢; omega)
    all_goals try (with_reducible exact dqs_sete1 _ (t₀.regs.get64 .rdx))
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); simp -implicitDefEqProofs only [BitVec.toNat_replaceLow8_mod, BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_of_le (Bool.toNat_le _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9934_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934_1" ⟨"ff_aac_sbr_apply.L9934_1", B.L9934_1, some "ff_aac_sbr_apply.L9934_2"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hxe, hXG, -⟩ := hc
  have hXG' := PLift.up hXG
  clear hXG
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h12, h9, hsi, hdi, hrb, y, hK, hCy, hax, hcx, hm⟩ := T.L9934_1.mp hs
  clear hs
  have hdc : (y.d ch).ypos ≤ 1 ∧ (y.d ch).te.length = 10 ∧ u8 (y.d ch).te 9 ≤ 19 := by
    unfold Args.d; split
    · obtain ⟨-, -, h3, -, -, -, -, -, h9, h10, -⟩ := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h10⟩
    · obtain ⟨-, -, h3, -, -, -, -, -, h9, h10, -⟩ := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h10⟩
  have hyp : (y.d ch).ypos ≤ 1 := hdc.1
  have htl : (y.d ch).te.length = 10 := hdc.2.1
  have hte9 : u8 (y.d ch).te 9 ≤ 19 := hdc.2.2
  have hkx0 : y.kx0 ≤ 32 := hCy.1.1
  have hkx1 : y.kx1 ≤ 32 := hCy.1.2.1
  have hm0 : y.kx0 + y.m0 ≤ 64 := hCy.1.2.2.1
  have hm1 : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  rw [gn_y3 (dA t₀ ch + 0x7930#64) (y.d ch).ypos hyp] at hm
  simp only [DScW] at hm
  rw [gn_byte_split (y.d ch).te _ 9 (by omega) (by omega)] at hm
  simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
    arg4, lab, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rw [gn_x2 (t₀.regs.get64 .rsi) ch (by omega), gn_call_res_n k (0x60 + k) hSt (by omega)] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h12, h9, hsi, hdi, hax, hcx, hrb⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L9934_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, h12, h9, hsi, hdi, hax, hcx, hrb⟩ := hR.down
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d]
    at hsi hdi hax hcx
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (96 + k) (t₀.regs.get64 .rsp - 464#64),
      19456 ?@ (t₀.regs.get64 .rsi + (509024#64 + BitVec.ofNat 64 (19456 * ch))),
      10240 ?@ (t₀.regs.get64 .rsi + 478304#64),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (1 - (if ch = 0 then y.d0 else y.d1).ypos)))))),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
      Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64),
      Int.toBytes 4 (y.m0 : Int) =@ (t₀.regs.get64 .rsi + 166268#64),
      Int.toBytes 4 (y.m1 : Int) =@ (t₀.regs.get64 .rsi + 166272#64),
      [(if ch = 0 then y.d0 else y.d1).te.getD 9 0] =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64)))] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  rw [hxe]
  refine MachineWP.CallsTo.of_procSpec
    (⟨Rc, BitVec.ofNat 32 y.kx0, BitVec.ofNat 32 y.kx1, BitVec.ofNat 32 y.m0, BitVec.ofNat 32 y.m1,
      BitVec.ofNat 8 ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat⟩ : XGenArgs) hXG'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks]
    simp only [gn_te, gn_c4 _ (show y.kx0 < 2 ^ 31 by omega), gn_c4 _ (show y.kx1 < 2 ^ 31 by omega),
      gn_c4 _ (show y.m0 < 2 ^ 31 by omega), gn_c4 _ (show y.m1 < 2 ^ 31 by omega),
      gn_tb1 _ (show ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat < 128 by omega)]
    sep_mem hm
    sep_close hm
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h9,
    BitVec.toNat_ofNat]; omega)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks] at hpost
    simp only [gn_te, gn_c4 _ (show y.kx0 < 2 ^ 31 by omega), gn_c4 _ (show y.kx1 < 2 ^ 31 by omega),
      gn_c4 _ (show y.m0 < 2 ^ 31 by omega), gn_c4 _ (show y.m1 < 2 ^ 31 by omega),
      gn_tb1 _ (show ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat < 128 by omega)] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L9934_2]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩
      all_goals try (simp only [h12', h14', h12, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
      all_goals try (rw [hbx']; exact hrb)
      have hyp' : (y.d ch).ypos ≤ 1 := hyp
      have htl' : (y.d ch).te.length = 10 := htl
      simp only [Mm, ApplyF]
      rw [applyF_dpair y t₀ ch hch]
      simp only [DArrW, Blocks]
      rw [gn_y3 (dA t₀ ch + 0x7930#64) (y.d ch).ypos hyp']
      simp only [DScW]
      rw [gn_byte_split (y.d ch).te _ 9 (by omega) (by omega)]
      simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
        arg4, lab, BitVec.add_assoc, BitVec.reduceAdd]
      rw [gn_x2 (t₀.regs.get64 .rsi) ch (by omega), gn_call_res_n k (0x60 + k) hSt (by omega)]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, dA, Args.d, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hm' ⊢
      sep_close hm'
    · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9934_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934_2" ⟨"ff_aac_sbr_apply.L9934_2", B.L9934_2, some "ff_aac_sbr_apply.L99c6"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, hr12, hr14, hbl, y, hK, hCy, hm⟩ := T.L9934_2.mp hs
  clear hs
  have hbl2 : (s₀.regs.get64 Reg64.rbx).toNat % 256 < 2 := by rw [hbl]; split <;> decide
  have ga_arg : ∀ (c : BitVec 8) (r : BitVec 64), r.toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0) →
      (!(c &&& BitVec.setWidth 8 r == BitVec.zero 8)) = true → BitVec.setWidth 32 (arg2 t₀) = 1#32 := by
    intro c r h hx
    by_cases hP : BitVec.setWidth 32 (arg2 t₀) = 1#32
    · exact hP
    rw [if_neg hP] at h
    have h0 : BitVec.setWidth 8 r = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [h0, show BitVec.zero 8 = 0#8 from rfl, BitVec.and_zero] at hx
    simp at hx
  have hyp := gq_yp hCy ch
  obtain ⟨chv, hchv1, hchv2⟩ : ∃ v, ch ≤ v ∧ v ≤ ch := ⟨ch, Nat.le_refl _, Nat.le_refl _⟩
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9934_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have ga_byte0 : ∀ c0 : BitVec 32, BitVec.ofInt 8 (Int.ofBytes (List.take 1 (Int.toBytes 4 c0.toInt))) = c0.setWidth 8 := by
      intro c0
      rw [← BitVec.ofInt_ofBytes_take 8 1 rfl]
      have h := congrArg (BitVec.setWidth 8) (BitVec.ofInt_ofBytes_toBytes 32 4 rfl c0)
      rw [← h]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
      omega
    have ga_test0 : ∀ (c0 : BitVec 32) (r : BitVec 64), c0.getLsbD 0 = false → r.toNat % 256 < 2 →
        (BitVec.ofInt 8 (Int.ofBytes (List.take 1 (List.drop 0 (Int.toBytes 4 c0.toInt)))) &&& BitVec.setWidth 8 r
          == BitVec.zero 8) = true := by
      intro c0 r h0 hr
      rw [List.drop_zero, ga_byte0]
      simp only [beq_iff_eq]
      have hc : c0.toNat % 2 = 0 := by
        simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_false_iff_not] at h0
        omega
      rw [show BitVec.zero 8 = 0#8 from rfl]
      apply BitVec.eq_of_toNat_eq
      simp -implicitDefEqProofs only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]
      rcases (by omega : r.toNat % 2 ^ 8 = 0 ∨ r.toNat % 2 ^ 8 = 1) with h | h <;> rw [h]
      · simp
      · rw [Nat.and_one_is_mod]; omega
    all_goals try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    all_goals try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    all_goals vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (exfalso; have hx := ‹(!(_ &&& _ == BitVec.zero 8)) = true›; simp only [BitVec.sub_self, BitVec.toNat_zero, ga_test0 c0 _ (by simpa using hc0) hbl2, Bool.not_true, Bool.false_eq_true] at hx)
    all_goals try (sep_mem hm <;> simp [Int.toBytes_length]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L7682"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7682") ?_; refine ⟨isSome_at L.L7682, ?_, ?_⟩; rw [T.L7682]; first | (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩) | (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a02"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a02") ?_; refine ⟨isSome_at L.L9a02, ?_, ?_⟩; rw [T.L9a02]; first | (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩) | (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L99c6])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩)
    all_goals try (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩)
    all_goals try (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩)
    all_goals try (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (obtain rfl := Nat.le_antisymm hchv2 hchv1)
    all_goals try (sep_mem hm; (try simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl, BitVec.ofInt_toInt, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr14, hr12, arg1, sbrA]); first | rfl | (simp only [BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceGetLsbD, BitVec.getLsbD_zero, BitVec.reduceOfNat]; done) | (simp; done))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hr14, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, FrL, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)

end Kraken.Examples.Sbr.Apply

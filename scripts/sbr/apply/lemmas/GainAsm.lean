
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

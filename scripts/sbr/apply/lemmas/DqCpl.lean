set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## DqCpl helper lemmas (apply-dqcpl) -/

/-- The decoder-state facts the coupled dequantisation needs. -/
theorem dq_facts {x : Args} {t : MachineData} (h : ApplyC x t) :
    x.d0.nenv ≤ 8 ∧ (∀ e, e ≤ x.d0.nenv → u8 x.d0.freqRes e ≤ 1) ∧ x.d0.freqRes.length = 9
      ∧ x.d0.nnoise ≤ 2 ∧ x.n0 ≤ 48 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 := by
  obtain ⟨⟨-, -, -, -, -, -, -, h0, h1, hq, -, -, -, ⟨hl, -, -, -, hne, hfr, hnn, -⟩, -⟩, -⟩ := h
  exact ⟨hne, hfr, hl, hnn, Nat.le_trans h0 (by decide), h1, hq⟩

omit [CodeEnv] in
/-- Re-basing an address `a + X + c` to the block base `a + c0`. -/
theorem adr_rb (a X c c0 c1 : BitVec 64) (h : c0 + c1 = c) : a + X + c = a + c0 + (X + c1) := by
  subst h; ac_rfl

omit [CodeEnv] in
/-- Re-basing `a + c + E + K + d` (a pointer into another array plus a negative offset). -/
theorem adr_shift (a c E K d c' : BitVec 64) (h : c + d = c') :
    a + c + E + K + d = a + c' + (E + K) := by
  subst h; ac_rfl

omit [CodeEnv] in
/-- A load inside a known cell reads the cell's bytes there. -/
theorem Mem.Val.loadInt_slice_split {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a addr : BitVec w}
    {bs : List UInt8} {n : Nat} (h : m =⋆ H) (hs : Mem.Split (bs =@ a) R H)
    (hin : (addr - a).toNat + n ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    m.loadInt addr n = some (Int.ofBytes ((bs.drop (addr - a).toNat).take n)) := by
  rw [hs] at h
  exact Mem.loadInt_slice h hin hw

section IncSpec
variable {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}
/-- `incl %r32`: the 32-bit successor, zero-extended; the carry flag is kept. -/
@[spec] theorem MachineWP.inc32_reg_spec_dq (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r (v.setWidth 64),
              status := StatusFlags.from_result v
                { cf := s.status.cf,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                  of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    simp only [Reg64s.get_low32, Reg64s.set_low32]; exact hP)
end IncSpec

omit [CodeEnv] in
theorem dq_xlo_zext (v : BitVec 64) : BitVec.extractLsb' 0 64 (v.setWidth 128) = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := v.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

omit [CodeEnv] in
theorem dq_inc32 (n : Nat) (h : n ≤ 2) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 n)) + 1)
      = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.ofInt_natCast, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

omit [CodeEnv] in
/-- A load at a `Blocks` entry's base: present it as `base + 0` for `sep_mem`. -/
theorem dq_isSome_add0 {m : Mem 64} {a : BitVec 64} {n : Nat}
    (h : (m.loadInt (a + 0) n).isSome = true) : (m.loadInt a n).isSome = true := by
  simpa using h

omit [CodeEnv] in
theorem dq_c4_val (n : Nat) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int))))
      = BitVec.setWidth 64 (BitVec.ofNat 32 n) := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast]

omit [CodeEnv] in
theorem dq_ne0 (n : Nat) (h : n < 2 ^ 32)
    (hz : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 n)) == BitVec.zero 32) = false) :
    0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp at hz
  · exact h0

-- address re-basing for the noise arrays (r9 + idx + disp → block base + offset)
omit [CodeEnv] in
theorem dq_a_3e3f5 (a X : BitVec 64) : a + X + 0x3e3f5#64 = a + 0x3e3f0#64 + (X + 0x5#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e3f6 (a X : BitVec 64) : a + X + 0x3e3f6#64 = a + 0x3e3f0#64 + (X + 0x6#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e3f7 (a X : BitVec 64) : a + X + 0x3e3f7#64 = a + 0x3e3f0#64 + (X + 0x7#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e3f8 (a X : BitVec 64) : a + X + 0x3e3f8#64 = a + 0x3e3f0#64 + (X + 0x8#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e3f9 (a X : BitVec 64) : a + X + 0x3e3f9#64 = a + 0x3e3f0#64 + (X + 0x9#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53eb5 (a X : BitVec 64) : a + X + 0x53eb5#64 = a + 0x53eb0#64 + (X + 0x5#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53eb6 (a X : BitVec 64) : a + X + 0x53eb6#64 = a + 0x53eb0#64 + (X + 0x6#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53eb7 (a X : BitVec 64) : a + X + 0x53eb7#64 = a + 0x53eb0#64 + (X + 0x7#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53eb8 (a X : BitVec 64) : a + X + 0x53eb8#64 = a + 0x53eb0#64 + (X + 0x8#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53eb9 (a X : BitVec 64) : a + X + 0x53eb9#64 = a + 0x53eb0#64 + (X + 0x9#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e414 (a X : BitVec 64) : a + X + 0x3e414#64 = a + 0x3e400#64 + (X + 0x14#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e418 (a X : BitVec 64) : a + X + 0x3e418#64 = a + 0x3e400#64 + (X + 0x18#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e41c (a X : BitVec 64) : a + X + 0x3e41c#64 = a + 0x3e400#64 + (X + 0x1c#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e420 (a X : BitVec 64) : a + X + 0x3e420#64 = a + 0x3e400#64 + (X + 0x20#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_3e424 (a X : BitVec 64) : a + X + 0x3e424#64 = a + 0x3e400#64 + (X + 0x24#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53ed4 (a X : BitVec 64) : a + X + 0x53ed4#64 = a + 0x53ec0#64 + (X + 0x14#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53ed8 (a X : BitVec 64) : a + X + 0x53ed8#64 = a + 0x53ec0#64 + (X + 0x18#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53edc (a X : BitVec 64) : a + X + 0x53edc#64 = a + 0x53ec0#64 + (X + 0x1c#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53ee0 (a X : BitVec 64) : a + X + 0x53ee0#64 = a + 0x53ec0#64 + (X + 0x20#64) :=
  adr_rb _ _ _ _ _ (by decide)
omit [CodeEnv] in
theorem dq_a_53ee4 (a X : BitVec 64) : a + X + 0x53ee4#64 = a + 0x53ec0#64 + (X + 0x24#64) :=
  adr_rb _ _ _ _ _ (by decide)

/-! ### flags -/
omit [CodeEnv] in
theorem dq_cf32 (b c : BitVec 32) :
    ((b - c).unsigned != b.unsigned - c.unsigned) = decide (b.toNat < c.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  have hb := b.isLt; have hc := c.isLt
  by_cases h : b.toNat < c.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem dq_cf64 (b c : BitVec 64) :
    ((b - c).unsigned != b.unsigned - c.unsigned) = decide (b.toNat < c.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  have hb := b.isLt; have hc := c.isLt
  by_cases h : b.toNat < c.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem dq_zf {w : Nat} (v : BitVec w) : (v == BitVec.zero w) = decide (v.toNat = 0) := by
  by_cases h : v.toNat = 0
  · have : v = BitVec.zero w := BitVec.eq_of_toNat_eq (by simp [h])
    simp [this]
  · have : v ≠ BitVec.zero w := fun e => h (by simp [e])
    simpa [h] using this

omit [CodeEnv] in
theorem dq_ofNat_toNat (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; omega

theorem dq_subz {w : Nat} (a b : BitVec w) : (a - b).toNat = 0 ↔ a.toNat = b.toNat := by
  constructor
  · intro h
    have h0 : a - b = 0#w := BitVec.eq_of_toNat_eq (by simpa using h)
    have h1 := congrArg (· + b) h0
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h1
    rw [h1]
  · intro h
    have : a = b := BitVec.eq_of_toNat_eq h
    subst this; simp

theorem dq_one64 : (1 : BitVec 64).toNat = 1 := rfl

/-- variant comparison without `decide` on state terms (shared `var_step` times out here). -/
syntax "dq_var" : tactic
macro_rules
  | `(tactic| dq_var) => `(tactic| (
      simp only [lex_var]
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

syntax "dq_edge" : tactic
macro_rules
  | `(tactic| dq_edge) => `(tactic| first
      | (left; dq_var)
      | (right; constructor
         · dq_var
         · simp only [lex_var]; decide))

theorem dq_b64 (b : BitVec 8) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := b.isLt; omega

theorem dq_b32 (b : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := b.isLt; omega

theorem dq_7 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 7#64)) = 7#32 := by decide

theorem dq_sw32 (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem dq_sw3264 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 v) = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt; omega

theorem dq_sw32128 (v : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 128 v) = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt; omega

theorem dq_shl1 (c : Nat) (h : c ≤ 22) : ((1#32) <<< c).toNat ≤ 1124073472 := by
  rw [BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mul, Nat.reduceMod, Nat.reducePow]
  have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) h
  have h2 := Nat.mod_le (2 ^ c) 4294967296
  simp only [Nat.reducePow] at h1
  omega

theorem dq_ofb4 (n : Nat) (h : n < 2 ^ 31) :
    (Int.ofBytes (Int.toBytes 4 (n : Int)) % ((2 ^ 32 : Nat) : Int)).toNat = n := by
  rw [ofBytes_toBytes]
  simp only [Int.take]
  omega

theorem dq_lo_app (a b : BitVec 64) : BitVec.setWidth 64 (a ++ b) = b := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append]
  simp [hi, BitVec.getLsbD_eq_getElem]

/-- literal-only reassociation (does not touch symbolic store addresses, unlike `add_assoc`). -/
theorem dq_aal (r : BitVec 64) (a b : Nat) :
    r + BitVec.ofNat 64 a + BitVec.ofNat 64 b = r + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem dq_le1 (v : BitVec 64) (h : v.toNat ≤ 1) : v = 0#64 ∨ v = 1#64 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq (by simp [h0])
  · right; exact BitVec.eq_of_toNat_eq (by simp [h1])

theorem dq_u8 (bs : List UInt8) (i : Nat) (h : i < bs.length) :
    Int.ofBytes ((bs.drop i).take 1) = ((u8 bs i : Nat) : Int) := by
  have h1 : (bs.drop i).take 1 = [bs[i]] := by rw [List.drop_eq_getElem_cons h]; rfl
  rw [h1]; simp [Int.ofBytes, u8, List.getElem?_eq_getElem h]

theorem dq_cf8 (b c : BitVec 8) :
    ((b - c).unsigned != b.unsigned - c.unsigned) = decide (b.toNat < c.toNat) := by
  simp only [BitVec.unsigned_eq, BitVec.toNat_sub]
  have hb := b.isLt; have hc := c.isLt
  by_cases h : b.toNat < c.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]; omega

theorem dq_a_289ac (a X : BitVec 64) : a + X + 166316#64 = a + 166316#64 + X := by ac_rfl

open Lean Elab Tactic Meta in
/-- revert all hypotheses `loadInt m a n = some v` (so `sep_mem` can rewrite region loads). -/
elab "dq_revert_loads" : tactic => withMainContext do
  let mut fvs := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, lhs, rhs) := ty.eq? then
      if lhs.isAppOfArity ``Mem.loadInt 4 && rhs.isAppOfArity ``Option.some 2 then
        fvs := fvs.push d.fvarId
  if fvs.isEmpty then throwError "dq_revert_loads: none"
  let (_, g) ← (← getMainGoal).revert fvs
  replaceMainGoal [g]

theorem dq_a_15ac0_d (a X Y : BitVec 64) :
    a + 342000#64 + X + Y + BitVec.ofNat 64 18446744073709462848 = a + 253232#64 + X + Y := by
  have h : (342000#64 : BitVec 64) + BitVec.ofNat 64 18446744073709462848 = 253232#64 := by decide
  calc a + 342000#64 + X + Y + BitVec.ofNat 64 18446744073709462848
      = a + X + Y + (342000#64 + BitVec.ofNat 64 18446744073709462848) := by ac_rfl
    _ = a + 253232#64 + X + Y := by rw [h]; ac_rfl

theorem dq_a_15ac0_q (a X Y : BitVec 64) :
    a + 341568#64 + X + Y + BitVec.ofNat 64 18446744073709462848 = a + 252800#64 + X + Y := by
  have h : (341568#64 : BitVec 64) + BitVec.ofNat 64 18446744073709462848 = 252800#64 := by decide
  calc a + 341568#64 + X + Y + BitVec.ofNat 64 18446744073709462848
      = a + X + Y + (341568#64 + BitVec.ofNat 64 18446744073709462848) := by ac_rfl
    _ = a + 252800#64 + X + Y := by rw [h]; ac_rfl

theorem dq_fr30 (a : BitVec 64) : a - 8#64 + 18446744073709551568#64 = a - 56#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  congr 1

theorem dq_fr38 (a : BitVec 64) : a - 8#64 + 18446744073709551560#64 = a - 64#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  congr 1

theorem dq_add0 (a : BitVec 64) : a + 0 = a := BitVec.add_zero a

theorem dq_n0 (a : BitVec 64) :
    a + BitVec.ofNat 64 (BitVec.setWidth 8 0#64).toNat * 4#64 + 477952#64 = a + 477952#64 := by
  have h : BitVec.ofNat 64 (BitVec.setWidth 8 0#64).toNat * 4#64 = 0#64 := by decide
  rw [h, BitVec.add_zero]

theorem dq_n1 (a : BitVec 64) :
    a + BitVec.ofNat 64 (BitVec.setWidth 8 1#64).toNat * 4#64 + 477952#64 = a + 477956#64 := by
  have h : BitVec.ofNat 64 (BitVec.setWidth 8 1#64).toNat * 4#64 = 4#64 := by decide
  rw [h, BitVec.add_assoc]
  all_goals (try congr 1)

open Lean Elab Tactic Meta in
/-- Fail unless the main goal is literally an `Or` (guards edge_step against `E.X` goals). -/
elab "dq_guard_or" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.consumeMData.isAppOfArity ``Or 2 do throwError "dq_guard_or: not an Or"

theorem dq_n1r (a : BitVec 64) : a + 4#64 + 477952#64 = a + 477956#64 := by rw [BitVec.add_assoc]; rfl

import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: blocks of shard `DqCpl` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L68b0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L68b0" ⟨"ff_aac_sbr_apply.L68b0", B.L68b0, some "ff_aac_sbr_apply.L68d0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L68b0.mp hs).2.2.2.2
  have h9 := (T.L68b0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L68b0]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, he1, he2, hrbx, hr12, hr13⟩, -⟩ := T.L68b0.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13]
  all_goals try simp only [dq_a_289ac]
  all_goals try (dq_revert_loads; simp only [dq_a_289ac]; sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L68f8") ?_; refine ⟨isSome_at L.L68f8, ?_, ?_⟩; rw [T.L68f8])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L68d0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L68d0" ⟨"ff_aac_sbr_apply.L68d0", B.L68d0, some "ff_aac_sbr_apply.L68d0_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L68d0.mp hs).2.2.2.2
  have h9 := (T.L68d0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L68d0]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L68d0.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q]
  all_goals try (dq_revert_loads; (try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L68d0_1])
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L68d0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L68d0_1" ⟨"ff_aac_sbr_apply.L68d0_1", B.L68d0_1, some "ff_aac_sbr_apply.L68f8"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L68d0_1.mp hs).2.2.2.2
  have h9 := (T.L68d0_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L68d0_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L68d0_1.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q] at *
  all_goals try (dq_revert_loads; (try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L68f8])
  all_goals try var_step
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L68f8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L68f8" ⟨"ff_aac_sbr_apply.L68f8", B.L68f8, some "ff_aac_sbr_apply.L6940"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L68f8.mp hs).2.2.2.2
  have h9 := (T.L68f8.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L68f8]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L68f8.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceOfNat, BitVec.add_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, BitVec.reduceMul, dq_n1r] at *
  all_goals try ((first | dq_revert_loads | skip); (try simp only [Option.some.injEq, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceOfNat, BitVec.add_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, BitVec.reduceMul, dq_n1r]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done) | (simp only [Option.isSome_some]; done) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals (repeat (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | intro _))
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L6a90"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6a90") ?_; refine ⟨isSome_at L.L6a90, ?_, ?_⟩; rw [T.L6a90])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L6940"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6940") ?_; refine ⟨isSome_at L.L6940, ?_, ?_⟩; rw [T.L6940])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L69d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L69d0") ?_; refine ⟨isSome_at L.L69d0, ?_, ?_⟩; rw [T.L69d0])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L69dd"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L69dd") ?_; refine ⟨isSome_at L.L69dd, ?_, ?_⟩; rw [T.L69dd])
  all_goals try dq_var
  all_goals try (dq_guard_or; left; dq_var)
  all_goals try (dq_guard_or; edge_step)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega
  all_goals try simp only [BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, BitVec.reduceMul, BitVec.add_zero, dq_n1r]
  all_goals try ((sep_mem hm); all_goals (first | (simp only [Option.isSome_some]; done) | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)))
  all_goals try (simp only [BitVec.reduceSetWidth, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, BitVec.reduceMul, BitVec.add_zero, dq_n1r] at *; dq_revert_loads; sep_mem hm; all_goals (repeat (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | intro)); all_goals (first | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done) | (have h0' : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega); have h1' : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega); simp only [h0', h1', e14] at *; first | omega | (exfalso; omega))))
  all_goals try (right; refine ⟨?_, ?_⟩ <;> simp only [lex_var] <;> (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]) <;> (first | done | rfl | decide))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6940 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6940" ⟨"ff_aac_sbr_apply.L6940", B.L6940, some "ff_aac_sbr_apply.L6940_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6940.mp hs).2.2.2.2
  have h9 := (T.L6940.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6940]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L6940.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try ((first | dq_revert_loads | skip); (try simp only [Option.some.injEq, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done) | (simp only [Option.isSome_some]; done) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals (repeat (intro _))
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6940_1])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try (dq_guard_or; edge_step)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6940_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6940_1" ⟨"ff_aac_sbr_apply.L6940_1", B.L6940_1, some "ff_aac_sbr_apply.L69a4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6940_1.mp hs).2.2.2.2
  have h9 := (T.L6940_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6940_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L6940_1.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try ((first | dq_revert_loads | skip); (try simp only [Option.some.injEq, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done) | (simp only [Option.isSome_some]; done) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals (repeat (intro _))
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L69a4"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L69a4") ?_; refine ⟨isSome_at L.L69a4, ?_, ?_⟩; rw [T.L69a4])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L69a4])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try (dq_guard_or; edge_step)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L69a4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L69a4" ⟨"ff_aac_sbr_apply.L69a4", B.L69a4, some "ff_aac_sbr_apply.L69d0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L69a4.mp hs).2.2.2.2
  have h9 := (T.L69a4.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L69a4]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L69a4.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [dq_a_289ac]
  all_goals try (dq_revert_loads; simp only [dq_a_289ac]; sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L6a30"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6a30") ?_; refine ⟨isSome_at L.L6a30, ?_, ?_⟩; rw [T.L6a30])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L69d0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L69d0" ⟨"ff_aac_sbr_apply.L69d0", B.L69d0, some "ff_aac_sbr_apply.L69dd"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L69d0.mp hs).2.2.2.2
  have h9 := (T.L69d0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L69d0]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L69d0.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try (dq_revert_loads; (try simp only [hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L69dd])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L69dd (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L69dd" ⟨"ff_aac_sbr_apply.L69dd", B.L69dd, some "ff_aac_sbr_apply.L6a10"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L69dd.mp hs).2.2.2.2
  have h9 := (T.L69dd.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L69dd]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L69dd.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [dq_a_289ac]
  all_goals try (dq_revert_loads; simp only [dq_a_289ac]; sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L6a10"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6a10") ?_; refine ⟨isSome_at L.L6a10, ?_, ?_⟩; rw [T.L6a10])
  all_goals try (goal_has_str "ff_aac_sbr_apply.L6a30"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6a30") ?_; refine ⟨isSome_at L.L6a30, ?_, ?_⟩; rw [T.L6a30])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6a10 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a10" ⟨"ff_aac_sbr_apply.L6a10", B.L6a10, some "ff_aac_sbr_apply.L6a30"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6a10.mp hs).2.2.2.2
  have h9 := (T.L6a10.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6a10]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L6a10.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [dq_a_289ac]
  all_goals try (dq_revert_loads; simp only [dq_a_289ac]; sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6a30") ?_; refine ⟨isSome_at L.L6a30, ?_, ?_⟩; rw [T.L6a30])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6a30])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6a30 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a30" ⟨"ff_aac_sbr_apply.L6a30", B.L6a30, some "ff_aac_sbr_apply.L6a30_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6a30.mp hs).2.2.2.2
  have h9 := (T.L6a30.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6a30]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L6a30.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try (dq_revert_loads; (try simp only [hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L68d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L68d0") ?_; refine ⟨isSome_at L.L68d0, ?_, ?_⟩; rw [T.L68d0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6a30_1])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6a30_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a30_1" ⟨"ff_aac_sbr_apply.L6a30_1", B.L6a30_1, some "ff_aac_sbr_apply.L6a30_2"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hkk, hr14⟩, hm⟩ := T.L6a30_1.mp hs
  clear hs
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L6a30_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc1 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx, h12, h13, h14, -⟩, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by simp only [lex_var]; (try subst_vars); (try simp only [hbx, h14]); var_step⟩
      rw [T.L6a30_2]
      refine ⟨hC, ⟨hrsp', hrbp'⟩, ⟨ee, kk, he1, he2, ?_, ?_, ?_, hkk, ?_⟩, ?_⟩
      · rw [hbx]; exact hrbx
      · rw [h12]; exact hr12
      · rw [h13]; exact hr13
      · rw [h14]; exact hr14
      simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6a30_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a30_2" ⟨"ff_aac_sbr_apply.L6a30_2", B.L6a30_2, some "ff_aac_sbr_apply.L6a90"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6a30_2.mp hs).2.2.2
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm
  have h9 : True := trivial
  dsimp only
  simp only [B.L6a30_2]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hkk, hr14⟩, -⟩ := T.L6a30_2.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try ((first | dq_revert_loads | skip); (try simp only [Option.some.injEq, hrsp, hrbp, hrbx, hr12, hr13, hr14, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done) | (simp only [Option.isSome_some]; done) | (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals (repeat (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | intro))
  all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at *
  all_goals try (simp only [Option.isSome_some]; done)
  case vc2 =>
    sep_mem hm
    all_goals simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]
  case vc5 =>
    sep_mem hm
    · simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega
    · simp only [hfl, Nat.reducePow]; omega
  dq_revert_loads
  sep_mem hm
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals (repeat (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | intro))
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee] at *
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals (repeat (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | intro _))
  all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h9, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at *
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (rw [Mem.sub_base_add_add]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L68d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L68d0") ?_; refine ⟨isSome_at L.L68d0, ?_, ?_⟩; rw [T.L68d0])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try (dq_guard_or; edge_step)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6a90 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a90" ⟨"ff_aac_sbr_apply.L6a90", B.L6a90, some "ff_aac_sbr_apply.L6abf"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6a90.mp hs).2.2.2.2
  have h9 := (T.L6a90.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6a90]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, he1, he2, hrbx, hr12, hr13⟩, -⟩ := T.L6a90.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13]
  all_goals try simp only [dq_a_289ac]
  all_goals try (dq_revert_loads; simp only [dq_a_289ac]; sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp -implicitDefEqProofs only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13]
  all_goals try simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp -implicitDefEqProofs only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp -implicitDefEqProofs only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6abf") ?_; refine ⟨isSome_at L.L6abf, ?_, ?_⟩; rw [T.L6abf])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L68b0") ?_; refine ⟨isSome_at L.L68b0, ?_, ?_⟩; rw [T.L68b0])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee + 1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, h9, arg1]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, and_true, true_and, hrsp, hrbp, BitVec.setWidth_zero]; done)
  all_goals try (refine ⟨?_, ?_⟩ <;> simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp] <;> rfl)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6abf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6abf" ⟨"ff_aac_sbr_apply.L6abf", B.L6abf, some "ff_aac_sbr_apply.L6b00"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L6abf.mp hs
  clear hs
  obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  dsimp only
  simp only [B.L6abf]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, z] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try (refine dq_isSome_add0 ?_; sep_mem hm)
  all_goals try (simp; done)
  all_goals try simp only [dq_c4_val, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, dq_xlo_zext, CondCode.interp_z, CondCode.interp_nz,
    StatusFlags.zf_from_result, BitVec.and_self] at *
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74de") ?_; refine ⟨isSome_at L.L74de, ?_, ?_⟩; rw [T.L74de])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b12") ?_; refine ⟨isSome_at L.L6b12, ?_, ?_⟩; rw [T.L6b12])
  all_goals try edge_step
  -- L6b12
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩; rotate_left 8)
  -- L74de
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩; rotate_left 3)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; sep_close hm)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, h9, arg1]; done)
  all_goals try (apply dq_ne0 _ (by omega); assumption)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_inc32 _ hnn,
    BitVec.xor_self, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0),
    dq_xlo_zext]; done)
  all_goals (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]; decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6b00 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6b00" ⟨"ff_aac_sbr_apply.L6b00", B.L6b00, some "ff_aac_sbr_apply.L6b02"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6b00.mp hs).2.2.2.2
  have h9 := (T.L6b00.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6b00]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6b00.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6b02])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6b02 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6b02" ⟨"ff_aac_sbr_apply.L6b02", B.L6b02, some "ff_aac_sbr_apply.L6b12"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6b02.mp hs).2.2.2.2
  have h9 := (T.L6b02.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6b02]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6b02.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74de") ?_; refine ⟨isSome_at L.L74de, ?_, ?_⟩; rw [T.L74de])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6b12])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj + 1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6b12 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6b12" ⟨"ff_aac_sbr_apply.L6b12", B.L6b12, some "ff_aac_sbr_apply.L6b50"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6b12.mp hs).2.2.2.2
  have h9 := (T.L6b12.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6b12]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6b12.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b00") ?_; refine ⟨isSome_at L.L6b00, ?_, ?_⟩; rw [T.L6b00])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b50") ?_; refine ⟨isSome_at L.L6b50, ?_, ?_⟩; rw [T.L6b50])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b6c") ?_; refine ⟨isSome_at L.L6b6c, ?_, ?_⟩; rw [T.L6b6c])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, (BitVec.ofInt 8 ‹Int›).toNat, hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6b50 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6b50" ⟨"ff_aac_sbr_apply.L6b50", B.L6b50, some "ff_aac_sbr_apply.L6b6c"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6b50.mp hs).2.2.2.2
  have h9 := (T.L6b50.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6b50]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, dd, hjj, hrdx, hrsi, hrax, hx0, hd1, hd2, hrd, hrcx⟩, -⟩ := T.L6b50.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals have edd := congrArg BitVec.toNat hrd
  all_goals simp only [dq_ofNat_toNat _ (show dd < 2 ^ 64 by omega)] at edd
  all_goals have ecx := congrArg BitVec.toNat hrcx
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at ecx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b6c") ?_; refine ⟨isSome_at L.L6b6c, ?_, ?_⟩; rw [T.L6b6c])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6b6c])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6b6c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6b6c" ⟨"ff_aac_sbr_apply.L6b6c", B.L6b6c, some "ff_aac_sbr_apply.L6ba0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6b6c.mp hs).2.2.2.2
  have h9 := (T.L6b6c.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6b6c]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6b6c.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ba0") ?_; refine ⟨isSome_at L.L6ba0, ?_, ?_⟩; rw [T.L6ba0])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6bbc") ?_; refine ⟨isSome_at L.L6bbc, ?_, ?_⟩; rw [T.L6bbc])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ba0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ba0" ⟨"ff_aac_sbr_apply.L6ba0", B.L6ba0, some "ff_aac_sbr_apply.L6bbc"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ba0.mp hs).2.2.2.2
  have h9 := (T.L6ba0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ba0]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6ba0.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6bbc") ?_; refine ⟨isSome_at L.L6bbc, ?_, ?_⟩; rw [T.L6bbc])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6bbc])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6bbc (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6bbc" ⟨"ff_aac_sbr_apply.L6bbc", B.L6bbc, some "ff_aac_sbr_apply.L6bbc_1"⟩ := by
  info_off
  have hfm := Kraken.F32.dequantFloatModel_holds
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6bbc.mp hs).2.2.2.2
  have h9 := (T.L6bbc.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6bbc]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6bbc.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (have hF := hfm _ hx2; clear hm; simp_all only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0),
    RegZmms.get_set_xmm_same, dq_lo_app, StatusFlags.ofFCmp, Bool.false_or, Bool.or_false, Bool.false_eq_true]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6bbc_1])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6bbc_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6bbc_1" ⟨"ff_aac_sbr_apply.L6bbc_1", B.L6bbc_1, some "ff_aac_sbr_apply.L6c1e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6bbc_1.mp hs).2.2.2.2
  have h9 := (T.L6bbc_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6bbc_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6bbc_1.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c1e") ?_; refine ⟨isSome_at L.L6c1e, ?_, ?_⟩; rw [T.L6c1e])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c3a") ?_; refine ⟨isSome_at L.L6c3a, ?_, ?_⟩; rw [T.L6c3a])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, (BitVec.ofInt 8 ‹Int›).toNat, hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c1e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c1e" ⟨"ff_aac_sbr_apply.L6c1e", B.L6c1e, some "ff_aac_sbr_apply.L6c3a"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c1e.mp hs).2.2.2.2
  have h9 := (T.L6c1e.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c1e]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, dd, hjj, hrdx, hrsi, hrax, hx0, hd1, hd2, hrd, hrcx⟩, -⟩ := T.L6c1e.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals have edd := congrArg BitVec.toNat hrd
  all_goals simp only [dq_ofNat_toNat _ (show dd < 2 ^ 64 by omega)] at edd
  all_goals have ecx := congrArg BitVec.toNat hrcx
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at ecx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c3a") ?_; refine ⟨isSome_at L.L6c3a, ?_, ?_⟩; rw [T.L6c3a])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6c3a])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c3a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c3a" ⟨"ff_aac_sbr_apply.L6c3a", B.L6c3a, some "ff_aac_sbr_apply.L6c61"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c3a.mp hs).2.2.2.2
  have h9 := (T.L6c3a.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c3a]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6c3a.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c61") ?_; refine ⟨isSome_at L.L6c61, ?_, ?_⟩; rw [T.L6c61])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c7d") ?_; refine ⟨isSome_at L.L6c7d, ?_, ?_⟩; rw [T.L6c7d])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c61 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c61" ⟨"ff_aac_sbr_apply.L6c61", B.L6c61, some "ff_aac_sbr_apply.L6c7d"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c61.mp hs).2.2.2.2
  have h9 := (T.L6c61.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c61]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6c61.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6c7d") ?_; refine ⟨isSome_at L.L6c7d, ?_, ?_⟩; rw [T.L6c7d])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6c7d])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c7d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c7d" ⟨"ff_aac_sbr_apply.L6c7d", B.L6c7d, some "ff_aac_sbr_apply.L6c7d_1"⟩ := by
  info_off
  have hfm := Kraken.F32.dequantFloatModel_holds
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c7d.mp hs).2.2.2.2
  have h9 := (T.L6c7d.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c7d]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6c7d.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (have hF := hfm _ hx2; clear hm; simp_all only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0),
    RegZmms.get_set_xmm_same, dq_lo_app, StatusFlags.ofFCmp, Bool.false_or, Bool.or_false, Bool.false_eq_true]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6c7d_1])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c7d_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c7d_1" ⟨"ff_aac_sbr_apply.L6c7d_1", B.L6c7d_1, some "ff_aac_sbr_apply.L6c7d_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c7d_1.mp hs).2.2.2.2
  have h9 := (T.L6c7d_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c7d_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6c7d_1.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6c7d_2])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6c7d_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6c7d_2" ⟨"ff_aac_sbr_apply.L6c7d_2", B.L6c7d_2, some "ff_aac_sbr_apply.L6ce0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6c7d_2.mp hs).2.2.2.2
  have h9 := (T.L6c7d_2.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6c7d_2]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6c7d_2.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ce0") ?_; refine ⟨isSome_at L.L6ce0, ?_, ?_⟩; rw [T.L6ce0])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6cea") ?_; refine ⟨isSome_at L.L6cea, ?_, ?_⟩; rw [T.L6cea])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6d09") ?_; refine ⟨isSome_at L.L6d09, ?_, ?_⟩; rw [T.L6d09])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, (BitVec.ofInt 8 ‹Int›).toNat, hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ce0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ce0" ⟨"ff_aac_sbr_apply.L6ce0", B.L6ce0, some "ff_aac_sbr_apply.L6cea"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ce0.mp hs).2.2.2.2
  have h9 := (T.L6ce0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ce0]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6ce0.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6cea (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6cea" ⟨"ff_aac_sbr_apply.L6cea", B.L6cea, some "ff_aac_sbr_apply.L6d09"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6cea.mp hs).2.2.2.2
  have h9 := (T.L6cea.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6cea]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, dd, hjj, hrdx, hrsi, hrax, hx0, hd1, hd2, hrd, hrcx⟩, -⟩ := T.L6cea.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals have edd := congrArg BitVec.toNat hrd
  all_goals simp only [dq_ofNat_toNat _ (show dd < 2 ^ 64 by omega)] at edd
  all_goals have ecx := congrArg BitVec.toNat hrcx
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at ecx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6d09") ?_; refine ⟨isSome_at L.L6d09, ?_, ?_⟩; rw [T.L6d09])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6d09])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6d09 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6d09" ⟨"ff_aac_sbr_apply.L6d09", B.L6d09, some "ff_aac_sbr_apply.L6d32"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6d09.mp hs).2.2.2.2
  have h9 := (T.L6d09.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6d09]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6d09.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6d32") ?_; refine ⟨isSome_at L.L6d32, ?_, ?_⟩; rw [T.L6d32])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6d51") ?_; refine ⟨isSome_at L.L6d51, ?_, ?_⟩; rw [T.L6d51])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6d32 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6d32" ⟨"ff_aac_sbr_apply.L6d32", B.L6d32, some "ff_aac_sbr_apply.L6d51"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6d32.mp hs).2.2.2.2
  have h9 := (T.L6d32.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6d32]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6d32.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6d51") ?_; refine ⟨isSome_at L.L6d51, ?_, ?_⟩; rw [T.L6d51])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6d51])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6d51 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6d51" ⟨"ff_aac_sbr_apply.L6d51", B.L6d51, some "ff_aac_sbr_apply.L6d51_1"⟩ := by
  info_off
  have hfm := Kraken.F32.dequantFloatModel_holds
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6d51.mp hs).2.2.2.2
  have h9 := (T.L6d51.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6d51]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6d51.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (have hF := hfm _ hx2; clear hm; simp_all only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0),
    RegZmms.get_set_xmm_same, dq_lo_app, StatusFlags.ofFCmp, Bool.false_or, Bool.or_false, Bool.false_eq_true]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6d51_1])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6d51_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6d51_1" ⟨"ff_aac_sbr_apply.L6d51_1", B.L6d51_1, some "ff_aac_sbr_apply.L6dbc"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6d51_1.mp hs).2.2.2.2
  have h9 := (T.L6d51_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6d51_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6d51_1.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6dbc") ?_; refine ⟨isSome_at L.L6dbc, ?_, ?_⟩; rw [T.L6dbc])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ddb") ?_; refine ⟨isSome_at L.L6ddb, ?_, ?_⟩; rw [T.L6ddb])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, (BitVec.ofInt 8 ‹Int›).toNat, hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6dbc (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6dbc" ⟨"ff_aac_sbr_apply.L6dbc", B.L6dbc, some "ff_aac_sbr_apply.L6ddb"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6dbc.mp hs).2.2.2.2
  have h9 := (T.L6dbc.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6dbc]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, dd, hjj, hrdx, hrsi, hrax, hx0, hd1, hd2, hrd, hrcx⟩, -⟩ := T.L6dbc.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals have edd := congrArg BitVec.toNat hrd
  all_goals simp only [dq_ofNat_toNat _ (show dd < 2 ^ 64 by omega)] at edd
  all_goals have ecx := congrArg BitVec.toNat hrcx
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at ecx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ddb") ?_; refine ⟨isSome_at L.L6ddb, ?_, ?_⟩; rw [T.L6ddb])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6ddb])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ddb (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ddb" ⟨"ff_aac_sbr_apply.L6ddb", B.L6ddb, some "ff_aac_sbr_apply.L6e04"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ddb.mp hs).2.2.2.2
  have h9 := (T.L6ddb.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ddb]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6ddb.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6e04") ?_; refine ⟨isSome_at L.L6e04, ?_, ?_⟩; rw [T.L6e04])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6e23") ?_; refine ⟨isSome_at L.L6e23, ?_, ?_⟩; rw [T.L6e23])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6e04 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6e04" ⟨"ff_aac_sbr_apply.L6e04", B.L6e04, some "ff_aac_sbr_apply.L6e23"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6e04.mp hs).2.2.2.2
  have h9 := (T.L6e04.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6e04]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6e04.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6e23") ?_; refine ⟨isSome_at L.L6e23, ?_, ?_⟩; rw [T.L6e23])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6e23])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6e23 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6e23" ⟨"ff_aac_sbr_apply.L6e23", B.L6e23, some "ff_aac_sbr_apply.L6e23_1"⟩ := by
  info_off
  have hfm := Kraken.F32.dequantFloatModel_holds
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6e23.mp hs).2.2.2.2
  have h9 := (T.L6e23.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6e23]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6e23.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (have hF := hfm _ hx2; clear hm; simp_all only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0),
    RegZmms.get_set_xmm_same, dq_lo_app, StatusFlags.ofFCmp, Bool.false_or, Bool.or_false, Bool.false_eq_true]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6e23_1])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6e23_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6e23_1" ⟨"ff_aac_sbr_apply.L6e23_1", B.L6e23_1, some "ff_aac_sbr_apply.L6e8c"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6e23_1.mp hs).2.2.2.2
  have h9 := (T.L6e23_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6e23_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6e23_1.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6e8c") ?_; refine ⟨isSome_at L.L6e8c, ?_, ?_⟩; rw [T.L6e8c])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ea8") ?_; refine ⟨isSome_at L.L6ea8, ?_, ?_⟩; rw [T.L6ea8])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, (BitVec.ofInt 8 ‹Int›).toNat, hjj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6e8c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6e8c" ⟨"ff_aac_sbr_apply.L6e8c", B.L6e8c, some "ff_aac_sbr_apply.L6ea8"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6e8c.mp hs).2.2.2.2
  have h9 := (T.L6e8c.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6e8c]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, dd, hjj, hrdx, hrsi, hrax, hx0, hd1, hd2, hrd, hrcx⟩, -⟩ := T.L6e8c.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals have edd := congrArg BitVec.toNat hrd
  all_goals simp only [dq_ofNat_toNat _ (show dd < 2 ^ 64 by omega)] at edd
  all_goals have ecx := congrArg BitVec.toNat hrcx
  all_goals simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at ecx
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ea8") ?_; refine ⟨isSome_at L.L6ea8, ?_, ?_⟩; rw [T.L6ea8])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6ea8])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax, hrd, hrcx]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ea8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ea8" ⟨"ff_aac_sbr_apply.L6ea8", B.L6ea8, some "ff_aac_sbr_apply.L6ecf"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ea8.mp hs).2.2.2.2
  have h9 := (T.L6ea8.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ea8]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6ea8.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ecf") ?_; refine ⟨isSome_at L.L6ecf, ?_, ?_⟩; rw [T.L6ecf])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6eeb") ?_; refine ⟨isSome_at L.L6eeb, ?_, ?_⟩; rw [T.L6eeb])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6ecf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ecf" ⟨"ff_aac_sbr_apply.L6ecf", B.L6ecf, some "ff_aac_sbr_apply.L6eeb"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ecf.mp hs).2.2.2.2
  have h9 := (T.L6ecf.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ecf]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6ecf.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6eeb") ?_; refine ⟨isSome_at L.L6eeb, ?_, ?_⟩; rw [T.L6eeb])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6eeb])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6eeb (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6eeb" ⟨"ff_aac_sbr_apply.L6eeb", B.L6eeb, some "ff_aac_sbr_apply.L6eeb_1"⟩ := by
  info_off
  have hfm := Kraken.F32.dequantFloatModel_holds
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6eeb.mp hs).2.2.2.2
  have h9 := (T.L6eeb.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6eeb]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0, hx2⟩, -⟩ := T.L6eeb.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (have hF := hfm _ hx2; clear hm; simp_all only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0),
    RegZmms.get_set_xmm_same, dq_lo_app, StatusFlags.ofFCmp, Bool.false_or, Bool.or_false, Bool.false_eq_true]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6eeb_1])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx2]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6eeb_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6eeb_1" ⟨"ff_aac_sbr_apply.L6eeb_1", B.L6eeb_1, some "ff_aac_sbr_apply.L6eeb_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6eeb_1.mp hs).2.2.2.2
  have h9 := (T.L6eeb_1.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6eeb_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6eeb_1.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6eeb_2])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6eeb_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6eeb_2" ⟨"ff_aac_sbr_apply.L6eeb_2", B.L6eeb_2, some "ff_aac_sbr_apply.L6f32"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6eeb_2.mp hs).2.2.2.2
  have h9 := (T.L6eeb_2.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6eeb_2]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6eeb_2.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)

end Kraken.Examples.Sbr.Apply

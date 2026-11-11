/-
The register and system-state read-over-write API the spec framework discharges
against: `Sys D` and its projections, register reads over `set64` (both the
indexed `get64` and the per-field accessors), the `MachineData` record
projections, and the `StatusFlags`/`BitVec` reductions the flag and address
arithmetic normalize with.
-/
import Kraken.X64.OmniSemantics
import Kraken.GrindFold
import Std.Tactic.Do

open Std.WP
open Std.WP.WPMonad

set_option mvcgen.warning false
set_option grind.warning false

/-! ## System state

The denotational monad runs over `Sys D`: the CPU `MachineData` plus a device
state `D`. Instruction primitives update `machine` and thread `device`; a `jump`
carries the whole `Sys D` in the exception, so `device` survives control transfer.
The projection-over-`mk` lemmas let the state-simplification and `easm` fold a
`Sys` update the way they already fold a `MachineData` update. -/

structure Sys (D : Type) where
  machine : MachineData
  device : D

@[simp] theorem Sys.machine_mk {D : Type} (m : MachineData) (d : D) :
    (Sys.mk m d).machine = m := rfl
@[simp] theorem Sys.device_mk {D : Type} (m : MachineData) (d : D) :
    (Sys.mk m d).device = d := rfl

/-! ## Address spelling -/

/-- The baseline address semantics at 64-bit address size, with the label table
explicit. The explicit argument keeps every subterm rewritable (`simp`'s
congruence holds an instance-implicit argument fixed, so a state equation never
reaches a label table passed as an instance), and the literal `BitVec 64`
result is the width spelling the proof engines read. -/
def AddrExpr.interp64 (labels : Labels) (a : AddrExpr) (s : Reg64s) (p : Std.Rco Int64) : BitVec 64 :=
  @AddrExpr.interp labels (.mk .W64) a s p

/-! ## `.unsigned`/`.signed` reductions -/
@[grind hom] theorem BitVec.unsigned_hom {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.unsigned_eq {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.signed_eq {w} (x : BitVec w) : x.signed = x.toInt := rfl

@[simp, grind =] theorem StatusFlags.cf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).cf = f.cf := rfl

@[simp] theorem StatusFlags.from_result.Remaining.cf_mk (c a o : Bool) :
    (StatusFlags.from_result.Remaining.mk c a o).cf = c := rfl

@[simp, grind =] theorem StatusFlags.zf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == BitVec.zero w) := rfl

@[simp, grind =] theorem StatusFlags.sf_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).sf = v.msb := rfl

@[simp, grind =] theorem StatusFlags.of_from_result {w} (v : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).of = f.of := rfl

/-! ## Condition-code reductions, one lemma per code -/

@[simp, grind =] theorem CondCode.interp_z (s : StatusFlags) :
    CondCode.z.interp s = s.zf := rfl
@[simp, grind =] theorem CondCode.interp_nz (s : StatusFlags) :
    CondCode.nz.interp s = !s.zf := rfl
@[simp, grind =] theorem CondCode.interp_c (s : StatusFlags) :
    CondCode.c.interp s = s.cf := rfl
@[simp, grind =] theorem CondCode.interp_nc (s : StatusFlags) :
    CondCode.nc.interp s = !s.cf := rfl
@[simp, grind =] theorem CondCode.interp_a (s : StatusFlags) :
    CondCode.a.interp s = (!s.cf && !s.zf) := rfl
@[simp, grind =] theorem CondCode.interp_be (s : StatusFlags) :
    CondCode.be.interp s = (s.cf || s.zf) := rfl
@[simp, grind =] theorem CondCode.interp_l (s : StatusFlags) :
    CondCode.l.interp s = (s.sf != s.of) := rfl
@[simp, grind =] theorem CondCode.interp_le (s : StatusFlags) :
    CondCode.le.interp s = ((s.sf != s.of) || s.zf) := rfl
@[simp, grind =] theorem CondCode.interp_ge (s : StatusFlags) :
    CondCode.ge.interp s = (s.sf == s.of) := rfl
@[simp, grind =] theorem CondCode.interp_g (s : StatusFlags) :
    CondCode.g.interp s = (!s.zf && (s.sf == s.of)) := rfl
@[simp, grind =] theorem CondCode.interp_s (s : StatusFlags) :
    CondCode.s.interp s = s.sf := rfl
@[simp, grind =] theorem CondCode.interp_ns (s : StatusFlags) :
    CondCode.ns.interp s = !s.sf := rfl

/-! ## Signed comparisons

`cmp` leaves the flags of `a - b`, and `jl`/`jge` read them as the signed order
of `a` and `b`. The two rules below give that reading directly, as the unsigned
order of the operands with their sign bits flipped. That spelling is linear
arithmetic with a constant modulus, so `grind` does not case split on the signs
of `a`, `b` and `a - b`, as it does when the flags unfold to `BitVec.toInt`. The
hypothesis on `f` says that the overflow flag is the one a subtraction
computes; `grind` discharges it by reducing the projection. -/

theorem BitVec.toInt_lt_toInt_iff_flip (a b : BitVec 64) :
    a.toInt < b.toInt ↔ (a.toNat + 2 ^ 63) % 2 ^ 64 < (b.toNat + 2 ^ 63) % 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

theorem BitVec.toInt_le_toInt_iff_flip (a b : BitVec 64) :
    a.toInt ≤ b.toInt ↔ (a.toNat + 2 ^ 63) % 2 ^ 64 ≤ (b.toNat + 2 ^ 63) % 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

@[grind =] theorem CondCode.interp_l_sub (a b : BitVec 64)
    (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) :
    CondCode.l.interp (StatusFlags.from_result (a - b) f)
      = decide ((a.toNat + 2 ^ 63) % 2 ^ 64 < (b.toNat + 2 ^ 63) % 2 ^ 64) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf]
  have : ((a - b).msb != ((a - b).signed != a.signed - b.signed))
      = decide (a.toInt < b.toInt) := by
    grind [BitVec.signed_eq]
  simp only [this, BitVec.toInt_lt_toInt_iff_flip]

@[grind =] theorem CondCode.interp_ge_sub (a b : BitVec 64)
    (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) :
    CondCode.ge.interp (StatusFlags.from_result (a - b) f)
      = decide ((b.toNat + 2 ^ 63) % 2 ^ 64 ≤ (a.toNat + 2 ^ 63) % 2 ^ 64) := by
  rw [CondCode.interp_ge, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf]
  have : ((a - b).msb == ((a - b).signed != a.signed - b.signed))
      = decide (b.toInt ≤ a.toInt) := by
    grind [BitVec.signed_eq]
  simp only [this, BitVec.toInt_le_toInt_iff_flip]

/-! ## Unsigned comparisons

`ja`/`jbe` after `cmp` read the flags of `a - b` as the unsigned order of `a`
and `b`: the carry flag is the borrow, the zero flag equality. The hypothesis
on `f` says the carry flag is the one a subtraction computes; `grind`
discharges it by reducing the projection, as for the signed rules above. -/

/-- The borrow of an unsigned subtraction, as two linear cases. -/
theorem BitVec.toNat_sub_cases {w} (a b : BitVec w) :
    (b.toNat ≤ a.toNat → (a - b).toNat = a.toNat - b.toNat)
    ∧ (a.toNat < b.toNat → (a - b).toNat = 2 ^ w - b.toNat + a.toNat) := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_sub]
  generalize 2 ^ w = d at *
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show d - b.toNat + a.toNat = (a.toNat - b.toNat) + d by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

@[grind =] theorem CondCode.interp_a_sub {w} (a b : BitVec w)
    (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.a.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result, hf]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt
  have hb := b.isLt
  have hz : (a - b == BitVec.zero w) = decide (a.toNat = b.toNat) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq]
    simp only [BitVec.zero_eq, BitVec.toNat_ofNat, Nat.zero_mod]
    generalize 2 ^ w = d at *
    by_cases h : b.toNat ≤ a.toNat
    · rw [h₁ h]; omega
    · rw [h₂ (by omega)]; omega
  rw [hz, BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  generalize 2 ^ w = d at *
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]
    by_cases he : a.toNat = b.toNat
    · simp [he]
    · have : b.toNat < a.toNat := by omega
      simp [he, this]
      omega
  · rw [h₂ (by omega)]
    have : ¬ b.toNat < a.toNat := by omega
    simp [this]
    omega

@[grind =] theorem CondCode.interp_be_sub {w} (a b : BitVec w)
    (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.be.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat ≤ b.toNat) := by
  have h := CondCode.interp_a_sub a b f hf
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be]
  revert h
  cases (StatusFlags.from_result (a - b) f).cf <;> cases (StatusFlags.from_result (a - b) f).zf <;>
    simp <;> omega

/-! ## Reading a named register, one lemma per field -/

@[simp, grind =] theorem Reg64s.get64_rax (s : Reg64s) : s.get64 .rax = s.rax.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rbx (s : Reg64s) : s.get64 .rbx = s.rbx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rcx (s : Reg64s) : s.get64 .rcx = s.rcx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rdx (s : Reg64s) : s.get64 .rdx = s.rdx.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rsi (s : Reg64s) : s.get64 .rsi = s.rsi.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rdi (s : Reg64s) : s.get64 .rdi = s.rdi.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rsp (s : Reg64s) : s.get64 .rsp = s.rsp.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_rbp (s : Reg64s) : s.get64 .rbp = s.rbp.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r8 (s : Reg64s) : s.get64 .r8 = s.r8.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r9 (s : Reg64s) : s.get64 .r9 = s.r9.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r10 (s : Reg64s) : s.get64 .r10 = s.r10.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r11 (s : Reg64s) : s.get64 .r11 = s.r11.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r12 (s : Reg64s) : s.get64 .r12 = s.r12.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r13 (s : Reg64s) : s.get64 .r13 = s.r13.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r14 (s : Reg64s) : s.get64 .r14 = s.r14.toBitVec := rfl
@[simp, grind =] theorem Reg64s.get64_r15 (s : Reg64s) : s.get64 .r15 = s.r15.toBitVec := rfl

/-! ## Register identity as a number

The state-simplification pass reduces ground terms of the builtin types, so a
read-over-write condition is stated between register indices: the index of a
named register is a numeral, and the pass decides the comparison and takes the
branch. -/

def Reg64.idx : Reg64 → Nat
  | .rax => 0  | .rbx => 1  | .rcx => 2  | .rdx => 3
  | .rsi => 4  | .rdi => 5  | .rsp => 6  | .rbp => 7
  | .r8  => 8  | .r9  => 9  | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

theorem Reg64.eq_eq_idx_eq (r r' : Reg64) : (r = r') = (r.idx = r'.idx) := by
  cases r <;> cases r' <;> simp [Reg64.idx]

/-! ## Register read-over-write API

Register reads are characterized by rewriting, so discharging queries only the
registers the postcondition mentions and a state literal's register file is
never unfolded. -/

attribute [grind =] Width.bytes

@[simp, grind =] theorem Width.bytesv_W64 {n : Nat} :
    (Width.W64).bytesv (n := n) = BitVec.ofNat n 8 := rfl

@[simp, grind =] theorem Reg64s.set64_set64 (s : Reg64s) (r : Reg64) (v w : BitVec 64) :
    (s.set64 r v).set64 r w = s.set64 r w := by
  cases r <;> simp [Reg64s.set64]

@[simp, grind =] theorem Reg64s.set64_get64 (s : Reg64s) (r : Reg64) :
    s.set64 r (s.get64 r) = s := by
  cases r <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp, grind =] theorem Reg64s.get_low64 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

/-- A 32-bit read is the low half of the 64-bit register. A `grind` rule only,
so the simp normal form of a 32-bit read is unchanged. -/
@[grind =] theorem Reg64s.get_low32 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W32) = (s.get64 r).setWidth 32 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

@[simp, grind =] theorem Reg64s.set_low64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    Reg64s.set s (.low r .W64) v = s.set64 r v := rfl

/-- An 8-bit read is the low byte of the 64-bit register. A `grind` rule only,
like `get_low32`. -/
@[grind =] theorem Reg64s.get_low8 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W8) = (s.get64 r).setWidth 8 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

/-- A 32-bit write zero-extends into the 64-bit register. -/
@[simp, grind =] theorem Reg64s.set_low32 (s : Reg64s) (r : Reg64) (v : BitVec 32) :
    Reg64s.set s (.low r .W32) v = s.set64 r (v.setWidth 64) := rfl

/-- An 8-bit write replaces the low byte and keeps the rest. -/
@[simp, grind =] theorem Reg64s.set_low8 (s : Reg64s) (r : Reg64) (v : BitVec 8) :
    Reg64s.set s (.low r .W8) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

/-- The low byte after an 8-bit write is the byte written. -/
@[grind =] theorem BitVec.toNat_replaceLow8_mod (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).toNat % 256 = new.toNat := by
  have h : (old.replaceLow new).setWidth 8 = new := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_setWidth] using this

/-- The high bytes after an 8-bit write are the old ones. -/
@[grind =] theorem BitVec.toNat_replaceLow8_div (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).toNat / 256 = old.toNat / 256 := by
  have h : (old.replaceLow new) >>> 8 = old >>> 8 := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this

/-- An 8-bit read after an 8-bit write is the byte written. -/
@[simp, grind =] theorem BitVec.setWidth_replaceLow8 (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).setWidth 8 = new := by
  simp only [BitVec.replaceLow, BitVec.drop]
  bv_decide

/-! A value stored as `n` bytes and loaded back is the value, at the width of
the register it goes into. Instances of `BitVec.ofInt_ofBytes_toBytes_eq` at
the widths the instruction rules produce, so `grind` sees through
store-then-load without being told the width. -/

@[grind =] theorem BitVec.ofInt8_ofBytes_toBytes1 (v : Int) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 v)) = BitVec.ofInt 8 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl v
@[grind =] theorem BitVec.ofInt32_ofBytes_toBytes4 (v : Int) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v)) = BitVec.ofInt 32 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl v
@[grind =] theorem BitVec.ofInt64_ofBytes_toBytes8 (v : Int) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 v)) = BitVec.ofInt 64 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl v

attribute [grind =] BitVec.ofInt_toInt BitVec.toNat_setWidth

/-! `and al, 1` and the byte it leaves: a compiler's way of making a `bool`
well-formed. The low bit of a byte, as a natural number and as the integer
a store of the byte writes; and an integer that came from a natural number,
read back as a byte. -/

@[grind =] theorem BitVec.toNat_and_one (x : BitVec 8) : (x &&& 1#8).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and]; exact Nat.and_one_is_mod _

@[grind =] theorem BitVec.toInt_setWidth8_and_one (x : BitVec 64) :
    ((x.setWidth 8 &&& 1#8).toInt) = ((x.toNat % 2 : Nat) : Int) := by
  have h := BitVec.toNat_and_one (x.setWidth 8)
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide)] at h
  rw [BitVec.toInt_eq_toNat_of_msb, h]
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- As an integer equation on any `v`: `grind` normalises casts inward
(`↑((n + 1) % 2)` becomes `(↑n + 1) % 2`), so a statement keyed on
`BitVec.ofInt 8 ↑k` would not be found. -/
@[grind =] theorem BitVec.natCast_toNat_ofInt8 (v : Int) :
    ((BitVec.ofInt 8 v).toNat : Int) = v % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rfl

@[simp, grind =] theorem MachineData.regs_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).regs = s.regs.set r v := rfl
@[simp, grind =] theorem MachineData.status_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).status = s.status := rfl
@[simp, grind =] theorem MachineData.dmem_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).dmem = s.dmem := rfl
@[simp, grind =] theorem MachineData.zmms_setReg (s : MachineData) {w} (r : Reg w) (v : w.type) :
    (s.setReg r v).zmms = s.zmms := rfl

@[simp] theorem MachineData.regs_mk (r z st d) : (MachineData.mk r z st d).regs = r := rfl
@[simp] theorem MachineData.dmem_mk (r z st d) : (MachineData.mk r z st d).dmem = d := rfl
@[simp] theorem MachineData.status_mk (r z st d) : (MachineData.mk r z st d).status = st := rfl
@[simp] theorem MachineData.zmms_mk (r z st d) : (MachineData.mk r z st d).zmms = z := rfl

/-! ## Machine words in `grind`'s arithmetic

A register holds a `UInt64` whose payload is a `BitVec 64`, and the instruction
semantics moves between the two spellings and back through `Nat`. Each equation
below is one crossing that `grind` cannot take on its own: the payload bridge,
the range fact every word carries, and the three reductions a wrapping
subtraction and a double-width product need once the result is known to fit. -/

@[grind =] theorem UInt64.toNat_payload (x : UInt64) : x.toBitVec.toNat = x.toNat := rfl

@[grind .] theorem UInt64.lt_size (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

@[grind =] theorem BitVec.toNat_sub_le {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

@[grind =] theorem BitVec.toNat_ofInt_mul {a b : BitVec 64}
    (h : a.toNat * b.toNat < 2 ^ 64) :
    (BitVec.ofInt 64 ((a.toNat : Int) * (b.toNat : Int))).toNat = a.toNat * b.toNat := by
  rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  simp [Nat.mod_eq_of_lt h]

@[grind =] theorem BitVec.ofInt_mul_shiftRight {a b : BitVec 64}
    (h : a.toNat * b.toNat < 2 ^ 64) :
    BitVec.ofInt 64 (((a.toNat : Int) * (b.toNat : Int)) >>> 64) = 0#64 := by
  rw [← Int.natCast_mul, ← Int.natCast_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt h]
  simp

@[grind =] theorem Int64.ofNat_lit (n : Nat) : (OfNat.ofNat n : Int64) = Int64.ofNat n := rfl
@[grind =] theorem Int64.toBitVec_lit (n : Nat) :
    (OfNat.ofNat n : Int64).toBitVec = BitVec.ofNat 64 n := rfl
@[grind =] theorem BitVec.setWidth_64_64 (x : BitVec 64) :
    BitVec.setWidth 64 x = x := BitVec.setWidth_eq x
@[simp, grind =] theorem BitVec.ofInt_toInt_int64 (c : Int64) :
    BitVec.ofInt 64 c.toInt = c.toBitVec := by
  rw [show c.toInt = c.toBitVec.toInt from rfl, BitVec.ofInt_toInt]

/-- An immediate reaches `grind` as the payload of an `Int64` literal. This
rule rewrites the payload to a `BitVec` literal, so that shift counts,
displacements and masks are numerals to the arithmetic (`no_index` lets it
match the numeral). `MachineWP` registers it with `grind`'s normalizer. -/
theorem Int64.toBitVec_ofNat_norm (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toBitVec = BitVec.ofNat 64 n := rfl

/-- A negative immediate, likewise: the parser writes it as the negation of a
literal. -/
theorem Int64.toBitVec_neg_ofNat_norm (n : Nat) :
    (-(no_index (OfNat.ofNat n : Int64))).toBitVec
      = BitVec.ofNat 64 (2 ^ 64 - n % 2 ^ 64) := by
  rw [Int64.toBitVec_neg, Int64.toBitVec_ofNat_norm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]

/-! ## Masks

Code rounds down to a multiple of a power of two with `and $-2^k, %r`, and takes
the remainder with `and $2^k-1, %r`. The rules below read such an `and` as
arithmetic, both on the register value and on its `toNat`, the form `grind`
reaches through `BitVec.toNat_and`. Each fires only on a literal mask of its
shape. A number `n ≤ 2 ^ w` is a power of two exactly when `2 ^ w % n = 0`, so
the guards are literal arithmetic, which `grind` decides by evaluation. -/

theorem Nat.and_two_pow_sub_two_pow {x w k : Nat} (hk : k ≤ w) (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : 2 ^ w - 2 ^ k = 2 ^ k * (2 ^ (w - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  rw [h1, Nat.mul_comm (x / 2 ^ k), Nat.testBit_and, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hik : k ≤ i
  · simp only [ge_iff_le, hik, decide_true, Bool.true_and, Nat.sub_add_cancel hik]
    by_cases hiw : i < w
    · simp [show i - k < w - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hik]

theorem Nat.exists_eq_two_pow_of_dvd : ∀ {w n : Nat}, n ∣ 2 ^ w → ∃ k, n = 2 ^ k
  | 0, _, h => ⟨0, Nat.dvd_one.mp h⟩
  | w + 1, n, h => by
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h2
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w)] at h
      obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd
        (Nat.dvd_of_mul_dvd_mul_left (show 0 < 2 by decide) h)
      exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
    · have hc : Nat.Coprime n 2 := by
        show Nat.gcd n 2 = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, h2]
        rfl
      rw [Nat.pow_succ] at h
      exact Nat.exists_eq_two_pow_of_dvd (hc.dvd_of_dvd_mul_right h)

theorem BitVec.toNat_ofNat_lit_of_lt {w m : Nat} (hm : m < 2 ^ w) :
    (OfNat.ofNat m : BitVec w).toNat = m := by
  show (BitVec.ofNat w m).toNat = m
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

/-- An `and` of a register value with a mask of low bits is a remainder. -/
theorem BitVec.toNat_and_lowMask_toNat {w : Nat} (x : BitVec w) (m : Nat)
    (h : 2 ^ w % (m + 1) = 0) :
    x.toNat &&& m = x.toNat % (m + 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd (Nat.dvd_of_mod_eq_zero h)
  rw [hk, show m = 2 ^ k - 1 by omega, Nat.and_two_pow_sub_one_eq_mod]

/-- An `and` of a register value with a mask of high bits rounds down to a
multiple of `2 ^ w - m`. -/
theorem BitVec.toNat_and_highMask_toNat {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (2 ^ w - m) = 0) :
    x.toNat &&& m = x.toNat / (2 ^ w - m) * (2 ^ w - m) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_two_pow_of_dvd (Nat.dvd_of_mod_eq_zero h)
  have hkw : k ≤ w := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp (by omega)
  rw [hk, show m = 2 ^ w - 2 ^ k by omega]
  exact Nat.and_two_pow_sub_two_pow hkw x.isLt

/-- An `and` with a mask of low bits is a remainder. -/
theorem BitVec.toNat_and_lowMask {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (m + 1) = 0) :
    (x &&& (OfNat.ofNat m : BitVec w)).toNat = x.toNat % (m + 1) := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat_lit_of_lt hm]
  exact BitVec.toNat_and_lowMask_toNat x m h

/-- An `and` with a mask of high bits rounds down to a multiple of `2 ^ w - m`. -/
theorem BitVec.toNat_and_highMask {w : Nat} (x : BitVec w) (m : Nat) (hm : m < 2 ^ w)
    (h : 2 ^ w % (2 ^ w - m) = 0) :
    (x &&& (OfNat.ofNat m : BitVec w)).toNat = x.toNat / (2 ^ w - m) * (2 ^ w - m) := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat_lit_of_lt hm]
  exact BitVec.toNat_and_highMask_toNat x m hm h

grind_pattern BitVec.toNat_and_lowMask => x &&& (OfNat.ofNat m : BitVec w) where
  guard m < 2 ^ w
  guard 2 ^ w % (m + 1) = 0

grind_pattern BitVec.toNat_and_highMask => x &&& (OfNat.ofNat m : BitVec w) where
  guard m < 2 ^ w
  guard 2 ^ w % (2 ^ w - m) = 0

grind_pattern BitVec.toNat_and_lowMask_toNat => x.toNat &&& (OfNat.ofNat m : Nat) where
  guard 2 ^ w % (m + 1) = 0

grind_pattern BitVec.toNat_and_highMask_toNat => x.toNat &&& (OfNat.ofNat m : Nat) where
  guard m < 2 ^ w
  guard 2 ^ w % (2 ^ w - m) = 0

/-! ## Alignment

An alignment check is a remainder of the address, which `grind` reads as
arithmetic. -/

attribute [grind =] isAligned

/-! ## Per-register field reads over `set64`, one lemma per field -/

@[simp, grind =] theorem Reg64s.rax_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rax = if r = .rax then .ofBitVec v else s.rax := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbx = if r = .rbx then .ofBitVec v else s.rbx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rcx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rcx = if r = .rcx then .ofBitVec v else s.rcx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdx_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rdx = if r = .rdx then .ofBitVec v else s.rdx := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsi = if r = .rsi then .ofBitVec v else s.rsi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rdi_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rdi = if r = .rdi then .ofBitVec v else s.rdi := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rsp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rsp = if r = .rsp then .ofBitVec v else s.rsp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.rbp_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).rbp = if r = .rbp then .ofBitVec v else s.rbp := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r8_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r8 = if r = .r8 then .ofBitVec v else s.r8 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r9_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r9 = if r = .r9 then .ofBitVec v else s.r9 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r10_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r10 = if r = .r10 then .ofBitVec v else s.r10 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r11_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r11 = if r = .r11 then .ofBitVec v else s.r11 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r12_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r12 = if r = .r12 then .ofBitVec v else s.r12 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r13_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r13 = if r = .r13 then .ofBitVec v else s.r13 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r14_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r14 = if r = .r14 then .ofBitVec v else s.r14 := by cases r <;> simp [Reg64s.set64]
@[simp, grind =] theorem Reg64s.r15_set64 (s : Reg64s) (r : Reg64) (v : BitVec 64) :
    (s.set64 r v).r15 = if r = .r15 then .ofBitVec v else s.r15 := by cases r <;> simp [Reg64s.set64]

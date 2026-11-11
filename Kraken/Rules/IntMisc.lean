import Kraken.Rules.GenericMem

/-!
# Integer rules at every operand width

`MachineWP.lean` states its integer rules per shape, mostly at 64 bits, with a
few 32- and 8-bit forms. Compiled C uses every width and, with memory operands,
every addressing shape. This file gives the integer instructions their rules at
the widths 8, 16, 32 and 64 (named `…_w8_spec` … `…_w64_spec`):

* register forms `op %rs, %rd` and `op $i, %r`;
* memory forms over the operand `⟨some (.reg rb), idx, .int64 d⟩`, any index
  or none, as in `GenericMem.lean`: loads `op d(…), %r`, read-modify-writes
  `op %r, d(…)` and `op $i, d(…)`, and stores. A memory operand of `n` bytes
  reads `Mem.loadInt s.dmem addr n`; the precondition asks for those bytes to be
  readable, which, as everywhere in `MachineWP`, also makes them writable.

The operations are `add`, `sub`, `sbb`, `cmp`, `and`, `or`, `xor`, `test`,
`neg`, `not`, `dec`, `mov`, `movzx`/`movsx`, `cmovcc`, `setcc`, `imul` (two- and
three-operand register forms), `lea` (base and any index, or index without
base), and `shl`/`shr`/`sar` by an immediate or by `%cl`.

Each rule is one instance of a pattern per operand form; the instances differ
only in the width. They are stated per width, not once over `w : Width`, so
that a sub-register is read and written on the 64-bit register file, as the
32- and 8-bit rules of `MachineWP.lean` do: a 32-bit read is
`(s.regs.get64 r).setWidth 32`, a 32-bit write `s.regs.set64 r (v.setWidth 64)`,
an 8- or 16-bit write `s.regs.set64 r ((s.regs.get64 r).replaceLow v)`. A rule
over `w` would leave `s.regs.set (.low r .W32) v` in the verification
condition, which neither the state simplification nor `grind` reduces well.

All rules are `@[spec low]`, so the shape-specific rules of `MachineWP.lean`
and `GenericMem.lean` win where they fit.

Flags that the semantics leaves undefined are universally quantified in the
precondition (`∀ af : Bool`). A shift leaves its flags arbitrary (`∀ st`), and a
shift by a masked count of zero changes nothing, as the semantics says.
-/

open Kraken MachineWP Std.WP Lean.Order

/-- A 16-bit read is the low half-word of the 64-bit register. A `grind` rule
only, like `Reg64s.get_low32`. -/
theorem Reg64s.get_low16 (s : Reg64s) (r : Reg64) :
    s.get (.low r .W16) = (s.get64 r).setWidth 16 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

/-- A 16-bit write replaces the low half-word and keeps the rest. -/
@[simp] theorem Reg64s.set_low16 (s : Reg64s) (r : Reg64) (v : BitVec 16) :
    Reg64s.set s (.low r .W16) v = s.set64 r ((s.get64 r).replaceLow v) := rfl

/-- The low half-word after a 16-bit write is the half-word written. -/
theorem BitVec.toNat_replaceLow16_mod (old : BitVec 64) (new : BitVec 16) :
    (old.replaceLow new).toNat % 65536 = new.toNat := by
  have h : (old.replaceLow new).setWidth 16 = new := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_setWidth] using this

/-- The high bytes after a 16-bit write are the old ones. -/
theorem BitVec.toNat_replaceLow16_div (old : BitVec 64) (new : BitVec 16) :
    (old.replaceLow new).toNat / 65536 = old.toNat / 65536 := by
  have h : (old.replaceLow new) >>> 16 = old >>> 16 := by
    simp only [BitVec.replaceLow, BitVec.drop]
    bv_decide
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using this

/-- The whole register after a 16-bit write, as a number: the old high bytes
and the new half-word. With it `grind` decides equalities about the full
64-bit register after a 16-bit write (e.g. `(5#64).replaceLow 4#16 = 4#64`),
which the `_mod`/`_div` forms alone do not give it. -/
theorem BitVec.toNat_replaceLow16 (old : BitVec 64) (new : BitVec 16) :
    (old.replaceLow new).toNat = old.toNat / 65536 * 65536 + new.toNat := by
  have h1 := BitVec.toNat_replaceLow16_mod old new
  have h2 := BitVec.toNat_replaceLow16_div old new
  omega

/-- The whole register after an 8-bit write, as a number (see
`BitVec.toNat_replaceLow16`). -/
theorem BitVec.toNat_replaceLow8 (old : BitVec 64) (new : BitVec 8) :
    (old.replaceLow new).toNat = old.toNat / 256 * 256 + new.toNat := by
  have h1 := BitVec.toNat_replaceLow8_mod old new
  have h2 := BitVec.toNat_replaceLow8_div old new
  omega

/- The low byte (half-word) after an 8-bit (16-bit) write is resolved while
`grind` normalises, as `Reg64s.get64_set64` is (see `GenericMem.lean`): a
shift count set by `mov $3,%cl` is `(rcx.replaceLow 3#8).toNat % 256 % 32`,
which then becomes the literal 3. (The scoped `grind norm` attribute is set
below, in `Kraken.Rules.IntMisc.SubReg`, after the `grind =` ones.) -/

/-- A 16-bit read after a 16-bit write is the half-word written. -/
@[simp] theorem BitVec.setWidth_replaceLow16 (old : BitVec 64) (new : BitVec 16) :
    (old.replaceLow new).setWidth 16 = new := by
  simp only [BitVec.replaceLow, BitVec.drop]
  bv_decide

/-! The `grind` attributes of the sub-register lemmas above are scoped (`open
scoped Kraken.Rules.IntMisc.SubReg`), so that importing this file does not change
`grind` behaviour elsewhere. -/
namespace Kraken.Rules.IntMisc.SubReg
attribute [scoped grind =] Reg64s.get_low16 Reg64s.set_low16 BitVec.toNat_replaceLow16_mod
  BitVec.toNat_replaceLow16_div BitVec.toNat_replaceLow16 BitVec.toNat_replaceLow8
  BitVec.setWidth_replaceLow16
attribute [scoped grind norm] BitVec.toNat_replaceLow8_mod BitVec.toNat_replaceLow16_mod
end Kraken.Rules.IntMisc.SubReg

open scoped Kraken.Rules.IntMisc.SubReg

/-- The masked count of a shift by `%cl`, at an operand width below 64 bits. -/
theorem ShiftCountExpr.interpMasked_cl_lt64 [Labels] (s : MachineData) (rng : Std.Rco Int64)
    (w : Width) (hw : w ≠ .W64) :
    ShiftCountExpr.cl.interpMasked s rng w = (s.regs.get64 .rcx).toNat % 256 % 32 := by
  cases w <;> first
    | exact absurd rfl hw
    | simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
        BitVec.extractLsb'_toNat, Nat.and_two_pow_sub_one_eq_mod (n := 5)] <;> try rfl

/-- The masked count of a shift by `%cl`, at 64 bits. -/
theorem ShiftCountExpr.interpMasked_cl_64 [Labels] (s : MachineData) (rng : Std.Rco Int64) :
    ShiftCountExpr.cl.interpMasked s rng .W64 = (s.regs.get64 .rcx).toNat % 256 % 64 := by
  simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
    BitVec.extractLsb'_toNat, Nat.and_two_pow_sub_one_eq_mod (n := 6)]

/-- The masked count of a shift by an immediate, at an operand width below 64
bits. -/
theorem ShiftCountExpr.interpMasked_imm8_lt64 [Labels] (i : Int64) (s : MachineData)
    (rng : Std.Rco Int64) (w : Width) (hw : w ≠ .W64) :
    (ShiftCountExpr.imm8 (.int64 i)).interpMasked s rng w = i.toBitVec.toNat % 256 % 32 := by
  cases w <;> first
    | exact absurd rfl hw
    | simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp, BitVec.take,
        BitVec.extractLsb'_toNat, Nat.and_two_pow_sub_one_eq_mod (n := 5)] <;> try rfl

/-- The masked count of a shift by an immediate, at 64 bits. -/
theorem ShiftCountExpr.interpMasked_imm8_64 [Labels] (i : Int64) (s : MachineData)
    (rng : Std.Rco Int64) :
    (ShiftCountExpr.imm8 (.int64 i)).interpMasked s rng .W64 = i.toBitVec.toNat % 256 % 64 := by
  simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp, BitVec.take,
    BitVec.extractLsb'_toNat, Nat.and_two_pow_sub_one_eq_mod (n := 6)]

/-- The 64-bit address of a `disp(base,index,scale)` operand, before any
extension: what `lea` reads. -/
theorem AddrExpr.interp_base_idx_disp64 [Labels] (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) (regs : Reg64s) (rng : Std.Rco Int64) :
    (AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), idx, .int64 d⟩) regs rng : BitVec 64)
      = regs.get64 b + AddrIndex.offset64 idx regs + d.toBitVec := by
  rw [← AddrExpr.zeroExtend_interp_base_idx_disp b idx d regs rng]
  exact (BitVec.setWidth_eq _).symm

/-- The 64-bit address of a `disp(,index,scale)` operand (no base register) at
64-bit address size. -/
theorem AddrExpr.interp_index_disp64 [Labels] (i : Reg64) (c : Width) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    (AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨none, some ⟨i, c⟩, .int64 d⟩) regs rng : BitVec 64)
      = AddrIndex.offset64 (some ⟨i, c⟩) regs + d.toBitVec := by
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, AddrIndex.offset64]
  rw [htake, hsigned]
  show BitVec.ofInt 64 _ = _
  simp [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- Sub-register reads and writes, on the 64-bit register file. -/
local macro "sub_regs" : tactic =>
  `(tactic| simp only [Reg64s.get_low32, Reg64s.set_low32, Reg64s.get_low16, Reg64s.set_low16,
      Reg64s.get_low8, Reg64s.set_low8])

/-- The proof of a register rule. -/
local macro "reg_rule" : term =>
  `(fallthrough_spec (fun s rng P hP => by wp_step; (try sub_regs); exact hP))

/-- The proof of a register rule that leaves `af` undefined. -/
local macro "reg_nondet_rule" : term =>
  `(fallthrough_nondet_spec (fun s rng P hP => by wp_step; (try sub_regs); exact hP))

/-- The proof of a rule with one memory operand: the bytes are readable, so the
load (and the store, if any) takes the `some` branch. -/
local macro "mem_rule" : term => `(Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.load, MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      Width.bytes, hv, Effects.All]
    (try sub_regs)
    first
      | exact hk v hv _ hpl'
      | exact fun af => hk v hv af _ hpl'
      | exact hk _ hpl')

/-- The proof of a register rule that leaves four flags undefined (`imul`). -/
local macro "nondet4_rule" : term => `(Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    (try sub_regs)
    try simp only [Effects.All]
    intro sf zf af pf
    exact h sf zf af pf _ hpl')

/-- The proof of a `lea` rule. -/
local macro "lea_rule" : term =>
  `(fallthrough_spec (fun s rng P hP => by
      wp_step
      simp only [AddrExpr.interp_base_idx_disp64, AddrExpr.interp_index_disp64]
      (try sub_regs)
      exact hP))

/-- The proof of a shift rule: a zero count changes nothing; otherwise the
undefined `af`, `cf`, `of` are chosen in up to three steps;
`zf`, `sf`, `pf` come from the result. -/
local macro "shift_rule" : term => `(Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [ShiftCountExpr.interpMasked_cl_64, ShiftCountExpr.interpMasked_imm8_64,
      ShiftCountExpr.interpMasked_cl_lt64, ShiftCountExpr.interpMasked_imm8_lt64, ne_eq,
      reduceCtorEq, not_false_eq_true]
    (try sub_regs)
    split
    · next h0 =>
      try simp only [beq_iff_eq] at h0
      simp only [h0, ite_true] at h
      exact h false false false _ hpl'
    · next h0 =>
      try simp only [beq_iff_eq] at h0
      simp only [h0, ite_false] at h
      simp only [Effects.All]
      intro af
      split
      · split
        · exact h _ _ _ _ hpl'
        · intro of; exact h _ _ _ _ hpl'
      · intro cf
        split
        · exact h _ _ _ _ hpl'
        · intro of; exact h _ _ _ _ hpl')

/-- `addb %r, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 8
        let b := (s.regs.get64 rd).setWidth 8
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.add (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addw %r, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 16
        let b := (s.regs.get64 rd).setWidth 16
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.add (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addl %r, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 32
        let b := (s.regs.get64 rd).setWidth 32
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.add (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addq %r, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addb $i, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 8
        let b := (s.regs.get64 r).setWidth 8
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.add (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addw $i, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 16
        let b := (s.regs.get64 r).setWidth 16
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.add (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addl $i, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 32
        let b := (s.regs.get64 r).setWidth 32
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.add (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addq $i, %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 64
        let b := s.regs.get64 r
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned + b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                    of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.add (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `addb d(%rb,%idx), %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let b := (s.regs.get64 r).setWidth 8
            let v := a + b
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.add (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addw d(%rb,%idx), %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let b := (s.regs.get64 r).setWidth 16
            let v := a + b
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.add (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addl d(%rb,%idx), %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let b := (s.regs.get64 r).setWidth 32
            let v := a + b
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.add (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addq d(%rb,%idx), %r`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let b := s.regs.get64 r
            let v := a + b
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addb %r, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := (s.regs.get64 r).setWidth 8
            let b := BitVec.ofInt 8 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addw %r, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := (s.regs.get64 r).setWidth 16
            let b := BitVec.ofInt 16 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addl %r, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := (s.regs.get64 r).setWidth 32
            let b := BitVec.ofInt 32 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addq %r, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := s.regs.get64 r
            let b := BitVec.ofInt 64 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addb $i, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := i.toBitVec.truncate 8
            let b := BitVec.ofInt 8 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addw $i, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := i.toBitVec.truncate 16
            let b := BitVec.ofInt 16 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addl $i, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := i.toBitVec.truncate 32
            let b := BitVec.ofInt 32 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `addq $i, d(%rb,%idx)`: the sum and its flags. -/
@[spec low] theorem MachineWP.add_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := i.toBitVec.truncate 64
            let b := BitVec.ofInt 64 m
            let v := a + b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned + b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                        of := v.signed != a.signed + b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subb %r, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 8
        let b := (s.regs.get64 rd).setWidth 8
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.sub (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subw %r, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 16
        let b := (s.regs.get64 rd).setWidth 16
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.sub (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subl %r, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 32
        let b := (s.regs.get64 rd).setWidth 32
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.sub (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subq %r, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subb $i, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 8
        let b := (s.regs.get64 r).setWidth 8
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.sub (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subw $i, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 16
        let b := (s.regs.get64 r).setWidth 16
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.sub (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subl $i, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 32
        let b := (s.regs.get64 r).setWidth 32
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.sub (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subq $i, %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 64
        let b := s.regs.get64 r
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned,
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                    of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.sub (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `subb d(%rb,%idx), %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let b := (s.regs.get64 r).setWidth 8
            let v := b - a
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sub (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subw d(%rb,%idx), %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let b := (s.regs.get64 r).setWidth 16
            let v := b - a
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sub (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subl d(%rb,%idx), %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let b := (s.regs.get64 r).setWidth 32
            let v := b - a
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sub (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subq d(%rb,%idx), %r`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let b := s.regs.get64 r
            let v := b - a
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sub (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subb %r, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := (s.regs.get64 r).setWidth 8
            let b := BitVec.ofInt 8 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subw %r, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := (s.regs.get64 r).setWidth 16
            let b := BitVec.ofInt 16 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subl %r, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := (s.regs.get64 r).setWidth 32
            let b := BitVec.ofInt 32 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subq %r, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := s.regs.get64 r
            let b := BitVec.ofInt 64 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subb $i, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := i.toBitVec.truncate 8
            let b := BitVec.ofInt 8 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subw $i, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := i.toBitVec.truncate 16
            let b := BitVec.ofInt 16 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subl $i, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := i.toBitVec.truncate 32
            let b := BitVec.ofInt 32 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `subq $i, d(%rb,%idx)`: the difference and its flags. -/
@[spec low] theorem MachineWP.sub_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := i.toBitVec.truncate 64
            let b := BitVec.ofInt 64 m
            let v := b - a
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned,
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                        of := v.signed != b.signed - a.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sub (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbb %r, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 8
        let b := (s.regs.get64 rd).setWidth 8
        let v := b - a - BitVec.ofNat 8 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W8
          (.sbb (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbw %r, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 16
        let b := (s.regs.get64 rd).setWidth 16
        let v := b - a - BitVec.ofNat 16 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W16
          (.sbb (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbl %r, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 32
        let b := (s.regs.get64 rd).setWidth 32
        let v := b - a - BitVec.ofNat 32 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W32
          (.sbb (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbq %r, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let v := b - a - BitVec.ofNat 64 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W64
          (.sbb (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbb $i, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 8
        let b := (s.regs.get64 r).setWidth 8
        let v := b - a - BitVec.ofNat 8 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W8
          (.sbb (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbw $i, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 16
        let b := (s.regs.get64 r).setWidth 16
        let v := b - a - BitVec.ofNat 16 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W16
          (.sbb (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbl $i, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 32
        let b := (s.regs.get64 r).setWidth 32
        let v := b - a - BitVec.ofNat 32 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W32
          (.sbb (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbq $i, %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := i.toBitVec.truncate 64
        let b := s.regs.get64 r
        let v := b - a - BitVec.ofNat 64 s.status.cf.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                    af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                    of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } } ⦄
      (Directive.instr (.regular asz .W64
          (.sbb (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `sbbb d(%rb,%idx), %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let b := (s.regs.get64 r).setWidth 8
            let v := b - a - BitVec.ofNat 8 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sbb (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbw d(%rb,%idx), %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let b := (s.regs.get64 r).setWidth 16
            let v := b - a - BitVec.ofNat 16 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sbb (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbl d(%rb,%idx), %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let b := (s.regs.get64 r).setWidth 32
            let v := b - a - BitVec.ofNat 32 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sbb (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbq d(%rb,%idx), %r`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let b := s.regs.get64 r
            let v := b - a - BitVec.ofNat 64 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sbb (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbb %r, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := (s.regs.get64 r).setWidth 8
            let b := BitVec.ofInt 8 m
            let v := b - a - BitVec.ofNat 8 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbw %r, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := (s.regs.get64 r).setWidth 16
            let b := BitVec.ofInt 16 m
            let v := b - a - BitVec.ofNat 16 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbl %r, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := (s.regs.get64 r).setWidth 32
            let b := BitVec.ofInt 32 m
            let v := b - a - BitVec.ofNat 32 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbq %r, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := s.regs.get64 r
            let b := BitVec.ofInt 64 m
            let v := b - a - BitVec.ofNat 64 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbb $i, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := i.toBitVec.truncate 8
            let b := BitVec.ofInt 8 m
            let v := b - a - BitVec.ofNat 8 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbw $i, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := i.toBitVec.truncate 16
            let b := BitVec.ofInt 16 m
            let v := b - a - BitVec.ofNat 16 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbl $i, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := i.toBitVec.truncate 32
            let b := BitVec.ofInt 32 m
            let v := b - a - BitVec.ofNat 32 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `sbbq $i, d(%rb,%idx)`: the difference less the carry, and its flags. -/
@[spec low] theorem MachineWP.sbb_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := i.toBitVec.truncate 64
            let b := BitVec.ofInt 64 m
            let v := b - a - BitVec.ofNat 64 s.status.cf.toNat
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),
                        af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned - (s.status.cf.toNat : Int),
                        of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.sbb (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpb %r, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 8
        let b := (s.regs.get64 rs).setWidth 8
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.cmp (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpw %r, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 16
        let b := (s.regs.get64 rs).setWidth 16
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.cmp (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpl %r, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 32
        let b := (s.regs.get64 rs).setWidth 32
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.cmp (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpq %r, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rd
        let b := s.regs.get64 rs
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpb $i, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let b := i.toBitVec.truncate 8
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W8
          (.cmp (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpw $i, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let b := i.toBitVec.truncate 16
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.cmp (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpl $i, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let b := i.toBitVec.truncate 32
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.cmp (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpq $i, %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let b := i.toBitVec.truncate 64
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := v.unsigned != a.unsigned - b.unsigned,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                    of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmpb d(%rb,%idx), %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := (s.regs.get64 r).setWidth 8
            let b := BitVec.ofInt 8 m
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpw d(%rb,%idx), %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := (s.regs.get64 r).setWidth 16
            let b := BitVec.ofInt 16 m
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.cmp (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpl d(%rb,%idx), %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := (s.regs.get64 r).setWidth 32
            let b := BitVec.ofInt 32 m
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.cmp (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpq d(%rb,%idx), %r`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_reg_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := s.regs.get64 r
            let b := BitVec.ofInt 64 m
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpb %r, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_reg_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let b := (s.regs.get64 r).setWidth 8
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpw %r, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_reg_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let b := (s.regs.get64 r).setWidth 16
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpl %r, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_reg_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let b := (s.regs.get64 r).setWidth 32
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpq %r, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_reg_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let b := s.regs.get64 r
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpb $i, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let b := i.toBitVec.truncate 8
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpw $i, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let b := i.toBitVec.truncate 16
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpl $i, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let b := i.toBitVec.truncate 32
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmpq $i, d(%rb,%idx)`: no write; the flags of the difference. -/
@[spec low] theorem MachineWP.cmp_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let b := i.toBitVec.truncate 64
            let v := a - b
            WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := v.unsigned != a.unsigned - b.unsigned,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                        of := v.signed != a.signed - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmp (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andb %r, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 8 &&& (s.regs.get64 rs).setWidth 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.and (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andw %r, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 16 &&& (s.regs.get64 rs).setWidth 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.and (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andl %r, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 &&& (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.and (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andq %r, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.and (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andb $i, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 8 &&& i.toBitVec.truncate 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.and (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andw $i, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 16 &&& i.toBitVec.truncate 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.and (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andl $i, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 &&& i.toBitVec.truncate 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.and (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andq $i, %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r &&& i.toBitVec.truncate 64
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.and (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `andb d(%rb,%idx), %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := (s.regs.get64 r).setWidth 8 &&& BitVec.ofInt 8 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.and (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andw d(%rb,%idx), %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := (s.regs.get64 r).setWidth 16 &&& BitVec.ofInt 16 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.and (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andl d(%rb,%idx), %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := (s.regs.get64 r).setWidth 32 &&& BitVec.ofInt 32 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.and (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andq d(%rb,%idx), %r`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := s.regs.get64 r &&& BitVec.ofInt 64 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.and (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andb %r, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m &&& (s.regs.get64 r).setWidth 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andw %r, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m &&& (s.regs.get64 r).setWidth 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andl %r, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m &&& (s.regs.get64 r).setWidth 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andq %r, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m &&& s.regs.get64 r
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andb $i, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m &&& i.toBitVec.truncate 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andw $i, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m &&& i.toBitVec.truncate 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andl $i, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m &&& i.toBitVec.truncate 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `andq $i, d(%rb,%idx)`: the conjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.and_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m &&& i.toBitVec.truncate 64
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.and (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orb %r, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 8 ||| (s.regs.get64 rs).setWidth 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.or (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orw %r, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 16 ||| (s.regs.get64 rs).setWidth 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.or (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orl %r, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 ||| (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.or (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orq %r, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ||| s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.or (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orb $i, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 8 ||| i.toBitVec.truncate 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.or (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orw $i, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 16 ||| i.toBitVec.truncate 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.or (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orl $i, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 ||| i.toBitVec.truncate 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.or (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orq $i, %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r ||| i.toBitVec.truncate 64
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.or (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `orb d(%rb,%idx), %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := (s.regs.get64 r).setWidth 8 ||| BitVec.ofInt 8 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.or (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orw d(%rb,%idx), %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := (s.regs.get64 r).setWidth 16 ||| BitVec.ofInt 16 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.or (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orl d(%rb,%idx), %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := (s.regs.get64 r).setWidth 32 ||| BitVec.ofInt 32 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.or (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orq d(%rb,%idx), %r`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := s.regs.get64 r ||| BitVec.ofInt 64 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.or (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orb %r, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m ||| (s.regs.get64 r).setWidth 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orw %r, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m ||| (s.regs.get64 r).setWidth 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orl %r, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m ||| (s.regs.get64 r).setWidth 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orq %r, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m ||| s.regs.get64 r
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orb $i, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m ||| i.toBitVec.truncate 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orw $i, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m ||| i.toBitVec.truncate 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orl $i, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m ||| i.toBitVec.truncate 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `orq $i, d(%rb,%idx)`: the disjunction; `af` left arbitrary. -/
@[spec low] theorem MachineWP.or_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m ||| i.toBitVec.truncate 64
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.or (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorb %r, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 8 ^^^ (s.regs.get64 rs).setWidth 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.xor (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorw %r, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 16 ^^^ (s.regs.get64 rs).setWidth 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.xor (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorl %r, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 ^^^ (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorq %r, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd ^^^ s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorb $i, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 8 ^^^ i.toBitVec.truncate 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.xor (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorw $i, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 16 ^^^ i.toBitVec.truncate 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.xor (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorl $i, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 ^^^ i.toBitVec.truncate 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.xor (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorq $i, %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r ^^^ i.toBitVec.truncate 64
        ∀ af : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `xorb d(%rb,%idx), %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := (s.regs.get64 r).setWidth 8 ^^^ BitVec.ofInt 8 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.xor (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorw d(%rb,%idx), %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := (s.regs.get64 r).setWidth 16 ^^^ BitVec.ofInt 16 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.xor (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorl d(%rb,%idx), %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_load_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := (s.regs.get64 r).setWidth 32 ^^^ BitVec.ofInt 32 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((v).setWidth 64),
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.xor (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorq d(%rb,%idx), %r`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_load_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := s.regs.get64 r ^^^ BitVec.ofInt 64 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  regs := s.regs.set64 r v,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorb %r, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_store_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m ^^^ (s.regs.get64 r).setWidth 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorw %r, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_store_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m ^^^ (s.regs.get64 r).setWidth 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorl %r, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_store_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m ^^^ (s.regs.get64 r).setWidth 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorq %r, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_store_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m ^^^ s.regs.get64 r
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorb $i, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m ^^^ i.toBitVec.truncate 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorw $i, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m ^^^ i.toBitVec.truncate 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorl $i, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m ^^^ i.toBitVec.truncate 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `xorq $i, d(%rb,%idx)`: the exclusive or; `af` left arbitrary. -/
@[spec low] theorem MachineWP.xor_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m ^^^ i.toBitVec.truncate 64
            ∀ af : Bool, WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.xor (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testb %r, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_reg_w8_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 8 &&& (s.regs.get64 rs).setWidth 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.test (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testw %r, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_reg_w16_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 16 &&& (s.regs.get64 rs).setWidth 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.test (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testl %r, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_reg_w32_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 &&& (s.regs.get64 rs).setWidth 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.test (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testq %r, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_reg_w64_spec (asz : Width) (rd : Reg64) (rs : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 rd &&& s.regs.get64 rs
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testb $i, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 8 &&& i.toBitVec.truncate 8
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8
          (.test (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testw $i, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 16 &&& i.toBitVec.truncate 16
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W16
          (.test (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testl $i, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 32 &&& i.toBitVec.truncate 32
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.test (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testq $i, %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r &&& i.toBitVec.truncate 64
        ∀ af : Bool, WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                  { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_nondet_rule

/-- `testb d(%rb,%idx), %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := (s.regs.get64 r).setWidth 8 &&& BitVec.ofInt 8 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.test (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testw d(%rb,%idx), %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := (s.regs.get64 r).setWidth 16 &&& BitVec.ofInt 16 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.test (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testl d(%rb,%idx), %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := (s.regs.get64 r).setWidth 32 &&& BitVec.ofInt 32 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.test (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testq d(%rb,%idx), %r`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_reg_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := s.regs.get64 r &&& BitVec.ofInt 64 m
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.test (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testb %r, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_reg_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m &&& (s.regs.get64 r).setWidth 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testw %r, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_reg_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m &&& (s.regs.get64 r).setWidth 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testl %r, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_reg_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m &&& (s.regs.get64 r).setWidth 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testq %r, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_reg_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m &&& s.regs.get64 r
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testb $i, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := BitVec.ofInt 8 m &&& i.toBitVec.truncate 8
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testw $i, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := BitVec.ofInt 16 m &&& i.toBitVec.truncate 16
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testl $i, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := BitVec.ofInt 32 m &&& i.toBitVec.truncate 32
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `testq $i, d(%rb,%idx)`: no write; the flags of the conjunction, `af` left arbitrary. -/
@[spec low] theorem MachineWP.test_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := BitVec.ofInt 64 m &&& i.toBitVec.truncate 64
            ∀ af : Bool, WP.wp p Q E
              { s with
                  status := StatusFlags.from_result v
                      { cf := false, of := false, af } }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.test (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `negb %r`. -/
@[spec low] theorem MachineWP.neg_reg_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let b := (s.regs.get64 r).setWidth 8
        let v := -b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } } ⦄
      (Directive.instr (.regular asz .W8 (.neg (.reg (.low r .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `negw %r`. -/
@[spec low] theorem MachineWP.neg_reg_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let b := (s.regs.get64 r).setWidth 16
        let v := -b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } } ⦄
      (Directive.instr (.regular asz .W16 (.neg (.reg (.low r .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `negl %r`. -/
@[spec low] theorem MachineWP.neg_reg_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let b := (s.regs.get64 r).setWidth 32
        let v := -b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } } ⦄
      (Directive.instr (.regular asz .W32 (.neg (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `negq %r`. -/
@[spec low] theorem MachineWP.neg_reg_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let v := -b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.neg (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `negb d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.neg_mem_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let b := BitVec.ofInt 8 m
            let v := -b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W8 (.neg (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `negw d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.neg_mem_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let b := BitVec.ofInt 16 m
            let v := -b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W16 (.neg (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `negl d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.neg_mem_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let b := BitVec.ofInt 32 m
            let v := -b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32 (.neg (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `negq d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.neg_mem_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let b := BitVec.ofInt 64 m
            let v := -b
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed } }) ⦄
      (Directive.instr (.regular .W64 .W64 (.neg (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `notb %r`. -/
@[spec low] theorem MachineWP.not_reg_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let v := ~~~(s.regs.get64 r).setWidth 8
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v) } ⦄
      (Directive.instr (.regular asz .W8 (.not (.reg (.low r .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `notw %r`. -/
@[spec low] theorem MachineWP.not_reg_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let v := ~~~(s.regs.get64 r).setWidth 16
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v) } ⦄
      (Directive.instr (.regular asz .W16 (.not (.reg (.low r .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `notl %r`. -/
@[spec low] theorem MachineWP.not_reg_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let v := ~~~(s.regs.get64 r).setWidth 32
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32 (.not (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `notq %r`. -/
@[spec low] theorem MachineWP.not_reg_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let v := ~~~s.regs.get64 r
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `notb d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.not_mem_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let v := ~~~BitVec.ofInt 8 m
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt }) ⦄
      (Directive.instr (.regular .W64 .W8 (.not (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `notw d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.not_mem_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let v := ~~~BitVec.ofInt 16 m
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt }) ⦄
      (Directive.instr (.regular .W64 .W16 (.not (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `notl d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.not_mem_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let v := ~~~BitVec.ofInt 32 m
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt }) ⦄
      (Directive.instr (.regular .W64 .W32 (.not (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `notq d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.not_mem_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let v := ~~~BitVec.ofInt 64 m
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt }) ⦄
      (Directive.instr (.regular .W64 .W64 (.not (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `decb %r`. -/
@[spec low] theorem MachineWP.dec_reg_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let v := a - 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                    of := v.signed != a.signed - 1 } } ⦄
      (Directive.instr (.regular asz .W8 (.dec (.reg (.low r .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `decw %r`. -/
@[spec low] theorem MachineWP.dec_reg_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let v := a - 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                    of := v.signed != a.signed - 1 } } ⦄
      (Directive.instr (.regular asz .W16 (.dec (.reg (.low r .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `decl %r`. -/
@[spec low] theorem MachineWP.dec_reg_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a - 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((v).setWidth 64),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                    of := v.signed != a.signed - 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.dec (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `decq %r`. -/
@[spec low] theorem MachineWP.dec_reg_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a - 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                    of := v.signed != a.signed - 1 } } ⦄
      (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `decb d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.dec_mem_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            let a := BitVec.ofInt 8 m
            let v := a - 1
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := s.status.cf,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                        of := v.signed != a.signed - 1 } }) ⦄
      (Directive.instr (.regular .W64 .W8 (.dec (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `decw d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.dec_mem_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            let a := BitVec.ofInt 16 m
            let v := a - 1
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := s.status.cf,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                        of := v.signed != a.signed - 1 } }) ⦄
      (Directive.instr (.regular .W64 .W16 (.dec (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `decl d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.dec_mem_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let v := a - 1
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := s.status.cf,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                        of := v.signed != a.signed - 1 } }) ⦄
      (Directive.instr (.regular .W64 .W32 (.dec (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `decq d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.dec_mem_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            let a := BitVec.ofInt 64 m
            let v := a - 1
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 v.toInt,
                  status := StatusFlags.from_result v
                      { cf := s.status.cf,
                        af := (v.take 4).unsigned != (a.take 4).unsigned - 1,
                        of := v.signed != a.signed - 1 } }) ⦄
      (Directive.instr (.regular .W64 .W64 (.dec (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movb %rs, %rd`: the low bits replaced. -/
@[spec low] theorem MachineWP.mov_reg_reg_w8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow ((s.regs.get64 rs).setWidth 8)) } ⦄
      (Directive.instr (.regular asz .W8
          (.mov (.reg (.low rd .W8)) (.regOrMem (.reg (.low rs .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movw %rs, %rd`: the low bits replaced. -/
@[spec low] theorem MachineWP.mov_reg_reg_w16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow ((s.regs.get64 rs).setWidth 16)) } ⦄
      (Directive.instr (.regular asz .W16
          (.mov (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movb $i, %r`: the low bits replaced. -/
@[spec low] theorem MachineWP.mov_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (i.toBitVec.truncate 8)) } ⦄
      (Directive.instr (.regular asz .W8 (.mov (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movw $i, %r`: the low bits replaced. -/
@[spec low] theorem MachineWP.mov_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (i.toBitVec.truncate 16)) } ⦄
      (Directive.instr (.regular asz .W16 (.mov (.reg (.low r .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movb d(%rb,%idx), %r`. -/
@[spec low] theorem MachineWP.mov_load_mem_w8_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (BitVec.ofInt 8 m)) }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movw d(%rb,%idx), %r`. -/
@[spec low] theorem MachineWP.mov_load_mem_w16_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (BitVec.ofInt 16 m)) }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg rb), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movb %r, d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.mov_store_mem_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 ((s.regs.get64 r).setWidth 8).toInt }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movw %r, d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.mov_store_mem_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 ((s.regs.get64 r).setWidth 16).toInt }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movq %r, d(%rb,%idx)`. -/
@[spec low] theorem MachineWP.mov_store_mem_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 (s.regs.get64 r).toInt }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movb $i, d(%rb,%idx)`: the immediate truncated. -/
@[spec low] theorem MachineWP.mov_mem_imm_w8_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 (i.toBitVec.truncate 8).toInt }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movw $i, d(%rb,%idx)`: the immediate truncated. -/
@[spec low] theorem MachineWP.mov_mem_imm_w16_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 2 (i.toBitVec.truncate 16).toInt }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movl $i, d(%rb,%idx)`: the immediate truncated. -/
@[spec low] theorem MachineWP.mov_mem_imm_w32_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 4 (i.toBitVec.truncate 32).toInt }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movq $i, d(%rb,%idx)`: the immediate truncated. -/
@[spec low] theorem MachineWP.mov_mem_imm_w64_spec (rb : Reg64) (idx : Option AddrIndex) (d : Int64) (i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 8 (i.toBitVec.truncate 64).toInt }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg rb), idx, .int64 d⟩) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movzx` from `%rs` (8 bits) into `%rd` (32 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_reg_reg_w32_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((((s.regs.get64 rs).setWidth 8).zeroExtend 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.movzx (w' := .W8) (.reg (.low rd .W32)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movzx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (32 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_load_mem_w32_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((((BitVec.ofInt 8 m).zeroExtend 32)).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W8) (.reg (.low rd .W32)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movzx` from `%rs` (16 bits) into `%rd` (32 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_reg_reg_w32_16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((((s.regs.get64 rs).setWidth 16).zeroExtend 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.movzx (w' := .W16) (.reg (.low rd .W32)) (.reg (.low rs .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movzx` from the 2 bytes at `d(%rb,%idx)` into `%rd` (32 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_load_mem_w32_16_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((((BitVec.ofInt 16 m).zeroExtend 32)).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movzx (w' := .W16) (.reg (.low rd .W32)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movzx` from `%rs` (8 bits) into `%rd` (64 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_reg_reg_w64_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W64
          (.movzx (w' := .W8) (.reg (.low rd .W64)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movzx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (64 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_load_mem_w64_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((BitVec.ofInt 8 m).zeroExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movzx (w' := .W8) (.reg (.low rd .W64)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movzx` from `%rs` (16 bits) into `%rd` (64 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_reg_reg_w64_16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 16).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W64
          (.movzx (w' := .W16) (.reg (.low rd .W64)) (.reg (.low rs .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movzx` from the 2 bytes at `d(%rb,%idx)` into `%rd` (64 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_load_mem_w64_16_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((BitVec.ofInt 16 m).zeroExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movzx (w' := .W16) (.reg (.low rd .W64)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movzx` from `%rs` (8 bits) into `%rd` (16 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_reg_reg_w16_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow (((s.regs.get64 rs).setWidth 8).zeroExtend 16)) } ⦄
      (Directive.instr (.regular asz .W16
          (.movzx (w' := .W8) (.reg (.low rd .W16)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movzx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (16 bits), zero-extended. -/
@[spec low] theorem MachineWP.movzx_load_mem_w16_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow ((BitVec.ofInt 8 m).zeroExtend 16)) }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.movzx (w' := .W8) (.reg (.low rd .W16)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (8 bits) into `%rd` (32 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w32_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((((s.regs.get64 rs).setWidth 8).signExtend 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.movsx (w' := .W8) (.reg (.low rd .W32)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (32 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w32_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((((BitVec.ofInt 8 m).signExtend 32)).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movsx (w' := .W8) (.reg (.low rd .W32)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (16 bits) into `%rd` (32 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w32_16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((((s.regs.get64 rs).setWidth 16).signExtend 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.movsx (w' := .W16) (.reg (.low rd .W32)) (.reg (.low rs .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 2 bytes at `d(%rb,%idx)` into `%rd` (32 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w32_16_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((((BitVec.ofInt 16 m).signExtend 32)).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.movsx (w' := .W16) (.reg (.low rd .W32)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (8 bits) into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w64_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 8).signExtend 64) } ⦄
      (Directive.instr (.regular asz .W64
          (.movsx (w' := .W8) (.reg (.low rd .W64)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w64_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((BitVec.ofInt 8 m).signExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W8) (.reg (.low rd .W64)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (16 bits) into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w64_16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 16).signExtend 64) } ⦄
      (Directive.instr (.regular asz .W64
          (.movsx (w' := .W16) (.reg (.low rd .W64)) (.reg (.low rs .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 2 bytes at `d(%rb,%idx)` into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w64_16_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((BitVec.ofInt 16 m).signExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W16) (.reg (.low rd .W64)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (8 bits) into `%rd` (16 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w16_8_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow (((s.regs.get64 rs).setWidth 8).signExtend 16)) } ⦄
      (Directive.instr (.regular asz .W16
          (.movsx (w' := .W8) (.reg (.low rd .W16)) (.reg (.low rs .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 1 bytes at `d(%rb,%idx)` into `%rd` (16 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w16_8_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 1 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow ((BitVec.ofInt 8 m).signExtend 16)) }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.movsx (w' := .W8) (.reg (.low rd .W16)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `movsx` from `%rs` (32 bits) into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_reg_reg_w64_32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).signExtend 64) } ⦄
      (Directive.instr (.regular asz .W64
          (.movsx (w' := .W32) (.reg (.low rd .W64)) (.reg (.low rs .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `movsx` from the 4 bytes at `d(%rb,%idx)` into `%rd` (64 bits), sign-extended. -/
@[spec low] theorem MachineWP.movsx_load_mem_w64_32_spec (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((BitVec.ofInt 32 m).signExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W32) (.reg (.low rd .W64)) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmovccw %rs, %rd`: the destination is written either way (a 32-bit
destination is zero-extended even when the condition fails). -/
@[spec low] theorem MachineWP.cmovcc_reg_reg_w16_spec (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow (if cc.interp s.status then (s.regs.get64 rs).setWidth 16 else (s.regs.get64 rd).setWidth 16)) } ⦄
      (Directive.instr (.regular asz .W16
          (.cmovcc cc (.low rd .W16) (.reg (.low rs .W16)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmovccw d(%rb,%idx), %rd`: the bytes are read either way. -/
@[spec low] theorem MachineWP.cmovcc_load_mem_w16_spec (cc : CondCode) (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 2).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 2 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow (if cc.interp s.status then BitVec.ofInt 16 m else (s.regs.get64 rd).setWidth 16)) }) ⦄
      (Directive.instr (.regular .W64 .W16
          (.cmovcc cc (.low rd .W16) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmovccl %rs, %rd`: the destination is written either way (a 32-bit
destination is zero-extended even when the condition fails). -/
@[spec low] theorem MachineWP.cmovcc_reg_reg_w32_spec (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (((if cc.interp s.status then (s.regs.get64 rs).setWidth 32 else (s.regs.get64 rd).setWidth 32)).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.cmovcc cc (.low rd .W32) (.reg (.low rs .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmovccl d(%rb,%idx), %rd`: the bytes are read either way. -/
@[spec low] theorem MachineWP.cmovcc_load_mem_w32_spec (cc : CondCode) (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd (((if cc.interp s.status then BitVec.ofInt 32 m else (s.regs.get64 rd).setWidth 32)).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.cmovcc cc (.low rd .W32) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `cmovccq %rs, %rd`: the destination is written either way (a 32-bit
destination is zero-extended even when the condition fails). -/
@[spec low] theorem MachineWP.cmovcc_reg_reg_w64_spec (asz : Width) (cc : CondCode) (rd rs : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd (if cc.interp s.status then s.regs.get64 rs else s.regs.get64 rd) } ⦄
      (Directive.instr (.regular asz .W64
          (.cmovcc cc (.low rd .W64) (.reg (.low rs .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `cmovccq d(%rb,%idx), %rd`: the bytes are read either way. -/
@[spec low] theorem MachineWP.cmovcc_load_mem_w64_spec (cc : CondCode) (rd : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 8).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 8 = some m →
            WP.wp p Q E
              { s with
                  regs := s.regs.set64 rd (if cc.interp s.status then BitVec.ofInt 64 m else s.regs.get64 rd) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.cmovcc cc (.low rd .W64) (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `setcc %r8`: the low byte gets the condition as 0 or 1. -/
@[spec low] theorem MachineWP.setcc_reg_spec (asz : Width) (cc : CondCode) (r : Reg64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (BitVec.ofNat 8 (cc.interp s.status).toNat)) } ⦄
      (Directive.instr (.regular asz .W8 (.setcc cc (.reg (.low r .W8)))) :: p)
    ⦃ Q; E ⦄ :=
  reg_rule

/-- `setcc d(%rb,%idx)`: the byte gets the condition as 0 or 1. -/
@[spec low] theorem MachineWP.setcc_mem_spec (cc : CondCode) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem addr 1).isSome = true)
          ⊓ (
            WP.wp p Q E
              { s with
                  dmem := Mem.storeInt s.dmem addr 1 (BitVec.ofNat 8 (cc.interp s.status).toNat).toInt }) ⦄
      (Directive.instr (.regular .W64 .W8 (.setcc cc (.mem ⟨some (.reg rb), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  mem_rule

/-- `imulw $i, %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_imm_w16_spec (asz : Width) (rd rs : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 16
        let b := i.toBitVec.truncate 16
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.imul (some (.reg (.low rd .W16))) (.reg (.low rs .W16)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `imulw %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_w16_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 16
        let b := (s.regs.get64 rs).setWidth 16
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((s.regs.get64 rd).replaceLow v),
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W16
          (.imul none (.reg (.low rd .W16)) (.regOrMem (.reg (.low rs .W16))))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `imull $i, %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_imm_w32_spec (asz : Width) (rd rs : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rs).setWidth 32
        let b := i.toBitVec.truncate 32
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.imul (some (.reg (.low rd .W32))) (.reg (.low rs .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `imull %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_w32_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 rd).setWidth 32
        let b := (s.regs.get64 rs).setWidth 32
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd ((v).setWidth 64),
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W32
          (.imul none (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `imulq $i, %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_imm_w64_spec (asz : Width) (rd rs : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := i.toBitVec.truncate 64
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.imul (some (.reg (.low rd .W64))) (.reg (.low rs .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `imulq %rs, %rd`: the truncated product; `cf`/`of` say whether it
overflowed, the other flags are left arbitrary. -/
@[spec low] theorem MachineWP.imul_reg_reg_w64_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rd
        let b := s.regs.get64 rs
        let v := a * b
        ∀ sf : Bool, ∀ zf : Bool, ∀ af : Bool, ∀ pf : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status :=
                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,
                  sf := sf, of := v.signed != a.signed * b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.imul none (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  nondet4_rule

/-- `leal d(%rb,%idx), %r`: the address, truncated and zero-extended. -/
@[spec low] theorem MachineWP.lea_mem_w32_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((((s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec).setWidth 32)).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.lea (.low r .W32) ⟨some (.reg rb), idx, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  lea_rule

/-- `leal d(,%i,c), %r` (no base, 64-bit address size): the index times the
scale plus the displacement, truncated and zero-extended. -/
@[spec low] theorem MachineWP.lea_index_w32_spec (r i : Reg64) (c : Width) (d : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((((AddrIndex.offset64 (some ⟨i, c⟩) s.regs + d.toBitVec).setWidth 32)).setWidth 64) } ⦄
      (Directive.instr (.regular .W64 .W32
          (.lea (.low r .W32) ⟨none, some ⟨i, c⟩, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  lea_rule

/-- `leaq d(%rb,%idx), %r`: the address. -/
@[spec low] theorem MachineWP.lea_mem_w64_spec (r : Reg64) (rb : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec)) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64) ⟨some (.reg rb), idx, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  lea_rule

/-- `leaq d(,%i,c), %r` (no base, 64-bit address size): the index times the
scale plus the displacement. -/
@[spec low] theorem MachineWP.lea_index_w64_spec (r i : Reg64) (c : Width) (d : Int64) :
    ⦃ fun s =>
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((AddrIndex.offset64 (some ⟨i, c⟩) s.regs + d.toBitVec)) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64) ⟨none, some ⟨i, c⟩, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  lea_rule

/-- `shlb $i, %r`: shifted left by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a <<< n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.shl (.reg (.low r .W8)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shlw $i, %r`: shifted left by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a <<< n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.shl (.reg (.low r .W16)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shll $i, %r`: shifted left by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a <<< n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shlq $i, %r`: shifted left by the immediate mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := i.toBitVec.toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a <<< n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shlb %cl, %r`: shifted left by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_cl_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a <<< n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.shl (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shlw %cl, %r`: shifted left by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_cl_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a <<< n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.shl (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shll %cl, %r`: shifted left by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_cl_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a <<< n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shlq %cl, %r`: shifted left by `%cl` mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.shl_reg_cl_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := (s.regs.get64 .rcx).toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a <<< n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a <<< n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrb $i, %r`: shifted right logically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.ushiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.shr (.reg (.low r .W8)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrw $i, %r`: shifted right logically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.ushiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.shr (.reg (.low r .W16)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrl $i, %r`: shifted right logically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a.ushiftRight n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrq $i, %r`: shifted right logically by the immediate mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := i.toBitVec.toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a.ushiftRight n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrb %cl, %r`: shifted right logically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_cl_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.ushiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.shr (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrw %cl, %r`: shifted right logically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_cl_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.ushiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.shr (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrl %cl, %r`: shifted right logically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_cl_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a.ushiftRight n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `shrq %cl, %r`: shifted right logically by `%cl` mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.shr_reg_cl_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := (s.regs.get64 .rcx).toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a.ushiftRight n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarb $i, %r`: shifted right arithmetically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_imm_w8_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.sshiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.sar (.reg (.low r .W8)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarw $i, %r`: shifted right arithmetically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_imm_w16_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.sshiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.sar (.reg (.low r .W16)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarl $i, %r`: shifted right arithmetically by the immediate mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_imm_w32_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := i.toBitVec.toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a.sshiftRight n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.sar (.reg (.low r .W32)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarq $i, %r`: shifted right arithmetically by the immediate mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_imm_w64_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := i.toBitVec.toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a.sshiftRight n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.sar (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarb %cl, %r`: shifted right arithmetically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_cl_w8_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 8
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.sshiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W8 (.sar (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarw %cl, %r`: shifted right arithmetically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_cl_w16_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 16
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r ((s.regs.get64 r).replaceLow (a.sshiftRight n)),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W16 (.sar (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarl %cl, %r`: shifted right arithmetically by `%cl` mod 32; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 32 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_cl_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := (s.regs.get64 .rcx).toNat % 256 % 32
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (((a.sshiftRight n)).setWidth 64),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W32 (.sar (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- `sarq %cl, %r`: shifted right arithmetically by `%cl` mod 64; `zf`, `sf`, `pf`
from the result (`StatusFlags.from_result`), `cf`, `af`, `of` left arbitrary. A count of
zero mod 64 changes nothing. -/
@[spec low] theorem MachineWP.sar_reg_cl_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let n := (s.regs.get64 .rcx).toNat % 256 % 64
        ∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := if n = 0 then s.regs else s.regs.set64 r (a.sshiftRight n),
              status := if n = 0 then s.status
                else StatusFlags.from_result (a.sshiftRight n) { s.status with cf, af, of } } ⦄
      (Directive.instr (.regular asz .W64 (.sar (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  shift_rule

/-- The register file after `shlb %cl, %r` (as `shl_reg_cl_w8_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shlCl8 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8) <<< ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `shlCl8` at a known nonzero count. -/
theorem MachineWP.shlCl8_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shlCl8 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8) <<< n)) := by
  simp only [shlCl8, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shlCl8` at a count of zero. -/
theorem MachineWP.shlCl8_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shlCl8 r regs = regs := by
  simp only [shlCl8, hc, hn, ite_true]

/-- `shlb %cl, %r` with the flags forgotten (any status) and the register file
behind `shlCl8`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shl_reg_cl_w8_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shlCl8 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W8 (.shl (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w8_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 8) <<< ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shlCl8] at h
      split <;> simp_all)

/-- The register file after `shlw %cl, %r` (as `shl_reg_cl_w16_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shlCl16 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16) <<< ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `shlCl16` at a known nonzero count. -/
theorem MachineWP.shlCl16_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shlCl16 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16) <<< n)) := by
  simp only [shlCl16, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shlCl16` at a count of zero. -/
theorem MachineWP.shlCl16_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shlCl16 r regs = regs := by
  simp only [shlCl16, hc, hn, ite_true]

/-- `shlw %cl, %r` with the flags forgotten (any status) and the register file
behind `shlCl16`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shl_reg_cl_w16_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shlCl16 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W16 (.shl (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w16_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 16) <<< ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shlCl16] at h
      split <;> simp_all)

/-- The register file after `shll %cl, %r` (as `shl_reg_cl_w32_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shlCl32 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r (((((regs.get64 r).setWidth 32) <<< ((regs.get64 .rcx).toNat % 256 % 32))).setWidth 64)

omit [CodeEnv] in
/-- `shlCl32` at a known nonzero count. -/
theorem MachineWP.shlCl32_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shlCl32 r regs = regs.set64 r (((((regs.get64 r).setWidth 32) <<< n)).setWidth 64) := by
  simp only [shlCl32, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shlCl32` at a count of zero. -/
theorem MachineWP.shlCl32_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shlCl32 r regs = regs := by
  simp only [shlCl32, hc, hn, ite_true]

/-- `shll %cl, %r` with the flags forgotten (any status) and the register file
behind `shlCl32`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shl_reg_cl_w32_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shlCl32 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 32) <<< ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shlCl32] at h
      split <;> simp_all)

/-- The register file after `shlq %cl, %r` (as `shl_reg_cl_w64_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shlCl64 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 64 = 0 then regs
  else regs.set64 r ((regs.get64 r) <<< ((regs.get64 .rcx).toNat % 256 % 64))

omit [CodeEnv] in
/-- `shlCl64` at a known nonzero count. -/
theorem MachineWP.shlCl64_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = n) (h0 : n ≠ 0) :
    shlCl64 r regs = regs.set64 r ((regs.get64 r) <<< n) := by
  simp only [shlCl64, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shlCl64` at a count of zero. -/
theorem MachineWP.shlCl64_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = 0) :
    shlCl64 r regs = regs := by
  simp only [shlCl64, hc, hn, ite_true]

/-- `shlq %cl, %r` with the flags forgotten (any status) and the register file
behind `shlCl64`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shl_reg_cl_w64_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shlCl64 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w64_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 64 = 0 then s.status
        else StatusFlags.from_result ((s.regs.get64 r) <<< ((s.regs.get64 .rcx).toNat % 256 % 64)) { s.status with cf, af, of })
      simp only [shlCl64] at h
      split <;> simp_all)

/-- The register file after `shrb %cl, %r` (as `shr_reg_cl_w8_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shrCl8 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8).ushiftRight ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `shrCl8` at a known nonzero count. -/
theorem MachineWP.shrCl8_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shrCl8 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8).ushiftRight n)) := by
  simp only [shrCl8, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shrCl8` at a count of zero. -/
theorem MachineWP.shrCl8_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shrCl8 r regs = regs := by
  simp only [shrCl8, hc, hn, ite_true]

/-- `shrb %cl, %r` with the flags forgotten (any status) and the register file
behind `shrCl8`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shr_reg_cl_w8_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shrCl8 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W8 (.shr (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w8_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 8).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shrCl8] at h
      split <;> simp_all)

/-- The register file after `shrw %cl, %r` (as `shr_reg_cl_w16_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shrCl16 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16).ushiftRight ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `shrCl16` at a known nonzero count. -/
theorem MachineWP.shrCl16_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shrCl16 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16).ushiftRight n)) := by
  simp only [shrCl16, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shrCl16` at a count of zero. -/
theorem MachineWP.shrCl16_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shrCl16 r regs = regs := by
  simp only [shrCl16, hc, hn, ite_true]

/-- `shrw %cl, %r` with the flags forgotten (any status) and the register file
behind `shrCl16`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shr_reg_cl_w16_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shrCl16 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W16 (.shr (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w16_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 16).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shrCl16] at h
      split <;> simp_all)

/-- The register file after `shrl %cl, %r` (as `shr_reg_cl_w32_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shrCl32 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r (((((regs.get64 r).setWidth 32).ushiftRight ((regs.get64 .rcx).toNat % 256 % 32))).setWidth 64)

omit [CodeEnv] in
/-- `shrCl32` at a known nonzero count. -/
theorem MachineWP.shrCl32_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    shrCl32 r regs = regs.set64 r (((((regs.get64 r).setWidth 32).ushiftRight n)).setWidth 64) := by
  simp only [shrCl32, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shrCl32` at a count of zero. -/
theorem MachineWP.shrCl32_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    shrCl32 r regs = regs := by
  simp only [shrCl32, hc, hn, ite_true]

/-- `shrl %cl, %r` with the flags forgotten (any status) and the register file
behind `shrCl32`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shr_reg_cl_w32_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shrCl32 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 32).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [shrCl32] at h
      split <;> simp_all)

/-- The register file after `shrq %cl, %r` (as `shr_reg_cl_w64_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.shrCl64 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 64 = 0 then regs
  else regs.set64 r ((regs.get64 r).ushiftRight ((regs.get64 .rcx).toNat % 256 % 64))

omit [CodeEnv] in
/-- `shrCl64` at a known nonzero count. -/
theorem MachineWP.shrCl64_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = n) (h0 : n ≠ 0) :
    shrCl64 r regs = regs.set64 r ((regs.get64 r).ushiftRight n) := by
  simp only [shrCl64, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `shrCl64` at a count of zero. -/
theorem MachineWP.shrCl64_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = 0) :
    shrCl64 r regs = regs := by
  simp only [shrCl64, hc, hn, ite_true]

/-- `shrq %cl, %r` with the flags forgotten (any status) and the register file
behind `shrCl64`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.shr_reg_cl_w64_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := shrCl64 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shr_reg_cl_w64_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 64 = 0 then s.status
        else StatusFlags.from_result ((s.regs.get64 r).ushiftRight ((s.regs.get64 .rcx).toNat % 256 % 64)) { s.status with cf, af, of })
      simp only [shrCl64] at h
      split <;> simp_all)

/-- The register file after `sarb %cl, %r` (as `sar_reg_cl_w8_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.sarCl8 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8).sshiftRight ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `sarCl8` at a known nonzero count. -/
theorem MachineWP.sarCl8_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    sarCl8 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 8).sshiftRight n)) := by
  simp only [sarCl8, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `sarCl8` at a count of zero. -/
theorem MachineWP.sarCl8_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    sarCl8 r regs = regs := by
  simp only [sarCl8, hc, hn, ite_true]

/-- `sarb %cl, %r` with the flags forgotten (any status) and the register file
behind `sarCl8`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.sar_reg_cl_w8_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := sarCl8 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W8 (.sar (.reg (.low r .W8)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.sar_reg_cl_w8_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 8).sshiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [sarCl8] at h
      split <;> simp_all)

/-- The register file after `sarw %cl, %r` (as `sar_reg_cl_w16_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.sarCl16 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16).sshiftRight ((regs.get64 .rcx).toNat % 256 % 32)))

omit [CodeEnv] in
/-- `sarCl16` at a known nonzero count. -/
theorem MachineWP.sarCl16_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    sarCl16 r regs = regs.set64 r ((regs.get64 r).replaceLow (((regs.get64 r).setWidth 16).sshiftRight n)) := by
  simp only [sarCl16, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `sarCl16` at a count of zero. -/
theorem MachineWP.sarCl16_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    sarCl16 r regs = regs := by
  simp only [sarCl16, hc, hn, ite_true]

/-- `sarw %cl, %r` with the flags forgotten (any status) and the register file
behind `sarCl16`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.sar_reg_cl_w16_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := sarCl16 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W16 (.sar (.reg (.low r .W16)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.sar_reg_cl_w16_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 16).sshiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [sarCl16] at h
      split <;> simp_all)

/-- The register file after `sarl %cl, %r` (as `sar_reg_cl_w32_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.sarCl32 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 32 = 0 then regs
  else regs.set64 r (((((regs.get64 r).setWidth 32).sshiftRight ((regs.get64 .rcx).toNat % 256 % 32))).setWidth 64)

omit [CodeEnv] in
/-- `sarCl32` at a known nonzero count. -/
theorem MachineWP.sarCl32_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = n) (h0 : n ≠ 0) :
    sarCl32 r regs = regs.set64 r (((((regs.get64 r).setWidth 32).sshiftRight n)).setWidth 64) := by
  simp only [sarCl32, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `sarCl32` at a count of zero. -/
theorem MachineWP.sarCl32_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 32 = 0) :
    sarCl32 r regs = regs := by
  simp only [sarCl32, hc, hn, ite_true]

/-- `sarl %cl, %r` with the flags forgotten (any status) and the register file
behind `sarCl32`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.sar_reg_cl_w32_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := sarCl32 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.sar (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.sar_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 32 = 0 then s.status
        else StatusFlags.from_result (((s.regs.get64 r).setWidth 32).sshiftRight ((s.regs.get64 .rcx).toNat % 256 % 32)) { s.status with cf, af, of })
      simp only [sarCl32] at h
      split <;> simp_all)

/-- The register file after `sarq %cl, %r` (as `sar_reg_cl_w64_spec`), behind a
name: the state after a run of shifts by `%cl` stays linear in their number. -/
def MachineWP.sarCl64 (r : Reg64) (regs : Reg64s) : Reg64s :=
  if (regs.get64 .rcx).toNat % 256 % 64 = 0 then regs
  else regs.set64 r ((regs.get64 r).sshiftRight ((regs.get64 .rcx).toNat % 256 % 64))

omit [CodeEnv] in
/-- `sarCl64` at a known nonzero count. -/
theorem MachineWP.sarCl64_of_rcx {r : Reg64} {regs : Reg64s} {c : BitVec 64} (n : Nat)
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = n) (h0 : n ≠ 0) :
    sarCl64 r regs = regs.set64 r ((regs.get64 r).sshiftRight n) := by
  simp only [sarCl64, hc, hn, h0, ite_false]

omit [CodeEnv] in
/-- `sarCl64` at a count of zero. -/
theorem MachineWP.sarCl64_of_rcx0 {r : Reg64} {regs : Reg64s} {c : BitVec 64}
    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % 64 = 0) :
    sarCl64 r regs = regs := by
  simp only [sarCl64, hc, hn, ite_true]

/-- `sarq %cl, %r` with the flags forgotten (any status) and the register file
behind `sarCl64`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/
theorem MachineWP.sar_reg_cl_w64_spec' (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E { s with regs := sarCl64 r s.regs, status := st } ⦄
      (Directive.instr (.regular asz .W64 (.sar (.reg (.low r .W64)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.sar_reg_cl_w64_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % 64 = 0 then s.status
        else StatusFlags.from_result ((s.regs.get64 r).sshiftRight ((s.regs.get64 .rcx).toNat % 256 % 64)) { s.status with cf, af, of })
      simp only [sarCl64] at h
      split <;> simp_all)

-- `open scoped Kraken.Rules.IntMisc.ShiftClOpaque`: the flags-forgetting shifts by `%cl`.
namespace Kraken.Rules.IntMisc.ShiftClOpaque
attribute [scoped spec] MachineWP.shl_reg_cl_w8_spec'
  MachineWP.shl_reg_cl_w16_spec'
  MachineWP.shl_reg_cl_w32_spec'
  MachineWP.shl_reg_cl_w64_spec'
  MachineWP.shr_reg_cl_w8_spec'
  MachineWP.shr_reg_cl_w16_spec'
  MachineWP.shr_reg_cl_w32_spec'
  MachineWP.shr_reg_cl_w64_spec'
  MachineWP.sar_reg_cl_w8_spec'
  MachineWP.sar_reg_cl_w16_spec'
  MachineWP.sar_reg_cl_w32_spec'
  MachineWP.sar_reg_cl_w64_spec'
end Kraken.Rules.IntMisc.ShiftClOpaque

end Specs

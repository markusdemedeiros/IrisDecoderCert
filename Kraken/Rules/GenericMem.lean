import Kraken.MachineWP

/-!
# Memory-operand rules over any `disp(base,index,scale)` operand

The rules in `MachineWP.lean` are stated per addressing shape: `d(%b)`,
`(%b,%i,1)`, `d(%b,%i,1)`, and so on, one theorem each. Compiled C uses every
shape, so this file states the memory rules once over the operand
`⟨some (.reg b), idx, .int64 d⟩`, where the index `idx : Option AddrIndex` is
absent or any register and scale. That covers `d(%b)`, `(%b)`, `(%b,%i,s)`
and `d(%b,%i,s)` alike.

The address is `regs.get64 b + AddrIndex.offset64 idx regs + d.toBitVec`.
`AddrIndex.offset64` reduces by `simp`/`grind` at a concrete index (`none`
to `0`, scale 1 to the register itself, any other scale to a product), and
`+ 0` disappears. At the shapes `MachineWP.lean` already covers, the address
is therefore the one the shape-specific rule states.

The rules here are `@[spec low]`. Where a shape-specific rule fits, `vcgen`
keeps using it, and the examples written against those rules keep their
proofs.

`d(%rip)` operands (`sym(%rip)` after the parser) and base-less operands are
not covered here: their addresses have a different form
(`AddrExpr.zeroExtend_interp_rip_label`, `_index32_disp`). This file adds the
address of `sym+o(%rip)` and `sym-o(%rip)` (`AddrExpr.zeroExtend_interp_rip_label_add`,
`_sub`: the label plus or minus `o`) and their `lea` rules; the `sym(%rip)`
rules of `PackedSse.lean` and `ScalarFloat.lean` have `sym+o(%rip)` twins
(`_rip_off_spec`).
-/

open Kraken MachineWP Std.WP Lean.Order

/-- The index part of an address: absent, or the register times the scale. -/
def AddrIndex.offset64 : Option AddrIndex → Reg64s → BitVec 64
  | none, _ => 0
  | some ⟨i, c⟩, regs => regs.get64 i * BitVec.ofNat 64 c.bytes

@[simp] theorem AddrIndex.offset64_none (regs : Reg64s) :
    AddrIndex.offset64 none regs = 0 := rfl

@[simp] theorem AddrIndex.offset64_scale1 (i : Reg64) (regs : Reg64s) :
    AddrIndex.offset64 (some ⟨i, .W8⟩) regs = regs.get64 i := by
  simp [AddrIndex.offset64]

@[simp] theorem AddrIndex.offset64_scale2 (i : Reg64) (regs : Reg64s) :
    AddrIndex.offset64 (some ⟨i, .W16⟩) regs = regs.get64 i * 2#64 := rfl

@[simp] theorem AddrIndex.offset64_scale4 (i : Reg64) (regs : Reg64s) :
    AddrIndex.offset64 (some ⟨i, .W32⟩) regs = regs.get64 i * 4#64 := rfl

@[simp] theorem AddrIndex.offset64_scale8 (i : Reg64) (regs : Reg64s) :
    AddrIndex.offset64 (some ⟨i, .W64⟩) regs = regs.get64 i * 8#64 := rfl

/-- A displacement literal is the bit-vector literal, so that address terms
match the `Blocks.Inside` rules (`b + x + 64` against the block at `b + 64`). -/
@[simp] theorem Int64.toBitVec_ofNat_lit (n : Nat) :
    Int64.toBitVec (OfNat.ofNat n) = BitVec.ofNat 64 n := rfl

/- A register read after a write is resolved while `grind` normalises its
input, not only by E-matching (`Reg64s.get64_set64` is `@[simp, grind =]` in
`Specs.lean`). E-matching puts the value in the read's equivalence class, but
an operation that needs the value as a term then still sees the read: a
shift by `%cl` after `mov $3,%ecx` is `x <<< (get64 (set64 … rcx 3) rcx).toNat
% 256 % 32`, and `grind` has no rule for `x <<< n` with `n` merely equal to 3.
Normalising the read first makes the count the literal 3, which `grind`'s
simprocs fold. -/
/-! The `grind norm` lemmas above are scoped (`open scoped
Kraken.Rules.GenericMem.Norm`), so that importing this file (or a rule file built
on it) does not change `grind`'s normalisation elsewhere. -/
namespace Kraken.Rules.GenericMem.Norm
attribute [scoped grind norm] AddrIndex.offset64_none AddrIndex.offset64_scale1
  AddrIndex.offset64_scale2 AddrIndex.offset64_scale4 AddrIndex.offset64_scale8
  Int64.toBitVec_ofNat_lit Reg64s.get64_set64
end Kraken.Rules.GenericMem.Norm

open scoped Kraken.Rules.GenericMem.Norm

/-- The address a `disp(base,index,scale)` operand computes at 64-bit address
size, for any index (or none): base plus index times scale plus displacement. -/
theorem AddrExpr.zeroExtend_interp_base_idx_disp [Labels] (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), idx, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + AddrIndex.offset64 idx regs + d.toBitVec := by
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  cases idx with
  | none =>
    simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, AddrIndex.offset64]
    rw [htake, hsigned]
    show BitVec.ofInt 64 _ = _
    simp [BitVec.ofInt_add, BitVec.ofInt_toInt]
  | some ix =>
    obtain ⟨i, c⟩ := ix
    simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, AddrIndex.offset64]
    rw [htake, htake, hsigned, hsigned]
    show BitVec.ofInt 64 _ = _
    simp [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]

/-- The address a `sym+o(%rip)` operand computes: the symbol's plus `o`. The
parser writes the displacement `(sym + o) - .`, relative to the address behind
the instruction, where `%rip` points. -/
theorem AddrExpr.zeroExtend_interp_rip_label_add [Labels] (l : Label) (o : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩)
        regs rng).zeroExtend 64)
      = (label l).toBitVec + o.toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp]
  show BitVec.ofInt 64 _ = _
  rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt_int64, BitVec.ofInt_toInt_int64,
    Int64.toBitVec_sub, BitVec.add_comm, BitVec.sub_add_cancel, Int64.toBitVec_add]

/-- The address a `sym-o(%rip)` operand computes: the symbol's minus `o`. -/
theorem AddrExpr.zeroExtend_interp_rip_label_sub [Labels] (l : Label) (o : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some .rip, none, .sub (.sub (.label l) (.int64 o)) .after_current_instruction⟩)
        regs rng).zeroExtend 64)
      = (label l).toBitVec - o.toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp]
  show BitVec.ofInt 64 _ = _
  rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt_int64, BitVec.ofInt_toInt_int64,
    Int64.toBitVec_sub, BitVec.add_comm, BitVec.sub_add_cancel, Int64.toBitVec_sub]

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

/-- `movl d(%b,%i,s), %r32` (any index or none): the 4 bytes must be readable;
the tail runs with them zero-extended in the register. -/
@[spec low] theorem MachineWP.mov32_load_mem_spec (r b : Reg64) (idx : Option AddrIndex)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with
              regs := s.regs.set64 r ((BitVec.ofInt 32 v).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_idx_disp,
      Reg64s.set_low32, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `movq d(%b,%i,s), %r` (any index or none): the 8 bytes must be readable;
the tail runs with them in the register. -/
@[spec low] theorem MachineWP.mov_load_mem_spec (r b : Reg64) (idx : Option AddrIndex)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), idx, .int64 d⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_idx_disp,
      Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `movl %r32, d(%b,%i,s)` (any index or none): the 4 bytes must be owned; the
tail runs on the updated memory. -/
@[spec low] theorem MachineWP.mov32_store_mem_spec (b : Reg64) (idx : Option AddrIndex)
    (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 4 ((s.regs.get64 r).setWidth 32).toInt } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), idx, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      Reg64s.get_low32, Width.bytes, hv, Effects.All]
    exact hk _ hpl'

/-- `movaps d(%b,%i,s), %xmm` (any index or none): the 16 bytes must be
readable and 16-byte aligned; the low 128 bits of the register get them. -/
@[spec low] theorem MachineWP.movaps_load_mem_spec (x : RegMm) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨⟨hal, hsome⟩, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_base_idx_disp, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `leaq sym+o(%rip), %r` : the register gets the symbol's address plus `o`,
wherever the instruction sits. -/
@[spec] theorem MachineWP.lea_rip_label_add_spec (r : Reg64) (l : Label) (o : Int64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := (s.regs.set64 r
            (((_root_.Executable.labels cenv).label l).toBitVec + o.toBitVec)) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64)
            ⟨some .rip, none, .sub (.add (.label l) (.int64 o)) .after_current_instruction⟩)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [AddrExpr.zeroExtend_interp_rip_label_add]
    exact hP)

/-- `leaq sym-o(%rip), %r` : the register gets the symbol's address minus `o`. -/
@[spec] theorem MachineWP.lea_rip_label_sub_spec (r : Reg64) (l : Label) (o : Int64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := (s.regs.set64 r
            (((_root_.Executable.labels cenv).label l).toBitVec - o.toBitVec)) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64)
            ⟨some .rip, none, .sub (.sub (.label l) (.int64 o)) .after_current_instruction⟩)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [AddrExpr.zeroExtend_interp_rip_label_sub]
    exact hP)

end Specs

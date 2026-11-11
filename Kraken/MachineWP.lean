/-
The machine-founded weakest precondition. `Executable.wp` is defined by the
baseline interpreter: a fragment `q`, placed anywhere in the ambient code,
runs its cells and every stop lands in the fall-through postcondition at the
placement's end, or in the exit channel at the pc it stopped at. Exits are
pc values: `E : Int64 → MachineData → Prop`. A label exit is
`E ((_root_.Executable.labels cenv).label l)`; a computed exit is `E` at the value.

The step relation `instrStep`, the ambient code `CodeEnv` and the procedure
specifications `ProcSpec`/`ProcSpecK` are in `Kraken.Step`: a caller or a
linker needs those and not this file.
-/
import Kraken.Step
import Kraken.InterpSound

open Kraken
open Std.WP
open Lean.Order

/-! ## The wp -/

/-- The fragment `q` sits at `pc`: a label costs no address, and every other
cell is the next instruction there. -/
def Kraken.Executable.sits (e : Kraken.Executable Directive) (pc : Int64) : Program → Prop
  | [] => True
  | .label _ :: q => e.sits pc q
  | d :: q => ∃ z rest, e.codeAt pc = (d, z) :: rest ∧ e.sits (pc + .ofNat z) q

/-- The address behind the fragment `q` placed at `pc`. -/
def Kraken.Executable.after (e : Kraken.Executable Directive) (pc : Int64) : Program → Int64
  | [] => pc
  | .label _ :: q => e.after pc q
  | _ :: q =>
    match e.codeAt pc with
    | [] => pc
    | (_, z) :: _ => e.after (pc + .ofNat z) q

/-- The run of the fragment `q` from `s`: placed anywhere in the ambient
code, the machine eventually falls through to the placement's end with `Q`,
or stops at a pc satisfying `E`. Re-entry inside the fragment is free: the
judgment is the fixpoint `Eventually`, so a back edge simply keeps stepping. -/
def Kraken.Executable.wp (e : Kraken.Executable Directive) (q : Program) (Q : MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) : Prop :=
  ∀ (pc : Int64), e.sits pc q →
    Eventually (e.instrStep)
      (fun st => (st.2 = e.after pc q ∧ Q st.1) ∨ E st.2 st.1) (s, pc)

theorem Kraken.Executable.wp_mono {e : Kraken.Executable Directive} {q : Program}
    {Q₁ Q₂ : MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : e.wp q Q₁ E₁ s) : e.wp q Q₂ E₂ s := fun pc hpl =>
  eventually_weaken _ _ _ _
    (fun st hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)) (h pc hpl)

/-- The run of `d :: q` is the run of `d` with the run of `q` as its
post: the machine falls through `d` to the address where `q` sits. -/
theorem Kraken.Executable.wp_cons {e : Kraken.Executable Directive} {d : Directive} {q : Program}
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : e.wp [d] (fun s' => e.wp q Q E s') E s) : e.wp (d :: q) Q E s := by
  intro pc hpl
  have hcont : ∀ pc', e.sits pc' q → ∀ st : MachineState,
      (st.2 = pc' ∧ e.wp q Q E st.1) ∨ E st.2 st.1 →
      Eventually e.instrStep (fun st => (st.2 = e.after pc' q ∧ Q st.1) ∨ E st.2 st.1) st := by
    intro pc' hq ⟨sd, spc⟩ hst
    rcases hst with ⟨hpc, hwp⟩ | hE
    · dsimp only at hpc hwp
      subst hpc
      exact hwp _ hq
    · exact .done _ (Or.inr hE)
  cases d with
  | label l =>
    have h1 := h pc trivial
    exact eventually_trans _ _ _ _ h1 (hcont pc hpl)
  | instr i =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)
  | byteArray a =>
    obtain ⟨z, rest, hcode, hq⟩ := hpl
    have h1 := h pc ⟨z, rest, hcode, trivial⟩
    simp only [Executable.after, hcode] at h1 ⊢
    exact eventually_trans _ _ _ _ h1 (hcont _ hq)

namespace MachineWP

/-- A triple on a program is the machine-founded wp of the ambient code. -/
scoped instance instWP [CodeEnv] :
    WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  wpTrans q := ⟨fun Q E s => cenv.wp q (Q ()) E s⟩
  wp_trans_monotone _ _ _ _ _ hE hQ := fun s h =>
    Executable.wp_mono (fun s' => hQ () s') hE h

/-- Unfold a triple's wp into the machine-founded transformer. -/
theorem wp_eq [CodeEnv] (q : Program) (Q : Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop) (s : MachineData) :
    WP.wp q Q E s = cenv.wp q (Q ()) E s := rfl

/- An immediate in a machine-founded VC is the payload of an `Int64` literal.
With `MachineWP` open, `grind`'s normalizer rewrites it to a `BitVec` literal,
so no `Int64` literal enters the E-graph: one there, among register reads, has
been seen to exhaust `grind`'s recursion depth. The rules are scoped because
the separation-logic proofs (`SepAluMem`, `SepDynamicStack`) need immediates
in their `Int64` form. -/
attribute [scoped grind norm] Int64.toBitVec_ofNat_norm Int64.toBitVec_neg_ofNat_norm

/- A jump exit of `MachineWP.cfg` asks where its target sits in the list of
labels of the program, `["start", ".loop", …]`. With `MachineWP` open,
`grind`'s normalizer answers by evaluation. -/
attribute [scoped grind norm] List.idxOf_cons List.contains_cons

end MachineWP

/-! ## The rule set

One `@[spec]` triple per instruction shape, in composite form: the
precondition is the tail's wp at the record update the instruction performs,
a jump's precondition is `E` at the target's address. Proofs unfold one cell
of the interpreter and advance the placement. -/

/-- A load at the address a store wrote reads the stored value back. -/
@[grind =] theorem Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a Width.W64.bytes v).loadInt a Width.W64.bytes
      = some (Int.ofBytes (Int.toBytes Width.W64.bytes v)) :=
  Mem.loadInt_storeInt m a _ v (by decide)

/-- Reading back a pushed address: the bytes a store wrote decode to it. -/
@[grind =] theorem Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt Width.W64.bits
        (Int.ofBytes (Int.toBytes Width.W64.bytes ra.toBitVec.toInt))) = ra := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

/-- A push leaves on the stack the address it pushed. -/
@[grind =] theorem MachineData.retAddr_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).retAddr = some ra := by
  have hbound : Width.W64.bytes ≤ 2 ^ 64 := by decide
  simp only [MachineData.retAddr, MachineData.pushRa, Reg64s.get64_set64, reduceIte,
    Mem.loadInt_storeInt _ _ _ _ hbound, Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

/-- The address a `(base,index,1)` operand computes, at 64-bit address size:
the base register plus the index register. -/
theorem AddrExpr.zeroExtend_interp_sib1 [Labels] (b i : Reg64) (regs : Reg64s)
    (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned]
  show BitVec.ofInt 64 _ = _
  simp [Width.bytes, BitVec.ofInt_add, BitVec.ofInt_toInt]

/-- The address a `(base,index,scale)` operand computes, at 64-bit address
size: the base register plus the index register times the scale. -/
theorem AddrExpr.zeroExtend_interp_sib_scale [Labels] (b i : Reg64) (c : Width) (regs : Reg64s)
    (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, c⟩, .int64 0⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i * BitVec.ofNat 64 c.bytes := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned]
  show BitVec.ofInt 64 _ = _
  simp [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]

/-- The address a `disp(base,index,1)` operand computes, at 64-bit address
size: the base register plus the index register plus the displacement. The
parser writes `(base,index,1)` with the displacement `0`. -/
theorem AddrExpr.zeroExtend_interp_sib1_disp [Labels] (b i : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + regs.get64 i + d.toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake, htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, hsigned]
  show BitVec.ofInt 64 _ = _
  simp [Width.bytes, BitVec.ofInt_add, BitVec.ofInt_toInt]

/-- The address a `disp(base)` expression computes, at 64-bit address size:
the base register plus the displacement. -/
theorem AddrExpr.zeroExtend_interp_base_disp [L : Labels] (b : Reg64) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some (.reg b), none, .int64 d⟩) regs rng).zeroExtend 64)
      = regs.get64 b + BitVec.ofInt 64 d.toInt := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get64]
  have htake : ∀ x : BitVec 64, x.take Width.W64.bits = x := by
    intro x
    simp [BitVec.take, BitVec.extractLsb']
  rw [htake]
  have hsigned : ∀ x : BitVec 64, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, Int.add_zero,
    show ∀ y : BitVec Width.W64.bits, BitVec.zeroExtend 64 y = y from fun _ => rfl,
    BitVec.ofInt_add, BitVec.ofInt_toInt]

/-- The address a `sym(%rip)` operand computes: the symbol's. The assembler's
displacement is the symbol minus the address behind the instruction, which is
where `%rip` points. -/
theorem AddrExpr.zeroExtend_interp_rip_label [Labels] (l : Label) (regs : Reg64s)
    (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩) regs rng).zeroExtend 64)
      = (label l).toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp]
  show BitVec.ofInt 64 _ = _
  rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt_int64, BitVec.ofInt_toInt_int64,
    Int64.toBitVec_sub, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The address a `d(%rip)` operand with a numeric displacement computes: the
address behind the instruction plus `d`. Unlike `sym(%rip)`, this depends on
where the instruction sits. -/
theorem AddrExpr.zeroExtend_interp_rip_disp [Labels] (d : Int64) (regs : Reg64s)
    (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W64)
        (a := ⟨some .rip, none, .int64 d⟩) regs rng).zeroExtend 64)
      = rng.upper.toBitVec + d.toBitVec := by
  simp only [AddrExpr.interp, ConstExpr.interp]
  show BitVec.ofInt 64 _ = _
  rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt_int64, BitVec.ofInt_toInt_int64]

/-- The address a `disp(,index,scale)` operand computes at 32-bit address size
(the `0x67` prefix), zero-extended: the low half of the index register times
the scale, plus the displacement, wrapped to 32 bits. -/
theorem AddrExpr.zeroExtend_interp_index32_disp [Labels] (i : Reg64) (c : Width) (d : Int64)
    (regs : Reg64s) (rng : Std.Rco Int64) :
    ((AddrExpr.interp (address_size := .mk .W32)
        (a := ⟨none, some ⟨i, c⟩, .int64 d⟩) regs rng).zeroExtend 64)
      = (regs.get (.low i .W32) * BitVec.ofNat 32 c.bytes
          + d.toBitVec.setWidth 32).zeroExtend 64 := by
  simp only [AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, Reg64s.get_low32]
  congr 1
  have htake : (regs.get64 i).take Width.W32.bits = (regs.get64 i).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
  rw [htake]
  have hsigned : ∀ x : BitVec 32, x.signed = x.toInt := fun _ => rfl
  rw [hsigned, Int.zero_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    BitVec.ofInt_natCast, show d.toInt = d.toBitVec.toInt from rfl,
    ← BitVec.signExtend, BitVec.signExtend_eq_setWidth_of_le _ (by decide)]

section Specs

open MachineWP

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

/-- Unfold the fall-through address past one instruction cell. -/
theorem MachineWP.after_instr {i : Instr} {q : Program} {pc : Int64} {z : Nat}
    {rest : List (Directive × Nat)}
    (hcode : cenv.codeAt pc = (Directive.instr i, z) :: rest) :
    cenv.after pc (Directive.instr i :: q) = cenv.after (pc + .ofNat z) q := by
  simp only [Executable.after, hcode]

/-- Run one cell and continue: the rule pattern shared by every
instruction. -/
theorem MachineWP.step_here {post : @Post MachineState} {s : MachineData} {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hseg : cenv.codeAt pc = (d, z) :: rest)
    (hall : cenv.stepAt d z (s, pc) (fun st => Eventually cenv.instrStep post st)) :
    Eventually cenv.instrStep post (s, pc) :=
  step_cps _ _ _ ⟨d, z, rest, hseg, hall⟩

/-- The rule of a cell that runs and falls through: its interpretation stops
at the state the cell computes, so the tail's wp there is the cell's
precondition. Each entry of the dictionary below is this rule at one
instruction, with the reduction of its interpretation as the only content. -/
theorem MachineWP.fallthrough_spec {i : Instr} {f : MachineData → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      P (f s, 0) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => WP.wp p Q E (f s) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ (h _ hpl')))

/-- The rule of a cell whose fall-through leaves a value unspecified: the
tail's wp must hold whatever the machine picks. -/
theorem MachineWP.fallthrough_nondet_spec {α : Type} [NondetSupportingType α] {i : Instr}
    {f : MachineData → α → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop),
      (∀ v : α, P (f s v, 0)) → (@Directive.interp (_root_.Executable.labels cenv) (Directive.instr i) s rng
        (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => ∀ v : α, WP.wp p Q E (f s v) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ (fun v => h v _ hpl')))

@[spec] theorem MachineWP.nil_spec :
    ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc _
    exact Eventually.done _ (Or.inl ⟨rfl, h⟩)

/-- A label costs no step and no address. -/
@[spec] theorem MachineWP.label_spec (l : Label) :
    ⦃ fun s => WP.wp p Q E s ⦄ (Directive.label l :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => h

@[spec] theorem MachineWP.nop_spec (asz osz : Width) (n : Nat) :
    ⦃ fun s => WP.wp p Q E s ⦄
      (Directive.instr (.regular asz osz (.nop n)) :: p) ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.mov_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `mov $l₁-l₂, %r` : a difference of labels, which the assembler folds to a
constant; it does not depend on where the instruction sits. -/
@[spec] theorem MachineWP.mov_reg_imm_label_sub_spec (asz : Width) (r : Reg64) (l₁ l₂ : Label) :
    ⦃ fun s =>
        let v := (_root_.Executable.labels cenv).label l₁ - (_root_.Executable.labels cenv).label l₂
        WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.setWidth 64 v.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64
          (.mov (.reg (.low r .W64)) (.imm (.sub (.label l₁) (.label l₂))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.mov_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 rd (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64
          (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.sub_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 i.toBitVec
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `sub $l₁-l₂, %r` : the label difference is a constant, as for `mov`. -/
@[spec] theorem MachineWP.sub_reg_imm_label_sub_spec (asz : Width) (r : Reg64) (l₁ l₂ : Label) :
    ⦃ fun s =>
        let b := s.regs.get64 r
        let a := BitVec.setWidth 64 ((_root_.Executable.labels cenv).label l₁
          - (_root_.Executable.labels cenv).label l₂).toBitVec
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.sub (.reg (.low r .W64)) (.imm (.sub (.label l₁) (.label l₂))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `test %rb, %ra` : the flags of the conjunction, with `af` left arbitrary;
no register changes. -/
@[spec] theorem MachineWP.test_reg_reg_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let v := s.regs.get64 ra &&& s.regs.get64 rb
        ∀ af : Bool,
          WP.wp p Q E
            { s with status := StatusFlags.from_result v { cf := false, af, of := false } } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by wp_step; exact hP)

/-- `dec %r` : the register less one; the carry flag is kept. -/
@[spec] theorem MachineWP.dec_reg_spec (asz : Width) (r : Reg64) :
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
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.add_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        let b := s.regs.get64 r
        let v := a + b
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
                  of := v.signed != a.signed + b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.adc_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rs
        let b := s.regs.get64 rd
        let c := s.status.cf
        let v := a + b + BitVec.ofNat 64 c.toNat
        WP.wp p Q E
          { s with
              regs := s.regs.set64 rd v,
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned + b.unsigned + c,
                  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + c,
                  of := v.signed != a.signed + b.signed + c } } ⦄
      (Directive.instr (.regular asz .W64
          (.adc (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.mulx_reg_spec (asz : Width) (hi lo rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rs).unsigned * (s.regs.get64 .rdx).unsigned
        WP.wp p Q E
          { s with regs :=
              (s.regs.set64 lo (BitVec.ofInt 64 v)).set64 hi (BitVec.ofInt 64 (v >>> 64)) } ⦄
      (Directive.instr (.regular asz .W64
          (.mulx (.low hi .W64) (.low lo .W64) (.reg (.low rs .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.xor_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 rd
        let b := s.regs.get64 rs
        let v := a ^^^ b
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 rd v,
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64
          (.xor (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by wp_step; exact hP)

/-- `and $i, %r` : the register gets its conjunction with the immediate, and the
flags are those of the result, with `af` left arbitrary. -/
@[spec] theorem MachineWP.and_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := s.regs.get64 r &&& BitVec.setWidth 64 i.toBitVec
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 r v,
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W64 (.and (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### Register arithmetic and SSE

`shl` leaves its flags partly undefined, so its rule quantifies over the
flags; the rule covers nonzero counts only, the side condition vcgen emits. The
packed-float rules carry the lane arithmetic as the value written. -/

@[spec] theorem MachineWP.add_reg_reg_spec (asz : Width) (rd rs : Reg64) :
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
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.neg_reg_spec (asz : Width) (r : Reg64) :
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
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `shl $i, %r32` for a nonzero masked count: the 32-bit result is
zero-extended into `r`, and the flags are left arbitrary. The count is the
immediate masked to five bits, spelled so that ground evaluation reduces it to
a literal. -/
@[spec] theorem MachineWP.shl_reg32_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a : BitVec 32 := s.regs.get (.low r .W32)
        let n := i.toBitVec.toNat % 32
        (n ≠ 0) ⊓ (∀ st : StatusFlags, WP.wp p Q E
          { s with regs := s.regs.set64 r ((a <<< n).zeroExtend 64), status := st }) ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [meet_prop_eq_and] at h
    obtain ⟨hz, hk⟩ := h
    have hn : ∀ (L : Labels) rng,
        @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W32
          = i.toBitVec.toNat % 32 := fun _ _ => by
      show (i.toBitVec.take 8).toNat &&& (2 ^ 5 - 1) = _
      rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
    simp only [hn, hz, beq_iff_eq, ite_false]
    repeat (first | exact hk _ _ hpl' | intro _ | split | simp only [Effects.All])

@[spec] theorem MachineWP.movaps_reg_reg_spec (xd xs : RegMm) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm xd) (s.zmms.get (.xmm xs)) } ⦄
      (Directive.instr (.avx .W64 .W128 (.movaps (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.subps_reg_reg_spec (xd xs : RegMm) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.setLegacy (.xmm xd)
        (BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d - BitVec.toFloat32 c))
          (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs)))) } ⦄
      (Directive.instr (.avx .W64 .W128 (.subps (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.addps_reg_reg_spec (xd xs : RegMm) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.setLegacy (.xmm xd)
        (BitVec.packedBinOp 32 (fun d c => Float32.toBitVec (BitVec.toFloat32 d + BitVec.toFloat32 c))
          (s.zmms.get (.xmm xd)) (s.zmms.get (.xmm xs)))) } ⦄
      (Directive.instr (.avx .W64 .W128 (.addps (.avx (.xmm xd)) (.avx (.xmm xs)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `movaps (%b,%i,1), %xmm` : the address must be 16-byte aligned and the 16
bytes there readable; the tail runs with the loaded value in the register. -/
@[spec] theorem MachineWP.movaps_load_sib1_spec (x : RegMm) (b i : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1, hal, hv, AvxWidth.bytes,
      Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `movaps %xmm, (%b,%i,1)` : the address must be 16-byte aligned and the 16
bytes there owned (readable); the tail runs on the updated memory. -/
@[spec] theorem MachineWP.movaps_store_sib1_spec (x : RegMm) (b i : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get (.xmm x)).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 0⟩) (.avx (.xmm x)))) :: p)
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
    simp only [MachineData.storeAvx, AddrExpr.zeroExtend_interp_sib1, hal, hv, AvxWidth.bytes,
      Bool.not_true, Bool.and_false]
    exact hk _ hpl'

/-! ### Displacement and rip-relative operands

The operand shapes of compiled SSE code: a base register plus a constant
displacement, and a symbol addressed relative to `%rip`. A load or store at a
displacement has the side conditions of the `sib1` rules, at the address the
operand computes; a rip-relative operand reads the data at a label of the
program. -/

/-- `lea d(%b), %r` : the register gets the base plus the displacement. -/
@[spec] theorem MachineWP.lea_base_disp_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := s.regs.set64 r (s.regs.get64 b + d.toBitVec) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64) ⟨some (.reg b), none, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [AddrExpr.zeroExtend_interp_base_disp, BitVec.ofInt_toInt_int64]
    exact hP)

/-- `leaq sym(%rip), %r` : the register gets the symbol's address, wherever the
instruction sits. -/
@[spec] theorem MachineWP.lea_rip_label_spec (r : Reg64) (l : Label) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.set64 r ((_root_.Executable.labels cenv).label l).toBitVec } ⦄
      (Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64) ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [AddrExpr.zeroExtend_interp_rip_label]
    exact hP)

/-- `lea d(,%i32,s), %r` : a 32-bit address without a base register. The
register gets the low half of the index times the scale, plus the displacement,
wrapped to 32 bits and zero-extended; the upper half of the index is ignored. -/
@[spec] theorem MachineWP.lea_index32_disp_spec (r i : Reg64) (c : Width) (d : Int64) :
    ⦃ fun s => WP.wp p Q E { s with regs := (s.regs.set64 r
        ((s.regs.get (.low i .W32) * BitVec.ofNat 32 c.bytes
          + d.toBitVec.setWidth 32).zeroExtend 64)) } ⦄
      (Directive.instr (.regular .W32 .W64
          (.lea (.low r .W64) ⟨none, some ⟨i, c⟩, .int64 d⟩)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step
    simp only [AddrExpr.zeroExtend_interp_index32_disp]
    exact hP)

/-- `cmp %rb, %ra` : the flags of `ra - rb`; no register changes. -/
@[spec] theorem MachineWP.cmp_reg_reg_spec (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 ra
        let b := s.regs.get64 rb
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                  of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `cmp $i, %r` : the flags of `r - i`; no register changes. -/
@[spec] theorem MachineWP.cmp_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let b := BitVec.setWidth 64 i.toBitVec
        let v := a - b
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - b.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,
                  of := v.signed != a.signed - b.signed } } ⦄
      (Directive.instr (.regular asz .W64 (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-! ### The stack and sub-registers

The forms a compiler's frame code uses: `push`/`pop` of a 64-bit register,
32- and 8-bit moves between a sub-register (or an immediate) and `d(%b)`, a
32-bit compare of memory with an immediate, and 32- and 8-bit `sub`/`and` on a
sub-register. A 32-bit write zero-extends into the register
(`Reg64s.set_low32`); an 8-bit write keeps the upper bytes
(`Reg64s.set_low8`). A load needs its bytes readable; a store needs them
owned (readable), as the SSE rules do. -/

/-- `push %r` : the slot below the stack pointer must be owned; the tail runs
with the register's value there and the stack pointer lowered. -/
@[spec] theorem MachineWP.push_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 .rsp - Width.W64.bytesv
        ((Mem.loadInt s.dmem a Width.W64.bytes).isSome = true)
          ⊓ WP.wp p Q E { s with
              regs := s.regs.set64 .rsp a,
              dmem := Mem.storeInt s.dmem a Width.W64.bytes (s.regs.get64 r).toInt } ⦄
      (Directive.instr (.regular asz .W64 (.push (.regOrMem (.reg (.low r .W64))))) :: p)
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
    simp only [MachineData.store, hv, Effects.All]
    exact hk _ hpl'

/-- `pop %r` : the stack top must be readable; the tail runs with its value in
the register and the stack pointer raised. -/
@[spec] theorem MachineWP.pop_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 .rsp
        ((Mem.loadInt s.dmem a Width.W64.bytes).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a Width.W64.bytes = some v →
            WP.wp p Q E { s with
              regs := (s.regs.set64 .rsp (a + Width.W64.bytesv)).set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular asz .W64 (.pop (.reg (.low r .W64)))) :: p)
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
    simp only [MachineData.load, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `movl %r32, d(%b)` : the 4 bytes must be owned; the tail runs on the
updated memory. -/
@[spec] theorem MachineWP.mov32_store_base_disp_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 4 ((s.regs.get64 r).setWidth 32).toInt } ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W32))))) :: p)
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
    simp only [MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Reg64s.get_low32, Width.bytes, hv, Effects.All]
    exact hk _ hpl'

/-- `movq %r, d(%b)` : the 8 bytes must be owned; the tail runs on the updated
memory. -/
@[spec] theorem MachineWP.mov_store_base_disp_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 r).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W64))))) :: p)
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
    simp only [MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Reg64s.get_low64, Width.bytes, hv, Effects.All]
    exact hk _ hpl'

/-- `movl d(%b), %r32` : the 4 bytes must be readable; the tail runs with them
zero-extended in the register. -/
@[spec] theorem MachineWP.mov32_load_base_disp_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with
              regs := s.regs.set64 r ((BitVec.ofInt 32 v).setWidth 64) }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.mov (.reg (.low r .W32)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
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
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Reg64s.set_low32, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `cmpl $i, d(%b)` : the 4 bytes must be readable; the flags are those of
their 32-bit difference with the immediate. -/
@[spec] theorem MachineWP.cmp32_mem_imm_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let addr := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem addr 4).isSome = true)
          ⊓ (∀ m, Mem.loadInt s.dmem addr 4 = some m →
            let a := BitVec.ofInt 32 m
            let c := i.toBitVec.truncate 32
            let v := a - c
            WP.wp p Q E { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - c.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (c.take 4).unsigned,
                  of := v.signed != a.signed - c.signed } }) ⦄
      (Directive.instr (.regular .W64 .W32
          (.cmp (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p)
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
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `movb $i, d(%b)` : the byte must be owned; the tail runs on the updated
memory. -/
@[spec] theorem MachineWP.mov8_store_imm_base_disp_spec (b : Reg64) (d i : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 1).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 1 (i.toBitVec.truncate 8).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.imm (.int64 i)))) :: p)
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
    simp only [MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Width.bytes, hv, Effects.All]
    exact hk _ hpl'

/-- `movb %r8, d(%b)` : the byte must be owned; the tail runs on the updated
memory. -/
@[spec] theorem MachineWP.mov8_store_reg_base_disp_spec (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 1).isSome = true)
          ⊓ WP.wp p Q E { s with
              dmem := Mem.storeInt s.dmem a 1 ((s.regs.get64 r).setWidth 8).toInt } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))) :: p)
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
    simp only [MachineData.store, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Reg64s.get_low8, Width.bytes, hv, Effects.All]
    exact hk _ hpl'

/-- `movb d(%b), %r8` : the byte must be readable; the tail runs with it as
the register's low byte. -/
@[spec] theorem MachineWP.mov8_load_base_disp_spec (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 1).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 1 = some v →
            WP.wp p Q E { s with
              regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (BitVec.ofInt 8 v)) }) ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))) :: p)
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
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Reg64s.set_low8, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `subl $i, %r32` : the 32-bit difference, zero-extended into the register,
and its flags. -/
@[spec] theorem MachineWP.sub32_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let b := (s.regs.get64 r).setWidth 32
        let a := i.toBitVec.truncate 32
        let v := b - a
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r (v.setWidth 64),
              status := StatusFlags.from_result v
                { cf := v.unsigned != b.unsigned - a.unsigned,
                  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,
                  of := v.signed != b.signed - a.signed } } ⦄
      (Directive.instr (.regular asz .W32 (.sub (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low32, Reg64s.set_low32]; exact hP)

/-- `cmpl $i, %r32` : the flags of the 32-bit difference; no register changes. -/
@[spec] theorem MachineWP.cmp32_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let c := i.toBitVec.truncate 32
        let v := a - c
        WP.wp p Q E
          { s with
              status := StatusFlags.from_result v
                { cf := v.unsigned != a.unsigned - c.unsigned,
                  af := (v.take 4).unsigned != (a.take 4).unsigned - (c.take 4).unsigned,
                  of := v.signed != a.signed - c.signed } } ⦄
      (Directive.instr (.regular asz .W32 (.cmp (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low32]; exact hP)

/-- `movl %rs32, %rd32` : the low half, zero-extended into the register. -/
@[spec] theorem MachineWP.mov32_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.set64 rd (((s.regs.get64 rs).setWidth 32).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32
          (.mov (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low32, Reg64s.set_low32]; exact hP)

/-- `movl $i, %r32` : the immediate's low half, zero-extended into the register. -/
@[spec] theorem MachineWP.mov32_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.set64 r ((i.toBitVec.truncate 32).setWidth 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.set_low32]; exact hP)

/-- `xorl %rs32, %rd32` : the 32-bit exclusive or, zero-extended into the
register, and its flags, with `af` left arbitrary. -/
@[spec] theorem MachineWP.xor32_reg_reg_spec (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).setWidth 32 ^^^ (s.regs.get64 rs).setWidth 32
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 rd (v.setWidth 64),
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W32
          (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low32, Reg64s.set_low32]; exact hP)

/-- `movslq (%b,%i,s), %r` (`movsxd`) : the 4 bytes must be readable; the tail
runs with them sign-extended in the register. A jump table's entry load. -/
@[spec] theorem MachineWP.movsxd_load_sib_spec (r b i : Reg64) (c : Width) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * BitVec.ofNat 64 c.bytes
        ((Mem.loadInt s.dmem a 4).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 4 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r ((BitVec.ofInt 32 v).signExtend 64) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.movsx (w' := .W32) (.reg (.low r .W64))
            (.mem ⟨some (.reg b), some ⟨i, c⟩, .int64 0⟩))) :: p)
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
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_sib_scale, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

/-- `andb $i, %r8` : the low byte gets its conjunction with the immediate, the
rest of the register stays, and the flags are those of the byte, with `af`
left arbitrary. -/
@[spec] theorem MachineWP.and8_reg_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let v := (s.regs.get64 r).setWidth 8 &&& i.toBitVec.truncate 8
        ∀ af : Bool,
          WP.wp p Q E
            { s with
                regs := s.regs.set64 r ((s.regs.get64 r).replaceLow v),
                status := StatusFlags.from_result v { cf := false, of := false, af } } ⦄
      (Directive.instr (.regular asz .W8 (.and (.reg (.low r .W8)) (.imm (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_nondet_spec (fun s rng P hP => by
    wp_step; simp only [Reg64s.get_low8, Reg64s.set_low8]; exact hP)

/-- `movaps d(%b), %xmm` : the address must be 16-byte aligned and the 16 bytes
there readable; the tail runs with the loaded value in the register. -/
@[spec] theorem MachineWP.movaps_load_base_disp_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, hal, hv, AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `movaps %xmm, d(%b)` : the address must be 16-byte aligned and the 16 bytes
there owned (readable); the tail runs on the updated memory. -/
@[spec] theorem MachineWP.movaps_store_base_disp_spec (x : RegMm) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get (.xmm x)).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), none, .int64 d⟩) (.avx (.xmm x)))) :: p)
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
    simp only [MachineData.storeAvx, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, hal, hv, AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk _ hpl'

/-- `movaps d(%b,%i,1), %xmm` : the address `b + i + d` must be 16-byte aligned
and the 16 bytes there readable; the tail runs with them in the register. The
priority is low, so that the displacement-`0` form keeps `movaps_load_sib1_spec`. -/
@[spec low] theorem MachineWP.movaps_load_sib1_disp_spec (x : RegMm) (b i : Reg64)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.setLegacy (.xmm x) (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `movaps %xmm, d(%b,%i,1)` : the address `b + i + d` must be 16-byte aligned
and the 16 bytes there owned (readable); the tail runs on the updated memory.
The priority is low, as for the load. -/
@[spec low] theorem MachineWP.movaps_store_sib1_disp_spec (x : RegMm) (b i : Reg64)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get (.xmm x)).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
          (.movaps (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.avx (.xmm x)))) :: p)
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
    simp only [MachineData.storeAvx, AddrExpr.zeroExtend_interp_sib1_disp, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk _ hpl'

/-- `mulps d(%b,%i,1), %xmm` : the address `b + i + d` must be 16-byte aligned
and the 16 bytes there readable; the tail runs with `xmm * mem`, lanewise, in
the register, whose bits above 128 are kept. The parser writes `(%b,%i,1)` with
the displacement `0`, so this rule covers it too. -/
@[spec] theorem MachineWP.mulps_load_sib1_disp_spec (x : RegMm) (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.setLegacy (.xmm x)
              (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get (.xmm x)) (BitVec.ofInt 128 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.mulps (.avx (.xmm x)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `xorps sym(%rip), %xmm` : the 16 bytes at the label `sym` must be 16-byte
aligned and readable; the tail runs with them xored into the register. -/
@[spec] theorem MachineWP.xorps_load_rip_spec (x : RegMm) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with
              zmms := s.zmms.setLegacy (.xmm x) (s.zmms.get (.xmm x) ^^^ BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.xorps (.avx (.xmm x))
            (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_rip_label, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-! ### VEX-encoded AVX

A VEX write to a register clears the bits above the operation width, which is
what `RegZmms.set` does. Of the memory operands, only `vmovaps` checks
alignment. The memory rules take the `disp(%b,%i,1)` shape; the parser writes
`(%b,%i,1)` as the displacement `0`, so the same rules cover it. -/

@[spec] theorem MachineWP.vxorps_reg_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg w) :
    ⦃ fun s => WP.wp p Q E
        { s with zmms := s.zmms.set dst (s.zmms.get src1 ^^^ s.zmms.get src2) } ⦄
      (Directive.instr (.avx asz w (.vxorps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vaddps_reg_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg w) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 32 BitVec.f32add (s.zmms.get src1) (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vaddps dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vshufps_reg_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg w) (imm : UInt8) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 128 (BitVec.shufps128 imm) (s.zmms.get src1) (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vshufps dst src1 (.avx src2) imm)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vextractf128_spec {w : AvxWidth} (asz : Width)
    (dst : AvxReg .W128) (src : AvxReg .W256) (imm : UInt8) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        ((s.zmms.get src).extractLsb' (128 * (imm.toNat % 2)) 128)) } ⦄
      (Directive.instr (.avx asz w (.vextractf128 dst src imm)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vmovhlps_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 64 64 ++ (s.zmms.get src2).extractLsb' 64 64)) } ⦄
      (Directive.instr (.avx asz w (.vmovhlps dst src1 src2)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vmovss_reg_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 32 96 ++ (s.zmms.get src2).extractLsb' 0 32)) } ⦄
      (Directive.instr (.avx asz w (.vmovss dst src1 src2)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vaddss_spec {w : AvxWidth} (asz : Width)
    (dst src1 src2 : AvxReg .W128) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        ((s.zmms.get src1).extractLsb' 32 96
          ++ BitVec.f32add ((s.zmms.get src1).extractLsb' 0 32)
            ((s.zmms.get src2).extractLsb' 0 32))) } ⦄
      (Directive.instr (.avx asz w (.vaddss dst src1 src2)) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

@[spec] theorem MachineWP.vzeroupper_spec {w : AvxWidth} (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := s.zmms.zeroUpper } ⦄
      (Directive.instr (.avx asz w .vzeroupper) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by wp_step; exact hP)

/-- `vmovups d(%b,%i,1), %ymm` : the 32 bytes at the address must be readable,
at any alignment; the tail runs with them in the register. -/
@[spec] theorem MachineWP.vmovups_load_sib1_disp_spec (y : AvxReg .W256) (b i : Reg64)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256
          (.vmovups (.avx y) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hv, AvxWidth.bytes,
      Bool.false_and, Bool.false_eq_true, ite_false]
    exact hk v hv _ hpl'

/-- `vfmadd231ps d(%b,%i,1), %ymm1, %ymm0` : the 32 bytes at the address must
be readable, at any alignment; the tail runs with `ymm0 + ymm1 * mem`, each lane
rounded once, in `ymm0`. -/
@[spec] theorem MachineWP.vfmadd231ps_load_sib1_disp_spec (dst src1 : AvxReg .W256)
    (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              (BitVec.packedTernOp 32 BitVec.f32fma (s.zmms.get src1) (BitVec.ofInt 256 v)
                (s.zmms.get dst))) }) ⦄
      (Directive.instr (.avx .W64 .W256
          (.vfmadd231ps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hv, AvxWidth.bytes,
      Bool.false_and, Bool.false_eq_true, ite_false]
    exact hk v hv _ hpl'

/-- `vmovaps d(%b,%i,1), %xmm` : the address must be 16-byte aligned and the 16
bytes there readable; the tail runs with them in the register. -/
@[spec] theorem MachineWP.vmovaps_load_sib1_disp_spec (x : AvxReg .W128) (b i : Reg64)
    (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        (isAligned 16 a = true) ⊓ ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmovaps (.avx x) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hal, hv,
      AvxWidth.bytes, Bool.not_true, Bool.and_false]
    exact hk v hv _ hpl'

/-- `vmulps d(%b,%i,1), %xmm1, %xmm0` : the 16 bytes at the address must be
readable, at any alignment; the tail runs with `xmm1 * mem` in `xmm0`. -/
@[spec] theorem MachineWP.vmulps_load_sib1_disp_spec (dst src1 : AvxReg .W128)
    (b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := (s.zmms.set dst
              (BitVec.packedBinOp 32 BitVec.f32mul (s.zmms.get src1) (BitVec.ofInt 128 v))) }) ⦄
      (Directive.instr (.avx .W64 .W128
          (.vmulps dst src1 (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))) :: p)
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
    simp only [MachineData.loadAvx, AddrExpr.zeroExtend_interp_sib1_disp, hv, AvxWidth.bytes,
      Bool.false_and, Bool.false_eq_true, ite_false]
    exact hk v hv _ hpl'

/-- A data cell does not run: the machine faults on reaching it. Its rule asks
that control never get there, which a table entry of `False` provides. -/
@[spec] theorem MachineWP.byteArray_spec (a : ByteArray) :
    ⦃ fun _ => False ⦄ (Directive.byteArray a :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => False.elim h

@[spec] theorem MachineWP.jmp_label_spec (asz osz : Width) (l : Label) :
    ⦃ fun s => E ((_root_.Executable.labels cenv).label l) s ⦄
      (Directive.instr (.regular asz osz
          (.jmp (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    refine step_here hseg ?_
    wp_step
    have hcancel : pc + .ofNat z + ((_root_.Executable.labels cenv).label l - (pc + .ofNat z))
        = (_root_.Executable.labels cenv).label l := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp only [hcancel]
    exact Eventually.done _ (Or.inr h)

/-! ### Computed jumps and reading the pc

A jump through a register exits at the register's value: the exit channel is
pc-valued, so a computed target needs no new machinery, and the rule is
position-independent like every other. Where control lands is the table's
business (`Table.ofLabels` asks that the value be some label's address).

Reading the pc is different. `d(%rip)` with a numeric `d` computes the
address behind the instruction plus `d`, which depends on where the fragment
sits, and `Executable.wp` quantifies over every placement: no
position-independent precondition can name the value. (`sym(%rip)` is fine:
the assembler's displacement cancels the pc.) Its rule is therefore stated at
a known address, in `Eventually` form, and a proof that reads the pc steps
that block by hand at its label's address; `Triple.run_at` reads the other
blocks' triples at their addresses. -/

/-- `jmp %r` : a computed jump, to the address the register holds. -/
@[spec] theorem MachineWP.jmp_reg_spec (asz osz : Width) (r : Reg64) :
    ⦃ fun s => E (Int64.ofBitVec (s.regs.get64 r)) s ⦄
      (Directive.instr (.regular asz osz (.jmp (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_here hseg ?_
    wp_step
    exact Eventually.done _ (Or.inr h)

/-- `jmp *d(%b)` : an indirect jump, to the address stored at `b + d`. The 8
bytes must be readable. -/
@[spec] theorem MachineWP.jmp_mem_base_disp_spec (osz : Width) (b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + d.toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
              E (Int64.ofBitVec (BitVec.ofInt 64 v)) s) ⦄
      (Directive.instr (.regular .W64 osz (.jmp (.mem ⟨some (.reg b), none, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, -⟩ := hpl
    refine step_here hseg ?_
    wp_step
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_base_disp,
      BitVec.ofInt_toInt_int64, Width.bytes, hv, Effects.All]
    exact Or.inr (Eventually.done _ (Or.inr (hk v hv)))

/-- `lea d(%rip), %r` at the address `pc`: the register gets the address behind
the instruction plus `d`, and the run continues there. -/
theorem MachineWP.lea_rip_disp_run (r : Reg64) (d : Int64) {pc : Int64} {s : MachineData}
    {post : @Post MachineState}
    (hs : cenv.sits pc
      [Directive.instr (.regular .W64 .W64 (.lea (.low r .W64) ⟨some .rip, none, .int64 d⟩))])
    (hk : Eventually cenv.instrStep post
      ({ s with regs := s.regs.set64 r ((cenv.after pc
          [Directive.instr (.regular .W64 .W64
            (.lea (.low r .W64) ⟨some .rip, none, .int64 d⟩))]).toBitVec + d.toBitVec) },
        cenv.after pc
          [Directive.instr (.regular .W64 .W64
            (.lea (.low r .W64) ⟨some .rip, none, .int64 d⟩))])) :
    Eventually cenv.instrStep post (s, pc) := by
  obtain ⟨z, rest, hseg, -⟩ := hs
  simp only [Executable.after, hseg] at hk
  refine step_here hseg (Or.inl ?_)
  wp_step
  simp only [AddrExpr.zeroExtend_interp_rip_disp]
  exact hk

/-- A fragment's triple, read at an address where it sits. -/
theorem MachineWP.Triple.run_at {q : Program} {P : MachineData → Prop}
    {Q' : Unit → MachineData → Prop} {E' : Int64 → MachineData → Prop}
    (h : ⦃ P ⦄ q ⦃ Q'; E' ⦄) {pc : Int64} {s : MachineData}
    (hs : cenv.sits pc q) (hp : P s) :
    Eventually cenv.instrStep
      (fun st => (st.2 = cenv.after pc q ∧ Q' () st.1) ∨ E' st.2 st.1) (s, pc) :=
  h.le_wp s hp pc hs

/-- A return jumps to the address the stack holds. -/
@[spec] theorem MachineWP.ret_spec (asz osz : Width) :
    ⦃ fun s =>
        (s.retAddr.isSome = true)
          ⊓ (∀ ra : Int64, s.retAddr = some ra →
              E ra { s with
                  regs := s.regs.set64 .rsp (s.regs.get64 .rsp + Width.W64.bytesv) }) ⦄
      (Directive.instr (.regular asz osz .ret) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  simp only [meet_prop_eq_and] at h
  obtain ⟨hmapped, hE⟩ := h
  obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp hmapped
  obtain ⟨i, hi, hval⟩ : ∃ i, Mem.loadInt s.dmem (s.regs.get64 .rsp) Width.W64.bytes = some i
      ∧ Int64.ofBitVec (BitVec.ofInt Width.W64.bits i) = ra := by
    unfold MachineData.retAddr at hra
    cases hl : Mem.loadInt s.dmem (s.regs.get64 .rsp) Width.W64.bytes with
    | none => rw [hl] at hra; exact absurd hra (by simp)
    | some i => exact ⟨i, rfl, by rw [hl] at hra; simpa using hra⟩
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hi,
    Effects.All, hval]
  exact Eventually.done _ (Or.inr (hE ra hra))

/-- One call, with the callee's run as its premise. `P ra` is the callee's
assertion at its entry, for a run that returns to `ra`, so a caller pins the
return address inside its own choice of `P`. The conclusion rolls `P` back over
the push, quantified over the address the machine pushes, and the callee's exit
at that address continues the caller's wp of the cells behind the call. An exit
anywhere else is the caller's own. -/
theorem MachineWP.call_spec {P : Int64 → MachineData → Prop} (asz osz : Width) (l : Label)
    (body : Program) (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ ra : Int64,
      ⦃ P ra ⦄
        body
      ⦃ (fun _ _ => False);
        fun a s' => if a = ra then WP.wp p Q E s' else E a s' ⦄) :
    ⦃ fun s => (∀ ra : Int64, P ra (s.pushRa ra))
        ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes).isSome = true ⦄
      (Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  obtain ⟨hP, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  have hrun := (hbody (pc + Int64.ofNat z)).le_wp (s.pushRa (pc + Int64.ofNat z))
    (hP (pc + Int64.ofNat z))
  rw [MachineWP.wp_eq] at hrun
  refine eventually_trans _ _ _ _ (hrun ((_root_.Executable.labels cenv).label l) hplace) ?_
  rintro ⟨s', a⟩ (⟨-, hbot⟩ | hexit)
  · exact hbot.elim
  · dsimp only at hexit
    by_cases ha : a = pc + Int64.ofNat z
    · rw [if_pos ha] at hexit
      rw [after_instr hseg]
      subst ha
      exact hexit _ hpl'
    · rw [if_neg ha] at hexit
      exact Eventually.done _ (Or.inr hexit)

/-- The spec of a procedure at a label, in the form `vcgen` steps a call with.
`Pre` is what the procedure needs of the caller's state and `Post` relates that
state to the one the caller resumes in, so neither mentions the return address.
The tail and the channels stay open: one `have` per procedure serves every call
site. -/
theorem MachineWP.fun_spec_from_label {Pre : MachineData → Prop}
    {Post : MachineData → MachineData → Prop} {l : Label} {body : Program}
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label l) body)
    (hbody : ∀ (ra : Int64) (s : MachineData),
      ⦃ fun t => t = s.pushRa ra ∧ Pre s ⦄
        body
      ⦃ (fun _ _ => False); fun a s' => a = ra ∧ Post s s' ⦄) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s => (Pre s)
          ⊓ ((Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
              Width.W64.bytes).isSome = true)
          ⊓ (∀ s' : MachineData, Post s s' → WP.wp p Q E s') ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ := by
  intro asz osz p Q E
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨⟨hpre, hmapped⟩, hcont⟩ := h
  refine (MachineWP.call_spec
    (P := fun ra t => ∃ s₀ : MachineData, t = s₀.pushRa ra ∧ Pre s₀
      ∧ ∀ s' : MachineData, Post s₀ s' → WP.wp p Q E s')
    asz osz l body hplace ?_).le_wp s ⟨fun ra => ⟨s, rfl, hpre, hcont⟩, hmapped⟩
  intro ra
  refine Triple.intro fun t ht => ?_
  obtain ⟨s₀, rfl, hpre₀, hcont₀⟩ := ht
  rw [MachineWP.wp_eq]
  have hrun := (hbody ra s₀).le_wp (s₀.pushRa ra) ⟨rfl, hpre₀⟩
  rw [MachineWP.wp_eq] at hrun
  refine Executable.wp_mono (fun _ hq => hq) ?_ hrun
  rintro a s' ⟨rfl, hpost⟩
  rw [if_pos rfl]
  exact hcont₀ s' hpost

/-- Stepping a `call` through the callee's spec: the caller fixes the logical
variable `x`, and for whatever address the machine pushes, the callee's
precondition holds of the pushed state and its postcondition continues the
caller's tail. -/
theorem MachineWP.call_proc_spec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (asz osz : Width)
    (l : Label) (hproc : cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post) :
    ⦃ fun s =>
        (∀ ra : Int64, Pre x ra (s.pushRa ra)
          ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
        ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes).isSome = true ⦄
      (Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  obtain ⟨hP, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.pushRa (pc + Int64.ofNat z)) (hP _).1) ?_
  rintro ⟨s', a⟩ ⟨rfl, hpost⟩
  rw [after_instr hseg]
  exact (hP _).2 s' hpost _ hpl'

/-- `call_proc_spec` with the widths, the tail and the channels open, in the
form `vcgen [hc]` steps a call with: `have hc := call_proc_spec_at x l hproc`
at the call site, `x` the callee's logical variable for this call. -/
theorem MachineWP.call_proc_spec_at {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (l : Label)
    (hproc : cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          (∀ ra : Int64, Pre x ra (s.pushRa ra)
            ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ :=
  fun asz osz _ _ _ => MachineWP.call_proc_spec x asz osz l hproc

/-- `call_proc_spec` for the continuation form: the callee's `Spec` is asked
with the caller's tail as the continuation. -/
theorem MachineWP.call_proc_specK {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (asz osz : Width) (l : Label)
    (hproc : cenv.ProcSpecK ((_root_.Executable.labels cenv).label l) Spec) :
    ⦃ fun s =>
        (∀ ra : Int64, Spec ra (WP.wp p Q E) (s.pushRa ra))
        ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes).isSome = true ⦄
      (Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  obtain ⟨hP, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  refine eventually_trans _ _ _ _
    (hproc (pc + Int64.ofNat z) _ (s.pushRa (pc + Int64.ofNat z)) (hP _)) ?_
  rintro ⟨s', a⟩ ⟨rfl, hpost⟩
  rw [after_instr hseg]
  exact hpost _ hpl'

/-- `call_proc_specK` with the widths, the tail and the channels open, for
`vcgen [hc]` with `have hc := call_proc_specK_at l hproc` at the call site. -/
theorem MachineWP.call_proc_specK_at {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (l : Label) (hproc : cenv.ProcSpecK ((_root_.Executable.labels cenv).label l) Spec) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          (∀ ra : Int64, Spec ra (WP.wp p Q E) (s.pushRa ra))
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ :=
  fun asz osz _ _ _ => MachineWP.call_proc_specK asz osz l hproc

/-- The state `vcgen` leaves at a call site is a literal: the pushed state
`s.pushRa ra`, with registers set one by one. `grind` does not read a
register or the memory out of such a literal; this does, in every hypothesis
and the goal. Run it after a `vcgen` that stepped a `call`, `push` or `pop`,
before `grind`.

A call site with `vcgen [call_proc_spec_at x l hproc]` then reads:
```
vcgen [hc]
all_goals call_simp
all_goals try refine ⟨fun w => ⟨?_, fun s' hpost => ?_⟩, ?_⟩  -- open the rule's shape
all_goals try (vcgen; all_goals call_simp)                   -- the block after the return
all_goals grind …
```
The `refine` is the one step that is not mechanical: the rule states the
callee's precondition and the continuation under `∀ ra`, and `vcgen` does not
step into the continuation's `wp` there; the second `vcgen` does once the
quantifier is open. -/
macro "call_simp" : tactic =>
  `(tactic| try simp only [MachineData.dmem_pushRa, MachineData.get64_pushRa,
      Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at *)

@[spec] theorem MachineWP.jcc_spec (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s =>
        (cc.interp s.status = true → E ((_root_.Executable.labels cenv).label l) s)
          ⊓ (cc.interp s.status = false → WP.wp p Q E s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg ?_
    wp_step
    cases hc : CondCode.interp cc s.status <;>
      simp only [hc, Bool.false_eq_true, ite_true, ite_false, meet_prop_eq_and,
        Effects.All] at h ⊢
    · exact Or.inl (h.2 trivial _ hpl')
    · exact Or.inr (Eventually.done _ (Or.inr (h.1 trivial)))

end Specs

/-! ## Triples at an address

`Executable.wp` quantifies over every placement of a fragment, which is what
lets one triple serve wherever the fragment sits, and what rules out reading
the pc: `lea d(%rip)` yields the address behind it, which no
position-independent precondition can name. `TripleAt pc` is the judgment at
one address. Every triple gives one at each address (`TripleAt.of_triple`),
and the pc-reading rule is one (`lea_rip_disp_at`): its precondition names
`cenv.after pc [lea]`, which a proof rewrites to a label's address by the
placement fact `PlacedIn.next`. The control-flow rule takes block obligations
in this form (`cfg_reach_at`, `ProcSpec.of_cfg_at`), at each block's label. -/

namespace MachineWP

/-- The run of `q` placed at `pc`, from a state with `P`: it falls through to
the end of the placement with `Q`, or stops at a pc satisfying `E`. -/
def TripleAt [CodeEnv] (pc : Int64) (P : MachineData → Prop) (q : Program)
    (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop) : Prop :=
  ∀ s, P s → cenv.sits pc q →
    Eventually cenv.instrStep (fun st => (st.2 = cenv.after pc q ∧ Q () st.1) ∨ E st.2 st.1) (s, pc)

theorem TripleAt.of_triple [CodeEnv] {pc : Int64} {P : MachineData → Prop} {q : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (h : ⦃ P ⦄ q ⦃ Q; E ⦄) : TripleAt pc P q Q E :=
  fun s hp hs => h.le_wp s hp pc hs

theorem TripleAt.mono [CodeEnv] {pc : Int64} {P : MachineData → Prop} {q : Program}
    {Q₁ Q₂ : Unit → MachineData → Prop} {E₁ E₂ : Int64 → MachineData → Prop}
    (hQ : ∀ s, Q₁ () s → Q₂ () s) (hE : ∀ a s, E₁ a s → E₂ a s)
    (h : TripleAt pc P q Q₁ E₁) : TripleAt pc P q Q₂ E₂ :=
  fun s hp hs => eventually_weaken _ _ _ _
    (fun _ hst => hst.imp (fun ⟨ha, hq⟩ => ⟨ha, hQ _ hq⟩) (hE _ _)) (h s hp hs)

theorem TripleAt.pre [CodeEnv] {pc : Int64} {P P' : MachineData → Prop} {q : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
    (hP : ∀ s, P s → P' s) (h : TripleAt pc P' q Q E) : TripleAt pc P q Q E :=
  fun s hp hs => h s (hP s hp) hs

/-- `lea d(%rip), %r` at `pc` : the register gets the address behind the
instruction plus `d`. -/
theorem lea_rip_disp_at [CodeEnv] (r : Reg64) (d : Int64) (pc : Int64)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    TripleAt pc
      (fun s => Q () { s with regs := s.regs.set64 r ((cenv.after pc
        [Directive.instr (.regular .W64 .W64
          (.lea (.low r .W64) ⟨some .rip, none, .int64 d⟩))]).toBitVec + d.toBitVec) })
      [Directive.instr (.regular .W64 .W64 (.lea (.low r .W64) ⟨some .rip, none, .int64 d⟩))]
      Q E :=
  fun _ hq hs => lea_rip_disp_run r d hs (Eventually.done _ (Or.inl ⟨rfl, hq⟩))

end MachineWP

/-! ## The bridge to the segment judgment

`instrStep` runs one instruction; kraken's `straightlineStep` runs a whole
segment, from the pc until a jump or the end of the text. An instruction
chain therefore refines a segment chain, and the two agree when the
postcondition can hold only where the text has run out. -/

private theorem int64_add_zero (pc : Int64) : pc + Int64.ofNat 0 = pc := by simp

/-- What the bridge needs of the ambient code: a label occupies no bytes, and
behind an instruction cell the segment map continues with the cells behind
it. -/
structure Kraken.Executable.CodeWF (e : Kraken.Executable Directive) : Prop where
  label_size : ∀ c ∈ e.2, c.1.isLabel = true → c.2 = 0
  advance : ∀ pc d z rest, e.codeAt pc = (d, z) :: rest →
    e.directivesFromAddress (pc + .ofNat z) = rest

private theorem mem_takeWhile {α} {p : α → Bool} {l : List α} {a : α}
    (h : a ∈ l.takeWhile p) : p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hp : p x
    · rw [List.takeWhile_cons, if_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hp
      · exact ih h'
    · rw [List.takeWhile_cons, if_neg hp] at h
      simp at h

/-- One segment burst, as a step of the omni-judgment. -/
private theorem step_burst [_root_.Layout] {e : Kraken.Executable Directive} {post : @Post MachineState}
    {st : MachineState}
    (h : (Executable.straightline e st .done).All
      (fun m => Eventually (straightlineStep e) post m)) :
    Eventually (straightlineStep e) post st := by
  refine step_cps _ _ _ ?_
  unfold straightlineStep at h ⊢
  exact h

/-- A run of label cells at the head of a segment changes nothing. -/
private theorem interp_label_prefix [Labels] :
    ∀ (ls X : List (Directive × Nat)) (s : MachineData) (pc : Int64)
      (ret : Int64 → MachineData → Effects),
      (∀ c ∈ ls, c.1.isLabel = true ∧ c.2 = 0) →
      Directives.interp (ls ++ X) s pc ret = Directives.interp X s pc ret := by
  intro ls
  induction ls with
  | nil => intro X s pc ret _; rfl
  | cons c ls ih =>
    intro X s pc ret hls
    obtain ⟨hlab, hz⟩ := hls c List.mem_cons_self
    obtain ⟨d, z⟩ := c
    cases d with
    | label l =>
      simp only at hz
      subst hz
      simp only [List.cons_append, Directives.interp, Directive.interp, int64_add_zero]
      exact ih X s pc ret (fun c hc => hls c (List.mem_cons_of_mem _ hc))
    | instr i => simp [Directive.isLabel] at hlab
    | byteArray a => simp [Directive.isLabel] at hlab

/-- One segment, cut at its first instruction: the instruction runs, and a
fall-through continues with the segment behind it. -/
theorem Kraken.Executable.straightline_cons {e : Kraken.Executable Directive} (hwf : e.CodeWF)
    {pc : Int64} {s : MachineData} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (hcode : e.codeAt pc = (d, z) :: rest) :
    Executable.straightline e (s, pc) .done
      = @Directive.interp (_root_.Executable.labels e) d s (.mk pc (pc + .ofNat z))
          (fun s' => Executable.straightline e (s', pc + .ofNat z) .done)
          (fun pc' s' => .done (s', pc')) := by
  letI := (_root_.Executable.labels e)
  have hsplit : e.directivesFromAddress pc
      = (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel) ++ (d, z) :: rest := by
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c => c.1.isLabel)
      (l := e.directivesFromAddress pc)]
    rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)
      = (d, z) :: rest from hcode]
  have hsub : ∀ c ∈ e.directivesFromAddress pc, c ∈ e.2 := by
    intro c hc
    unfold Kraken.Executable.directivesFromAddress at hc
    have hmem : c ∈ e.withAddresses.map (·.2) :=
      List.map_subset _ (List.dropWhile_subset _) hc
    rwa [show e.withAddresses.map (·.2) = e.2 from Executable.withAddresses_map_snd e.2 e.1]
      at hmem
  have hls : ∀ c ∈ (e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel),
      c.1.isLabel = true ∧ c.2 = 0 := by
    intro c hc
    have hlab : c.1.isLabel = true :=
      mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc
    have hmem : c ∈ e.directivesFromAddress pc :=
      (List.takeWhile_sublist _).subset hc
    exact ⟨hlab, hwf.label_size c (hsub c hmem) hlab⟩
  show @Directives.interp (_root_.Executable.labels e) (e.directivesFromAddress pc) s pc
    (fun pc' s' => .done (s', pc')) = _
  rw [hsplit, interp_label_prefix _ _ _ _ _ hls]
  simp only [Directives.interp]
  congr 1
  funext s'
  show Directives.interp rest s' (pc + .ofNat z) _ = _
  rw [← hwf.advance pc d z rest hcode]
  rfl

/-- An instruction chain is a segment chain, when the postcondition can hold
only where the text has run out. -/
theorem Kraken.Executable.bridge [_root_.Layout] {e : Kraken.Executable Directive} (hwf : e.CodeWF)
    {post : @Post MachineState}
    (hbnd : ∀ st, post st → e.directivesFromAddress st.2 = []) :
    ∀ st, Eventually e.instrStep post st → Eventually (straightlineStep e) post st := by
  have key : ∀ st, Eventually e.instrStep post st →
      (Executable.straightline e st .done).All
        (fun m => Eventually (straightlineStep e) post m) := by
    intro st h
    induction h with
    | done st hp =>
      show (@Directives.interp (_root_.Executable.labels e) (e.directivesFromAddress st.2) st.1 st.2 _).All _
      rw [hbnd st hp]
      simp only [Directives.interp, Effects.All]
      exact Eventually.done _ hp
    | step st mid_p htrans _ ih =>
      obtain ⟨d, z, rest, hcode, hstep⟩ := htrans
      rw [Executable.straightline_cons hwf hcode]
      letI := (_root_.Executable.labels e)
      -- name the address behind the cell, so the transport unifies syntactically
      -- instead of reducing 64-bit arithmetic under a metavariable
      unfold Executable.stepAt at hstep
      generalize hnext : st.2 + (Int64.ofNat z) = pc' at hstep ⊢
      exact Directive.interp_sound (next := fun s' => mid_p (s', pc')) (jmp := mid_p)
        (fun s' hmid => ih (s', pc') hmid)
        (fun st' hmid => step_burst (ih st' hmid))
        hstep
  intro st h
  exact step_burst (key st h)

section Derive

/-! ## Deriving the ambient facts

A laid-out program satisfies `CodeWF`: `ValidLayout` gives a label cell zero
size and an instruction cell positive size, so the address behind an
instruction determines the position behind it. -/

private theorem dropWhile_eq_drop {α} (p : α → Bool) (l : List α) :
    ∃ j, l.dropWhile p = l.drop j ∧ ∀ i a, i < j → l[i]? = some a → p a = true := by
  induction l with
  | nil => exact ⟨0, rfl, by intro i a hi h; simp at h⟩
  | cons x xs ih =>
    obtain ⟨j, hj, hp⟩ := ih
    by_cases hx : p x
    · refine ⟨j + 1, ?_, ?_⟩
      · rw [List.dropWhile_cons, if_pos hx, List.drop_succ_cons]
        exact hj
      · intro i a hi hg
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
          exact hg ▸ hx
        | succ n =>
          simp only [List.getElem?_cons_succ] at hg
          exact hp n a (by omega) hg
    · refine ⟨0, ?_, by intro i a hi; omega⟩
      rw [List.dropWhile_cons, if_neg hx, List.drop_zero]

private theorem addrOf_succ_of_none (e : Kraken.Executable Directive) {n : Nat} (h : e.2[n]? = none) :
    e.addrOf (n + 1) = e.addrOf n := by
  have hle : e.2.length ≤ n := by
    by_cases hlt : n < e.2.length
    · rw [List.getElem?_eq_getElem hlt] at h; cases h
    · omega
  unfold Executable.addrOf Executable.sizeBefore
  rw [List.take_of_length_le (by omega), List.take_of_length_le hle]

/-- A run of label cells occupies no bytes, so the address does not move. -/
private theorem addrOf_add_of_labels (e : Kraken.Executable Directive) [Executable.ValidLayout e] {k : Nat} :
    ∀ (j : Nat), (∀ i a, i < j → e.2[k + i]? = some a → a.1.isLabel = true) →
      e.addrOf (k + j) = e.addrOf k := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have hstep : e.addrOf (k + n + 1) = e.addrOf (k + n) := by
      cases hc : e.2[k + n]? with
      | none => exact addrOf_succ_of_none e hc
      | some c =>
        have hlab := h n c (by omega) hc
        obtain ⟨d, z⟩ := c
        cases d with
        | label l =>
          have hz : z = 0 := Executable.ValidLayout.label_size (k + n) l z hc
          rw [Executable.addrOf_succ e hc, hz]
          simp
        | instr i => simp [Directive.isLabel] at hlab
        | byteArray a => simp [Directive.isLabel] at hlab
    rw [show k + (n + 1) = k + n + 1 from rfl, hstep]
    exact ih (fun i a hi hg => h i a (by omega) hg)

/-- A laid-out program is wellformed code. -/
theorem Kraken.Executable.codeWF_of_valid (e : Kraken.Executable Directive) [hv : Executable.ValidLayout e] :
    e.CodeWF where
  label_size := by
    intro c hc hlab
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨d, z⟩ := c
    cases d with
    | label l => exact hv.label_size i l z hi
    | instr i' => simp [Directive.isLabel] at hlab
    | byteArray a => simp [Directive.isLabel] at hlab
  advance := by
    intro pc d z rest hcode
    have hne : e.directivesFromAddress pc ≠ [] := by
      intro hnil
      rw [Executable.codeAt, hnil] at hcode
      simp at hcode
    obtain ⟨k, hklen, hkaddr, hkdrop⟩ := Executable.exists_pos_of_directivesFromAddress e hne
    obtain ⟨j, hj, hjp⟩ := dropWhile_eq_drop (fun c : Directive × Nat => c.1.isLabel)
      (e.directivesFromAddress pc)
    have hcodeDrop : e.2.drop (k + j) = (d, z) :: rest := by
      rw [← List.drop_drop, ← hkdrop, ← hj]
      exact hcode
    have hcell : e.2[k + j]? = some (d, z) := by
      have h0 : (e.2.drop (k + j))[0]? = some (d, z) := by rw [hcodeDrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hdlab : d.isLabel = false := by
      have := List.head?_dropWhile_not (p := fun c : Directive × Nat => c.1.isLabel)
        (l := e.directivesFromAddress pc)
      rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel) = (d, z) :: rest
        from hcode] at this
      simpa using this
    have haddr : e.addrOf (k + j) = pc := by
      rw [addrOf_add_of_labels e j ?_, hkaddr]
      intro i a hi hg
      refine hjp i a hi ?_
      rw [hkdrop, List.getElem?_drop]
      exact hg
    have hsucc : e.addrOf (k + j + 1) = pc + .ofNat z := by
      rw [Executable.addrOf_succ e hcell, haddr]
    have hfresh : ∀ i, i < k + j + 1 → e.addrOf i ≠ e.addrOf (k + j + 1) := by
      intro i hi
      refine Executable.addrOf_ne_of_valid e hi ?_ ?_
      · rw [show k + j + 1 - 1 = k + j from rfl, hcell]
        rfl
      · intro l zz hzz
        rw [show k + j + 1 - 1 = k + j from rfl, hcell] at hzz
        simp only [Option.some.injEq, Prod.mk.injEq] at hzz
        rw [hzz.1] at hdlab
        simp [Directive.isLabel] at hdlab
    have hlen : k + j + 1 ≤ e.2.length := by
      have : (e.2.drop (k + j)).length = e.2.length - (k + j) := List.length_drop
      rw [hcodeDrop] at this
      simp only [List.length_cons] at this
      omega
    have hdfa := Executable.directivesFromAddress_addrOf e (k + j + 1) hlen hfresh
    rw [hsucc] at hdfa
    rw [hdfa]
    have : e.2.drop (k + j + 1) = rest := by
      rw [show k + j + 1 = (k + j) + 1 from rfl, ← List.drop_drop, hcodeDrop]
      rfl
    exact this

/-- Unfold a placement at a cell that is not a label. -/
theorem Kraken.Executable.sits_cons_of_not_label {e : Kraken.Executable Directive} {pc : Int64} {d : Directive}
    {q : Program} (hd : d.isLabel = false) :
    e.sits pc (d :: q) = ∃ z rest, e.codeAt pc = (d, z) :: rest ∧ e.sits (pc + .ofNat z) q := by
  cases d with
  | label l => simp [Directive.isLabel] at hd
  | instr i => rfl
  | byteArray a => rfl

/-- Unfold the fall-through address past a cell that is not a label. -/
theorem Kraken.Executable.after_cons_of_not_label {e : Kraken.Executable Directive} {pc : Int64} {d : Directive}
    {q : Program} {z : Nat} {rest : List (Directive × Nat)} (hd : d.isLabel = false)
    (hcode : e.codeAt pc = (d, z) :: rest) :
    e.after pc (d :: q) = e.after (pc + .ofNat z) q := by
  cases d with
  | label l => simp [Directive.isLabel] at hd
  | instr i => simp only [Executable.after, hcode]
  | byteArray a => simp only [Executable.after, hcode]

/-! ### Walking a laid-out program

A laid-out program places the directive at position `i` at the address
`Executable.addrOf i`, so a fragment of the text sits at the address of its
first position (`Executable.walk_addrOf`), and a label's address is the
address of its cell (`Program.label_addrOf_drop`). The whole text sits at one
address only (`Executable.entry_of_sits`): a placement consumes one cell per
non-label directive, and the text has no cell to spare. -/

private theorem countP_frag [_root_.Layout] (f : Directive → Bool) :
    ∀ (n : Nat) (q : Program), (Layout.frag n q).countP (fun c => f c.1) = q.countP f := by
  intro n q
  induction q generalizing n with
  | nil => rfl
  | cons d q ih => rw [Layout.frag_cons, List.countP_cons, List.countP_cons, ih]

/-- The cell of a laid-out program at a position. -/
private theorem layout_getElem [layout : _root_.Layout] (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

/-- A label occupies no bytes. -/
private theorem size_label [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] {i : Nat} {l : Label}
    (hp : p[i]? = some (Directive.label l)) : Kraken.Layout.size Directive i = 0 :=
  hv.label_size i l _ (by rw [layout_getElem, hp]; rfl)

/-- Stepping one position advances the address by that position's size. -/
private theorem addrOf_step [layout : _root_.Layout] {p : Program} {i : Nat} {d : Directive}
    (hp : p[i]? = some d) :
    (layout p).addrOf (i + 1) = (layout p).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  Executable.addrOf_succ _ (by rw [layout_getElem, hp]; rfl)

/-- The cells at the address of a position that holds an instruction: the text
from that position on. -/
theorem Kraken.Executable.codeAt_addrOf [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {i : Nat} {d : Directive}
    (hd : d.isLabel = false) (hp : p[i]? = some d) :
    (layout p).codeAt ((layout p).addrOf i)
      = (d, Kraken.Layout.size Directive i) :: Layout.frag (i + 1) (p.drop (i + 1)) := by
  have hi : i < p.length := by
    by_cases h : i < p.length
    · exact h
    · rw [List.getElem?_eq_none (by omega)] at hp; cases hp
  have hlen : i ≤ (layout p).2.length := by
    rw [Layout.apply_snd, Layout.frag_length]; omega
  obtain ⟨j, hji, hdfa, hlab⟩ := Executable.exists_cut (layout p) hlen
  have hlent : ((p.drop j).take (i - j)).length = i - j := by
    rw [List.length_take, List.length_drop]; omega
  have hdrop : (layout p).2.drop j
      = Layout.frag j ((p.drop j).take (i - j)) ++ Layout.frag i (p.drop i) := by
    rw [Layout.apply_snd, Layout.frag_drop, Nat.zero_add]
    conv => lhs; rw [← List.take_append_drop (i - j) (p.drop j)]
    rw [Layout.frag_append, hlent, List.drop_drop, show j + (i - j) = i from by omega]
  have hslice : ∀ dz ∈ Layout.frag j ((p.drop j).take (i - j)),
      (fun c : Directive × Nat => c.1.isLabel) dz = true := by
    intro dz hdz
    show dz.1.isLabel = true
    obtain ⟨m, hm, heq⟩ := List.getElem_of_mem (Layout.frag_mem hdz)
    rw [hlent] at hm
    have hpm : p[j + m]? = some dz.1 := by
      rw [← List.getElem?_drop, ← List.getElem?_take_of_lt hm,
        List.getElem?_eq_getElem (by rw [hlent]; omega), heq]
    obtain ⟨l', z, hlz⟩ := hlab (j + m) (Nat.le_add_right j m) (by omega)
    rw [layout_getElem, hpm] at hlz
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlz
    rw [hlz.1]
    rfl
  have hget : p[i] = d := by
    have h := List.getElem?_eq_getElem hi
    rw [hp] at h
    exact (Option.some.inj h).symm
  have hhead : p.drop i = d :: p.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  rw [Executable.codeAt, hdfa, hdrop, List.dropWhile_append_of_pos hslice, hhead,
    Layout.frag_cons, List.dropWhile_cons, if_neg (by simpa using hd)]

/-- Walking a fragment of a laid-out program: it sits at the address of its
first position, and the walk ends at the address of the position behind it. -/
theorem Kraken.Executable.walk_addrOf [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] :
    ∀ (body rest : Program) (i : Nat), p.drop i = body ++ rest →
      (layout p).sits ((layout p).addrOf i) body
        ∧ (layout p).after ((layout p).addrOf i) body
            = (layout p).addrOf (i + body.length) := by
  intro body
  induction body with
  | nil => intro rest i _; exact ⟨trivial, by simp [Executable.after]⟩
  | cons d body ih =>
    intro rest i hdrop
    have hp : p[i]? = some d := by
      have h0 : (p.drop i)[0]? = some d := by rw [hdrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hdrop' : p.drop (i + 1) = body ++ rest := by
      rw [← List.drop_drop, hdrop]
      rfl
    obtain ⟨hsits, hafter⟩ := ih rest (i + 1) hdrop'
    by_cases hd : d.isLabel
    · obtain ⟨l, rfl⟩ : ∃ l, d = Directive.label l := by
        cases d with
        | label l => exact ⟨l, rfl⟩
        | instr i' => simp [Directive.isLabel] at hd
        | byteArray a => simp [Directive.isLabel] at hd
      have hstep : (layout p).addrOf (i + 1) = (layout p).addrOf i := by
        rw [addrOf_step hp, size_label hp]
        simp
      rw [hstep] at hsits hafter
      refine ⟨hsits, ?_⟩
      rw [show (layout p).after ((layout p).addrOf i) (Directive.label l :: body)
        = (layout p).after ((layout p).addrOf i) body from rfl, hafter]
      congr 1
      simp only [List.length_cons]
      omega
    · have hdf : d.isLabel = false := by simpa using hd
      have hcode := Executable.codeAt_addrOf hdf hp
      rw [addrOf_step hp] at hsits hafter
      refine ⟨?_, ?_⟩
      · rw [Executable.sits_cons_of_not_label hdf]
        exact ⟨_, _, hcode, hsits⟩
      · rw [Executable.after_cons_of_not_label hdf hcode, hafter]
        congr 1
        simp only [List.length_cons]
        omega

/-- A placement consumes one cell per non-label directive: the segment at the
placement's start is the segment behind it, with those cells in front. -/
private theorem consume {e : Kraken.Executable Directive} (hwf : e.CodeWF) :
    ∀ (q : Program) (pc : Int64), e.sits pc q →
      ∃ pre, e.directivesFromAddress pc = pre ++ e.directivesFromAddress (e.after pc q)
        ∧ pre.countP (fun c => !c.1.isLabel) = q.countP (fun d => !d.isLabel) := by
  intro q
  induction q with
  | nil => intro pc _; exact ⟨[], by simp [Executable.after], by simp⟩
  | cons d q ih =>
    intro pc hsits
    by_cases hd : d.isLabel
    · obtain ⟨l, rfl⟩ : ∃ l, d = Directive.label l := by
        cases d with
        | label l => exact ⟨l, rfl⟩
        | instr i => simp [Directive.isLabel] at hd
        | byteArray a => simp [Directive.isLabel] at hd
      obtain ⟨pre, hpre, hcnt⟩ := ih pc hsits
      exact ⟨pre, hpre, by simpa [List.countP_cons, Directive.isLabel] using hcnt⟩
    · have hdf : d.isLabel = false := by simpa using hd
      rw [Executable.sits_cons_of_not_label hdf] at hsits
      obtain ⟨z, rest, hcode, hsits'⟩ := hsits
      obtain ⟨pre, hpre, hcnt⟩ := ih (pc + (Int64.ofNat z : Int64)) hsits'
      refine ⟨(e.directivesFromAddress pc).takeWhile (fun c => c.1.isLabel) ++ (d, z) :: pre,
        ?_, ?_⟩
      · rw [Executable.after_cons_of_not_label hdf hcode, List.append_assoc,
          List.cons_append, ← hpre, hwf.advance pc d z rest hcode]
        conv => lhs; rw [← List.takeWhile_append_dropWhile
          (p := fun c : Directive × Nat => c.1.isLabel) (l := e.directivesFromAddress pc)]
        rw [show (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)
          = (d, z) :: rest from hcode]
      · have hzero : ((e.directivesFromAddress pc).takeWhile
            (fun c => c.1.isLabel)).countP (fun c => !c.1.isLabel) = 0 :=
          List.countP_eq_zero.mpr (fun c hc => by
            simp [mem_takeWhile (p := fun c : Directive × Nat => c.1.isLabel) hc])
        rw [List.countP_append, hzero, List.countP_cons, List.countP_cons, hcnt, hdf]
        simp

/-- The one address a laid-out program sits at: its start. Every non-label
directive consumes a cell, and the text has exactly as many. -/
theorem Kraken.Executable.entry_of_sits [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] (hne : 0 < p.countP (fun d => !d.isLabel))
    {pc : Int64} (h : (layout p).sits pc p) : pc = (layout p).addrOf 0 := by
  obtain ⟨pre, hpre, hcnt⟩ := consume (Executable.codeWF_of_valid (layout p)) p pc h
  have htext : ((layout p).2).countP (fun c => !c.1.isLabel)
      = p.countP (fun d => !d.isLabel) := by
    rw [Layout.apply_snd]
    exact countP_frag (fun d => !d.isLabel) 0 p
  have hnil : (layout p).directivesFromAddress pc ≠ [] := by
    intro hz
    rw [hz] at hpre
    have : pre = [] := (List.append_eq_nil_iff.mp hpre.symm).1
    rw [this] at hcnt
    simp at hcnt
    omega
  obtain ⟨k, -, hk, hdrop⟩ :=
    Executable.exists_pos_of_directivesFromAddress (layout p) hnil
  have hsplit : ((layout p).2).countP (fun c => !c.1.isLabel)
      = (((layout p).2).take k).countP (fun c => !c.1.isLabel)
        + (((layout p).2).drop k).countP (fun c => !c.1.isLabel) := by
    conv => lhs; rw [← List.take_append_drop k ((layout p).2)]
    rw [List.countP_append]
  rw [← hdrop, hpre, List.countP_append, hcnt, htext] at hsplit
  have htake : (((layout p).2).take k).countP (fun c => !c.1.isLabel) = 0 := by omega
  have hlabels : ∀ i a, i < k → ((layout p).2)[0 + i]? = some a → a.1.isLabel = true := by
    intro i a hi hget
    rw [Nat.zero_add] at hget
    have hmem : a ∈ ((layout p).2).take k :=
      List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_take_of_lt hi]; exact hget⟩
    simpa using List.countP_eq_zero.mp htake a hmem
  rw [← hk]
  have := addrOf_add_of_labels (layout p) (k := 0) k hlabels
  rw [Nat.zero_add] at this
  exact this

/-- The address of a label, from the position its scope suffix starts at. -/
theorem Program.label_addrOf_drop [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] (hnd : (Program.labels p).Nodup)
    {l : Label} {i : Nat} (hdrop : p.drop i = Program.fromLabel p l)
    (hne : Program.fromLabel p l ≠ []) :
    (_root_.Executable.labels (layout p)).label l = (layout p).addrOf i := by
  obtain ⟨t, rest, hsplit, hfl, hfresh, hlen⟩ := Program.fromLabel_split hnd hne
  have hplen : p.length = t.length + (Program.fromLabel p l).length := by
    have h := congrArg List.length hsplit
    rw [hfl]
    simpa using h
  have hdlen : p.length - i = (Program.fromLabel p l).length := by
    have h := congrArg List.length hdrop
    rwa [List.length_drop] at h
  have hile : i ≤ p.length := by
    by_cases h : i ≤ p.length
    · exact h
    · rw [List.drop_eq_nil_of_le (by omega)] at hdrop
      exact absurd hdrop.symm hne
  have hit : i = t.length := by omega
  have hcell : p[i]? = some (Directive.label l) := by
    have h0 : (p.drop i)[0]? = some (Directive.label l) := by rw [hdrop, hfl]; rfl
    rw [List.getElem?_drop] at h0
    simpa using h0
  have hlay : (layout p).2[i]? = some (Directive.label l, Kraken.Layout.size Directive i) := by
    rw [layout_getElem, hcell]; rfl
  refine Executable.label_addrOf (layout p) l i ?_ ?_
  · rw [hlay, hv.label_size i l _ hlay]
  · have hpt : p.take i = t := by
      rw [hit, hsplit]
      exact List.take_left' rfl
    have htake : ((layout p).2).take i = Layout.frag 0 (p.take i) := by
      rw [Layout.apply_snd]
      conv => lhs; rw [← List.take_append_drop i p, Layout.frag_append]
      exact List.take_left' (by rw [Layout.frag_length, List.length_take]; omega)
    intro dz hdz heq
    rw [htake, hpt] at hdz
    exact hfresh (Program.mem_labels_of_cell (heq ▸ Layout.frag_mem hdz))

/-- A label whose scope suffix starts right behind an `.align n` directive is
`n`-aligned, whatever the layout. Every hypothesis is decidable for a concrete
program. -/
theorem Program.label_aligned_of_align [layout : _root_.Layout] {p : Program}
    [hv : Executable.ValidLayout (layout p)] (hnd : (Program.labels p).Nodup)
    {l : Label} {i : Nat} {aw w : Width} {n : Nat} {pad : Option Nat}
    (hal : p[i]? = some (.instr (.regular aw w (.nopalign n pad))))
    (hdrop : p.drop (i + 1) = Program.fromLabel p l)
    (hne : Program.fromLabel p l ≠ []) (hn : 0 < n) :
    isAligned n ((_root_.Executable.labels (layout p)).label l).toBitVec = true := by
  rw [Program.label_addrOf_drop hnd hdrop hne]
  have h := hv.align_addr i aw w n pad _ (by rw [layout_getElem, hal]; rfl) hn
  simp [isAligned, h]

/-- Behind a laid-out program whose last cell is an instruction the text runs
out. -/
theorem Kraken.Executable.directivesFromAddress_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive}
    (hlast : p[p.length - 1]? = some dlast) (hd : dlast.isLabel = false) :
    (layout p).directivesFromAddress ((layout p).addrOf p.length) = [] := by
  have hlen : (layout p).2.length = p.length := by
    rw [Layout.apply_snd, Layout.frag_length]
  have hcell : (layout p).2[p.length - 1]? = some (dlast, Kraken.Layout.size Directive (p.length - 1)) := by
    rw [layout_getElem, hlast]; rfl
  have hfresh : ∀ k, k < p.length → (layout p).addrOf k ≠ (layout p).addrOf p.length := by
    intro k hk
    refine Executable.addrOf_ne_of_valid (layout p) hk (by rw [hcell]; rfl) ?_
    intro l z hz
    rw [hcell] at hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hz
    rw [hz.1] at hd
    simp [Directive.isLabel] at hd
  rw [Executable.directivesFromAddress_addrOf (layout p) p.length (by omega) hfresh]
  exact List.drop_eq_nil_of_le (by omega)

/-- The empty exit channel holds nowhere. -/
theorem Kraken.Executable.bot_elim {a : Int64} {s : MachineData} {C : Prop}
    (h : (⊥ : Int64 → MachineData → Prop) a s) : C :=
  ((Lean.Order.bot_le (α := Int64 → MachineData → Prop) (fun _ _ => False)) a s h).elim

open MachineWP in
/-- A triple on a laid-out program, read at the machine as the baseline
judgment: from the start address the segment judgment reaches the triple's
postcondition. -/
theorem Program.run_of_triple [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {s : MachineData} {dlast : Directive}
    (ht : ⦃ P ⦄ p ⦃ Q ⦄) (hs : P s)
    (henv : cenv = layout p := by rfl)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    Eventually (straightlineStep (layout p)) (fun st => Q () st.1) (s, Kraken.Layout.start Directive) := by
  have h : (layout p).wp p (Q ()) ⊥ s := henv ▸ ht.le_wp s hs
  obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  rw [Nat.zero_add] at hafter
  have hev := h ((layout p).addrOf 0) hsits
  rw [hafter, Executable.addrOf_zero, Layout.apply_fst] at hev
  have hbnd : ∀ st : MachineState,
      ((st.2 = (layout p).addrOf p.length ∧ Q () st.1)
        ∨ (⊥ : Int64 → MachineData → Prop) st.2 st.1) →
      (layout p).directivesFromAddress st.2 = [] := by
    rintro ⟨s', a⟩ (⟨rfl, -⟩ | hbot)
    · exact Executable.directivesFromAddress_end hlast hd
    · exact Executable.bot_elim hbot
  refine eventually_weaken _ _ _ _ ?_
    (Executable.bridge (Executable.codeWF_of_valid (layout p)) hbnd _ hev)
  rintro ⟨s', a⟩ (⟨-, hq⟩ | hbot)
  · exact hq
  · exact Executable.bot_elim hbot

end Derive

/-! ## Linking fragments

`Program.link` ties finitely or infinitely many separately verified
fragments into one run. Each index `i` names a placed fragment: its text
`frag i` and the address `entry i` where it starts. The address behind it is
derived, `cenv.after`. `T i` is the invariant at that entry, and
`r` orders index-state pairs. A fragment's obligation is a Triple, so `vcgen`
proves it; `link` supplies the well-founded induction that a back edge
needs. -/

/-- Where a step out of fragment `i`, entered in state `s₀`, may land: the
global postcondition at the address it stopped at, or another fragment's
entry, with that fragment's invariant and a smaller measure. -/
def Program.Cont {ι : Type} (post : @Post MachineState) (entry : ι → Int64)
    (T : ι → MachineData → Prop) (r : ι × MachineData → ι × MachineData → Prop)
    (i : ι) (s₀ : MachineData) (a : Int64) (s : MachineData) : Prop :=
  post (s, a) ∨ ∃ j, entry j = a ∧ T j s ∧ r (j, s) (i, s₀)

open MachineWP in
/-- `Program.link` with each fragment's obligation at its entry address, so
that a fragment may read the pc. -/
theorem Program.link_at [CodeEnv] {ι : Type} {post : @Post MachineState}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → Prop)
    (r : ι × MachineData → ι × MachineData → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀,
      TripleAt (entry i) (fun s => T i s ∧ s = s₀) (frag i)
        (fun _ s => Program.Cont post entry T r i s₀ (cenv.after (entry i) (frag i)) s)
        (fun a s => Program.Cont post entry T r i s₀ a s)) :
    ∀ i s, T i s → Eventually cenv.instrStep post (s, entry i) := by
  suffices h : ∀ is : ι × MachineData, T is.1 is.2 →
      Eventually cenv.instrStep post (is.2, entry is.1) by
    intro i s hT
    exact h (i, s) hT
  intro is
  induction is using hwf.induction with
  | _ is ih =>
    intro hT
    have hev := hfrag is.1 is.2 is.2 ⟨hT, rfl⟩ (hplace is.1)
    refine eventually_trans _ _ _ _ hev ?_
    rintro ⟨s', a⟩ (⟨ha, hc⟩ | hc)
    · subst ha
      rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · rw [← hj]
        exact ih (j, s') hr hTj
    · rcases hc with hp | ⟨j, hj, hTj, hr⟩
      · exact Eventually.done _ hp
      · dsimp only at hj
        rw [← hj]
        exact ih (j, s') hr hTj

open MachineWP in
theorem Program.link [CodeEnv] {ι : Type} {post : @Post MachineState}
    (frag : ι → Program) (entry : ι → Int64) (T : ι → MachineData → Prop)
    (r : ι × MachineData → ι × MachineData → Prop) (hwf : WellFounded r)
    (hplace : ∀ i, cenv.sits (entry i) (frag i))
    (hfrag : ∀ i s₀,
      ⦃ fun s => T i s ∧ s = s₀ ⦄
        frag i
      ⦃ fun _ s => Program.Cont post entry T r i s₀
          (cenv.after (entry i) (frag i)) s;
        fun a s => Program.Cont post entry T r i s₀ a s ⦄) :
    ∀ i s, T i s → Eventually cenv.instrStep post (s, entry i) :=
  Program.link_at frag entry T r hwf hplace (fun i s₀ => TripleAt.of_triple (hfrag i s₀))

/-! ## The control-flow rule

`Program.cfg` instantiates `link` at the blocks of a labeled program: the
index is the label, the entry is the label's address, the fragment is the
block body, and the order is the lex order of variant and block position.
`Program.Placed` collects the placement facts that connect the program's
syntax to the ambient addresses. -/

/-- Where the blocks of a fragment sit in the ambient code: every block at its
label's address, falling through to the address of the label behind it. This
much holds of one procedure inside a larger image, so it is what a procedure's
proof assumes (`Program.PlacedIn.of_placed` derives it from the image's
`Placed`). -/
structure Program.PlacedIn [CodeEnv] (p : Program) : Prop where
  /-- A block's body sits at its label's address. -/
  block : ∀ l blk, Program.blockAt p l = some blk →
    cenv.sits ((_root_.Executable.labels cenv).label l) blk.body
  /-- A block that falls into another ends at that block's address. -/
  next : ∀ l blk l', Program.blockAt p l = some blk → blk.next = some l' →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = (_root_.Executable.labels cenv).label l'

/-- Where a label's block sits in the ambient code, for the whole text. -/
structure Program.Placed [CodeEnv] (p : Program) (l₀ : Label) : Prop
    extends Program.PlacedIn p where
  /-- Every placement of the text starts at the entry label's address. -/
  entry : ∀ pc, cenv.sits pc p → (_root_.Executable.labels cenv).label l₀ = pc
  /-- The last block ends where the text ends. -/
  last : ∀ l blk, Program.blockAt p l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after ((_root_.Executable.labels cenv).label l₀) p

/-- The placement facts of a laid-out program: every block sits at its label's
address, and falls through to the address of the label behind it. -/
theorem Program.placed_of_layout [layout : _root_.Layout] {p p' : Program}
    [Executable.ValidLayout (layout p)] {l₀ : Label} (hwf : Program.WF p)
    (hp : p = Directive.label l₀ :: p')
    (hne : p.any (fun d => !d.isLabel) = true) :
    @Program.Placed ⟨layout p⟩ p l₀ := by
  have hnd := hwf.nodup
  -- the entry label names the start of the text
  have hfl₀ : Program.fromLabel p l₀ = p := by
    have hlab : Program.labels p = l₀ :: Program.labels p' := by rw [hp]; rfl
    have hp' : Program.fromLabel p' l₀ = [] := by
      by_cases h : Program.fromLabel p' l₀ = []
      · exact h
      · exact absurd (Program.mem_labels_of_cell (Program.fromLabel_mem h))
          (by rw [hlab] at hnd; exact (List.nodup_cons.mp hnd).1)
    rw [hp, Program.fromLabel_cons, if_pos ⟨hp', rfl⟩]
  have hne₀ : Program.fromLabel p l₀ ≠ [] := by
    rw [hfl₀, hp]
    exact List.cons_ne_nil _ _
  have hentry : (_root_.Executable.labels (layout p)).label l₀ = (layout p).addrOf 0 :=
    Program.label_addrOf_drop hnd (l := l₀) (i := 0) (by rw [List.drop_zero, hfl₀]) hne₀
  have hwhole : (layout p).after ((layout p).addrOf 0) p
      = (layout p).addrOf p.length := by
    have h := (Executable.walk_addrOf (p := p) p [] 0 (by simp)).2
    rwa [Nat.zero_add] at h
  -- every block, at the position of its label cell
  have hpos : ∀ l blk, Program.blockAt p l = some blk →
      ∃ pos i, pos < p.length
        ∧ blk.next = ((Program.view p).2[i + 1]?).map (·.1)
        ∧ p.drop (pos + 1)
            = blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells
        ∧ (_root_.Executable.labels (layout p)).label l = (layout p).addrOf pos
        ∧ (layout p).sits ((layout p).addrOf pos) blk.body
        ∧ (layout p).after ((layout p).addrOf pos) blk.body
            = (layout p).addrOf (pos + 1 + blk.body.length) := by
    intro l blk hb
    obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec hb
    have hne' : Program.fromLabel p l ≠ [] :=
      Program.fromLabel_ne_nil_of_mem (Program.blockAt_mem_labels hb)
    obtain ⟨t, rest, hsplit, hfl, -, -⟩ := Program.fromLabel_split hnd hne'
    have hdropt : p.drop t.length = Program.fromLabel p l := by
      conv => lhs; rw [hsplit]
      rw [List.drop_left, hfl]
    have hdrop : p.drop t.length
        = Directive.label l
          :: (blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells) := by
      rw [hdropt, Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi]
    have hlabel : (_root_.Executable.labels (layout p)).label l = (layout p).addrOf t.length :=
      Program.label_addrOf_drop hnd hdropt hne'
    have hcell : p[t.length]? = some (Directive.label l) := by
      have h0 : (p.drop t.length)[0]? = some (Directive.label l) := by rw [hdrop]; rfl
      rw [List.getElem?_drop] at h0
      simpa using h0
    have hlt : t.length < p.length := by
      by_cases h : t.length < p.length
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
    have hstep : (layout p).addrOf (t.length + 1) = (layout p).addrOf t.length := by
      rw [addrOf_step hcell, size_label hcell]
      simp
    have hbody : p.drop (t.length + 1)
        = blk.body ++ ((Program.view p).2.drop (i + 1)).flatMap Program.blockCells := by
      rw [← List.drop_drop, hdrop]
      rfl
    obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf blk.body _ (t.length + 1) hbody
    rw [hstep] at hsits hafter
    exact ⟨t.length, i, hlt, hnext, hbody, hlabel, hsits, hafter⟩
  refine @Program.Placed.mk ⟨layout p⟩ p l₀ (@Program.PlacedIn.mk ⟨layout p⟩ p ?block ?next)
    ?entry ?last
  case entry =>
    intro pc hplace
    rw [hentry]
    exact (Executable.entry_of_sits (List.countP_pos_iff.mpr (List.any_eq_true.mp hne))
      hplace).symm
  case block =>
    intro l blk hb
    obtain ⟨pos, i, -, -, -, hlabel, hsits, -⟩ := hpos l blk hb
    rw [hlabel]
    exact hsits
  case next =>
    intro l blk l' hb hn
    obtain ⟨pos, i, -, hnext, hbody, hlabel, -, hafter⟩ := hpos l blk hb
    show (layout p).after ((_root_.Executable.labels (layout p)).label l) blk.body = (_root_.Executable.labels (layout p)).label l'
    rw [hn] at hnext
    obtain ⟨⟨l₁, b₁⟩, hi'⟩ : ∃ lb, (Program.view p).2[i + 1]? = some lb := by
      cases h : (Program.view p).2[i + 1]? with
      | none => rw [h] at hnext; cases hnext
      | some lb => exact ⟨lb, rfl⟩
    rw [hi'] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    have htail : p.drop (pos + 1 + blk.body.length) = Program.fromLabel p l' := by
      rw [← List.drop_drop, hbody, List.drop_left, Program.fromLabel_view hnd hi']
    have hne' : Program.fromLabel p l' ≠ [] := by
      rw [Program.fromLabel_view hnd hi', Program.drop_flatMap_cons hi']
      exact List.cons_ne_nil _ _
    rw [hlabel, hafter, Program.label_addrOf_drop hnd htail hne']
  case last =>
    intro l blk hb hn
    obtain ⟨pos, i, hlt, hnext, hbody, hlabel, -, hafter⟩ := hpos l blk hb
    show (layout p).after ((_root_.Executable.labels (layout p)).label l) blk.body
      = (layout p).after ((_root_.Executable.labels (layout p)).label l₀) p
    rw [hn] at hnext
    have hnone : (Program.view p).2[i + 1]? = none := by
      cases h : (Program.view p).2[i + 1]? with
      | none => rfl
      | some lb => rw [h] at hnext; cases hnext
    have hdropnil : (Program.view p).2.drop (i + 1) = [] :=
      List.drop_eq_nil_of_le (by
        by_cases hle : (Program.view p).2.length ≤ i + 1
        · exact hle
        · rw [List.getElem?_eq_getElem (by omega)] at hnone; cases hnone)
    rw [hdropnil] at hbody
    simp only [List.flatMap_nil, List.append_nil] at hbody
    have hlenb : pos + 1 + blk.body.length = p.length := by
      have h := congrArg List.length hbody
      rw [List.length_drop] at h
      omega
    rw [hlabel, hafter, hlenb, ← hwhole, hentry]

/-- The blocks of `p` are among those of `q`: same bodies, and the same
successor wherever `p` has one. Decidable, so `by decide` closes it for
closed texts; it holds when `p` is a run of whole blocks of `q`. -/
def Program.subBlocksOf (p q : Program) : Bool :=
  (Program.view p).2.all fun lb =>
    match Program.blockAt p lb.1, Program.blockAt q lb.1 with
    | some blk, some blk' =>
      decide (blk'.body = blk.body) && (blk.next.isNone || decide (blk'.next = blk.next))
    | _, _ => false

/-- A fragment whose blocks are among a placed text's is placed. -/
theorem Program.PlacedIn.of_placed [CodeEnv] {p q : Program} {m₀ : Label}
    (hq : Program.Placed q m₀) (h : Program.subBlocksOf p q = true) : Program.PlacedIn p := by
  have key : ∀ l blk, Program.blockAt p l = some blk →
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ (blk.next.isNone = true ∨ blk'.next = blk.next) := by
    intro l blk hb
    have hmem : l ∈ (Program.view p).2.map (·.1) := by
      rw [← Program.labels_view]
      exact Program.blockAt_mem_labels hb
    obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hmem
    have hall := List.all_eq_true.mp h lb hlb
    simp only [hb] at hall
    cases hb' : Program.blockAt q lb.1 with
    | none => rw [hb'] at hall; cases hall
    | some blk' =>
      rw [hb'] at hall
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hall
      exact ⟨blk', rfl, hall.1, hall.2⟩
  refine ⟨?_, ?_⟩
  · intro l blk hb
    obtain ⟨blk', hb', hbody, -⟩ := key l blk hb
    rw [← hbody]
    exact hq.block l blk' hb'
  · intro l blk l' hb hn
    obtain ⟨blk', hb', hbody, hnext⟩ := key l blk hb
    rw [hn] at hnext
    simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hnext
    rw [← hbody]
    exact hq.next l blk' l' hb' hnext

/-- A label-keyed table, read at an address. -/
def Table.ofLabels [CodeEnv] (tl : Label → MachineData → Prop) :
    Int64 → MachineData → Prop :=
  fun a s => ∃ l, (_root_.Executable.labels cenv).label l = a ∧ tl l s

@[grind ←] theorem Table.ofLabels_at [CodeEnv] {tl : Label → MachineData → Prop}
    {l : Label} {s : MachineData} (h : tl l s) :
    Table.ofLabels tl ((_root_.Executable.labels cenv).label l) s := ⟨l, rfl, h⟩

/-- The block a block falls into: it is mapped, and it sits one position
later in the text. -/
theorem Program.blockAt_next {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk)
    {l' : Label} (hn : blk.next = some l') :
    (Program.blockAt p l').isSome ∧ Program.blockIdx p l' = Program.blockIdx p l + 1 := by
  obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec h
  rw [hn] at hnext
  have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
  cases hj : (Program.view p).2[i + 1]? with
  | none => rw [hj] at hnext; cases hnext
  | some lb =>
    obtain ⟨l₁, b₁⟩ := lb
    rw [hj] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    subst hnext
    refine ⟨?_, ?_⟩
    · show (Program.blockAtAux (Program.view p).2 l').isSome = true
      rw [Program.blockAtAux_of_getElem hndv hj]
      rfl
    · rw [Program.blockIdx_eq hnd hj, Program.blockIdx_eq hnd hi]

/-- A mapped label sits inside the block list. -/
theorem Program.blockIdx_lt {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.blockIdx p l < (Program.view p).2.length := by
  obtain ⟨-, i, hi, -⟩ := Program.blockAtAux_spec h
  rw [Program.blockIdx_eq hnd hi]
  by_cases hlt : i < (Program.view p).2.length
  · exact hlt
  · rw [List.getElem?_eq_none (by omega)] at hi
    cases hi

/-- The block index never exceeds the number of blocks. -/
theorem Program.blockIdx_le (p : Program) (l : Label) :
    Program.blockIdx p l ≤ (Program.view p).2.length := by
  have h := List.idxOf_le_length (a := l) (l := Program.labels p)
  have hlen : (Program.labels p).length = (Program.view p).2.length := by
    rw [Program.labels_view, List.length_map]
  rw [hlen] at h
  exact h

/-- The lex order of the control-flow rule, encoded in one number: the
variant dominates, and the block position breaks ties. -/
private def Program.cfgMeasure (p : Program) (var : Label → MachineData → Nat)
    (x : Label × MachineData) : Nat :=
  var x.1 x.2 * ((Program.view p).2.length + 1)
    + ((Program.view p).2.length - Program.blockIdx p x.1)

/-- The control-flow rule: one spec table `T`, one variant `var`, one triple
per block of the map `Program.blockAt`. Each block is entered with its table
entry and the variant snapshotted; it falls into the next block with the
entry there and the variant not increased, and a jump exit lands on a mapped
table entry along `Program.EdgeLt`. -/
theorem MachineWP.cfg [CodeEnv] {p p' : Program} {P : MachineData → Prop}
    {Q : Unit → MachineData → Prop} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => Q);
        Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.Placed p l₀ := by
      first
        | assumption
        | exact Program.placed_of_layout (by decide) (by rfl) (by decide))
    (hP : P = T l₀ := by rfl) :
    ⦃ P ⦄ p ⦃ Q ⦄ := by
  subst hP
  have hnd := hwf.nodup
  refine Triple.intro fun s hT => ?_
  intro pc hplace
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length :=
    Program.blockIdx_le p
  have key := Program.link (post := fun st => st.2 = cenv.after pc p ∧ Q () st.1)
    (frag := fun l => (Program.blockAt p l).elim [] (·.body))
    (entry := fun l => (_root_.Executable.labels cenv).label l)
    (T := fun l s => (Program.blockAt p l).isSome ∧ T l s)
    (r := fun x y => Program.cfgMeasure p var x < Program.cfgMeasure p var y)
    (measure (Program.cfgMeasure p var)).wf ?_ ?_
  · have h0 : (Program.blockAt p l₀).isSome := by
      rw [hp]
      show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
      simp [Program.view, Program.blockAtAux]
    have hrun := key l₀ s ⟨h0, hT⟩
    rw [hpl.entry pc hplace] at hrun
    exact eventually_weaken _ _ _ _ (fun st hst => Or.inl hst) hrun
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s₀
    cases hb : Program.blockAt p l with
    | none =>
      exact Triple.intro fun s hpre => absurd hpre.1.1 (by simp [hb])
    | some blk =>
      simp only [Option.elim]
      refine Triple.intro fun s hpre => ?_
      obtain ⟨⟨-, hTl⟩, rfl⟩ := hpre
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hb
      refine Executable.wp_mono ?_ ?_ ((hblocks l blk hb (var l s)).le_wp s ⟨hTl, rfl⟩)
      · intro s' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          simp only [Program.cfgMeasure]
          omega
        | none =>
          rw [hnx] at hq
          have hend : cenv.after ((_root_.Executable.labels cenv).label l) blk.body = cenv.after pc p := by
            rw [hpl.last l blk hb hnx, hpl.entry pc hplace]
          exact Or.inl ⟨hend.symm ▸ rfl, hq⟩
      · rintro a s' ⟨l', hlab, hsome', hTl', hedge⟩
        refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
        have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
        simp only [Program.cfgMeasure]
        rcases hedge with hlt | ⟨heq, hij⟩
        · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hlt
          have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
              = var l' s' * ((Program.view p).2.length + 1)
                + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
          omega
        · rw [heq]
          omega

/-! ## The control-flow rule for a procedure

`cfg` concludes a triple on the whole text, which needs the text to be the
whole placement (`Placed.entry`) and closes the exit channel. A procedure is
a fragment of a larger image that leaves through `ret` (or a tail jump), so
its rule, `cfg_reach`, takes `PlacedIn`, keeps the exit channel `E` open, and
concludes that the run from the entry label reaches `E`. `ProcSpec.of_cfg`
and `ProcSpecK.of_cfg` dress this as a procedure specification: the table
and the exits may mention the logical variable, the return address and the
entry state, and the exits are those the convention allows — by default a
return, `a = ra` with the postcondition; a tail call `jmp f` adds an exit at
`f`'s label discharged by `f`'s `ProcSpec` at the same `ra` (`hexit`). -/

/-- `cfg_reach` with each block's obligation a `TripleAt` its label's address,
so that a block may read the pc. `cfg` for a fragment with an open exit channel: entered at `l₀` with its
table entry, the run reaches `E`. The last block must not fall off the end. -/
theorem MachineWP.cfg_reach_at [CodeEnv] {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (E : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      MachineWP.TripleAt ((_root_.Executable.labels cenv).label l)
        (fun s => T l s ∧ var l s = n) blk.body
        (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ _ => False)
        (fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ E a s))
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s, T l₀ s →
      Eventually cenv.instrStep (fun st => E st.2 st.1) (s, (_root_.Executable.labels cenv).label l₀) := by
  have hnd := hwf.nodup
  intro s hT
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length :=
    Program.blockIdx_le p
  have key := Program.link_at (post := fun st => E st.2 st.1)
    (frag := fun l => (Program.blockAt p l).elim [] (·.body))
    (entry := fun l => (_root_.Executable.labels cenv).label l)
    (T := fun l s => (Program.blockAt p l).isSome ∧ T l s)
    (r := fun x y => Program.cfgMeasure p var x < Program.cfgMeasure p var y)
    (measure (Program.cfgMeasure p var)).wf ?_ ?_
  · have h0 : (Program.blockAt p l₀).isSome := by
      rw [hp]
      show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
      simp [Program.view, Program.blockAtAux]
    exact key l₀ s ⟨h0, hT⟩
  · intro l
    cases hb : Program.blockAt p l with
    | none => exact trivial
    | some blk => simpa using hpl.block l blk hb
  · intro l s
    cases hb : Program.blockAt p l with
    | none =>
      exact fun _ hpre _ => absurd hpre.1.1 (by simp)
    | some blk =>
      simp only [Option.elim]
      have hidx : Program.blockIdx p l < (Program.view p).2.length :=
        Program.blockIdx_lt hnd hb
      refine MachineWP.TripleAt.pre ?_
        (MachineWP.TripleAt.mono ?_ ?_ (hblocks l blk hb (var l s)))
      · rintro s' ⟨⟨-, hTl⟩, rfl⟩
        exact ⟨hTl, rfl⟩
      · intro s' hq
        cases hnx : blk.next with
        | some l' =>
          rw [hnx] at hq
          obtain ⟨hTl', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hb hnx
          refine Or.inr ⟨l', (hpl.next l blk l' hb hnx).symm, ⟨hsome', hTl'⟩, ?_⟩
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          simp only [Program.cfgMeasure]
          omega
        | none =>
          rw [hnx] at hq
          exact hq.elim
      · rintro a s' (⟨l', hlab, hsome', hTl', hedge⟩ | hE)
        · refine Or.inr ⟨l', hlab, ⟨hsome', hTl'⟩, ?_⟩
          have hle' : Program.blockIdx p l' ≤ (Program.view p).2.length := hK l'
          simp only [Program.cfgMeasure]
          rcases hedge with hlt | ⟨heq, hij⟩
          · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
                ≤ var l s * ((Program.view p).2.length + 1) :=
              Nat.mul_le_mul_right _ hlt
            have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
                = var l' s' * ((Program.view p).2.length + 1)
                  + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
            omega
          · rw [heq]
            omega
        · exact Or.inl hE

/-- `cfg` for a fragment with an open exit channel: entered at `l₀` with its
table entry, the run reaches `E`. The last block must not fall off the end. -/
theorem MachineWP.cfg_reach [CodeEnv] {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (E : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ E a s ⦄)
    (hp : p = Directive.label l₀ :: p') (hwf : Program.WF p) (hpl : Program.PlacedIn p) :
    ∀ s, T l₀ s →
      Eventually cenv.instrStep (fun st => E st.2 st.1) (s, (_root_.Executable.labels cenv).label l₀) :=
  MachineWP.cfg_reach_at T var E
    (fun l blk hb n => MachineWP.TripleAt.of_triple (hblocks l blk hb n)) hp hwf hpl

open MachineWP in
/-- A procedure's spec from its blocks. `T x ra t₀ l` is the table entry at
label `l` for the logical variable `x`, the address `ra` to reach, and the
entry state `t₀`; `Exit` the exits the blocks may take besides jumps inside
the procedure, by default the return `a = ra ∧ Post x ra t₀ s`; `hexit` that
every exit reaches `ra` with `Post`, automatic for the default. The blocks
are discharged with `intro x ra t₀` and `cfg_cases`. -/
theorem Kraken.Executable.ProcSpec.of_cfg [CodeEnv] {p p' : Program} {l₀ : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : α → Int64 → MachineData → Int64 → MachineData → Prop :=
      fun x ra t₀ a s => a = ra ∧ Post x ra t₀ s)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x ra t₀ a s ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hexit : ∀ x ra t₀ a s, Exit x ra t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ Post x ra t₀ st.1) (s, a) := by
      rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var (Exit x ra t) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit x ra t st.2 st.1 hst)

open MachineWP in
/-- `ProcSpec.of_cfg` with each block's obligation a `TripleAt` its label's
address, so that a block may read the pc (`lea_rip_disp_at`). A procedure's spec from its blocks. `T x ra t₀ l` is the table entry at
label `l` for the logical variable `x`, the address `ra` to reach, and the
entry state `t₀`; `Exit` the exits the blocks may take besides jumps inside
the procedure, by default the return `a = ra ∧ Post x ra t₀ s`; `hexit` that
every exit reaches `ra` with `Post`, automatic for the default. The blocks
are discharged with `intro x ra t₀` and `cfg_cases`. -/
theorem Kraken.Executable.ProcSpec.of_cfg_at [CodeEnv] {p p' : Program} {l₀ : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : α → Int64 → MachineData → Int64 → MachineData → Prop :=
      fun x ra t₀ a s => a = ra ∧ Post x ra t₀ s)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      TripleAt ((_root_.Executable.labels cenv).label l)
        (fun s => T x ra t₀ l s ∧ var l s = n) blk.body
        (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False)
        (fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x ra t₀ a s))
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hexit : ∀ x ra t₀ a s, Exit x ra t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ Post x ra t₀ st.1) (s, a) := by
      rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach_at (T x ra t) var (Exit x ra t) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit x ra t st.2 st.1 hst)

open MachineWP in
/-- `ProcSpec.of_cfg` with the blocks returning through `Post'`, a form of
the postcondition in the terms the exit block leaves (a frame as the cells
the code used, say), and `hpost` recovering the specification's `Post` from
it: the exit counterpart of `hpre`. -/
theorem Kraken.Executable.ProcSpec.of_cfg_post [CodeEnv] {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post :=
  Kraken.Executable.ProcSpec.of_cfg T var (fun x ra t₀ a s => a = ra ∧ Post' x ra t₀ s) hblocks
    hpre (by rintro x ra t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, hpost x a t₀ s h⟩)
    hp hwf hpl

open MachineWP in
/-- `ProcSpec.of_cfg_post` with the precondition at the entry state in hand
for the blocks and for `hpost`: facts about the entry (the stack pointer's
headroom, say) need not be carried through the table. -/
theorem Kraken.Executable.ProcSpec.of_cfg_post_pre [CodeEnv] {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData), Pre x ra t₀ → ∀ l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Pre x ra t₀ → Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var (fun a s => a = ra ∧ Post' x ra t s)
    (hblocks x ra t ht) hp hwf hpl t (hpre x ra t ht)
  exact eventually_trans _ _ _ _ h (fun st hst =>
    Eventually.done _ ⟨hst.1, hpost x ra t st.1 ht hst.2⟩)

open MachineWP in
/-- `ProcSpec.of_cfg` for the continuation form: the table and the exits
mention the continuation `K` instead of a logical variable; the default exit
is the return into `K`. -/
theorem Kraken.Executable.ProcSpecK.of_cfg [CodeEnv] {p p' : Program} {l₀ : Label}
    {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (T : Int64 → (MachineData → Prop) → MachineData → Label → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (Exit : Int64 → (MachineData → Prop) → MachineData → Int64 → MachineData → Prop :=
      fun ra K _ a s => a = ra ∧ K s)
    (hblocks : ∀ (ra : Int64) (K : MachineData → Prop) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T ra K t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T ra K t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T ra K t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit ra K t₀ a s ⦄)
    (hpre : ∀ ra K t, Spec ra K t → T ra K t l₀ t)
    (hexit : ∀ ra K t₀ a s, Exit ra K t₀ a s →
      Eventually cenv.instrStep (fun st => st.2 = ra ∧ K st.1) (s, a) := by
      rintro ra K t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label l₀) Spec := by
  intro ra K t ht
  have h := MachineWP.cfg_reach (T ra K t) var (Exit ra K t) (hblocks ra K t) hp hwf hpl t
    (hpre ra K t ht)
  exact eventually_trans _ _ _ _ h (fun st hst => hexit ra K t st.2 st.1 hst)

open MachineWP in
/-- The block obligations of a table with an existential in front, `∃ x, W x ∧
T x l s`, from the obligations at each witness `x` (with `W x` in hand): the
blocks are proved as if `x` were a logical variable, and the exits of the
witness's table are mapped into the common exit `Exit'`. This is how a
`ProcSpecK` whose `Spec` quantifies the caller's data existentially is
established from blocks stated in that data (`ProcSpecK.of_cfg` with the
table `fun ra K t₀ l s => ∃ x, W ra K t₀ x ∧ T ra t₀ x l s`). -/
theorem MachineWP.cfg_blocks_exists [CodeEnv] {β : Type} {p : Program}
    (T : β → Label → MachineData → Prop) (W : β → Prop) (var : Label → MachineData → Nat)
    (Exit : β → Int64 → MachineData → Prop) (Exit' : Int64 → MachineData → Prop)
    (hblocks : ∀ x, W x → ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit x a s ⦄)
    (hexit : ∀ x, W x → ∀ a s, Exit x a s → Exit' a s) :
    ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => (∃ x, W x ∧ T x l s) ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => (∃ x, W x ∧ T x l' s) ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome
          ∧ (∃ x, W x ∧ T x l' s) ∧ Program.EdgeLt p var l n l' s) a s ∨ Exit' a s ⦄ := by
  intro l blk hblk n
  refine Triple.intro fun s ⟨⟨x, hw, ht⟩, hv⟩ => ?_
  have h := (hblocks x hw l blk hblk n).le_wp s ⟨ht, hv⟩
  rw [MachineWP.wp_eq] at h ⊢
  refine Executable.wp_mono ?_ ?_ h
  · intro s' hq
    revert hq
    cases blk.next with
    | some l' => exact fun hq => ⟨⟨x, hw, hq.1⟩, hq.2⟩
    | none => exact fun hq => hq
  · rintro a s' (⟨l', hl, hsome, ht', he⟩ | hex)
    · exact Or.inl ⟨l', hl, hsome, ⟨x, hw, ht'⟩, he⟩
    · exact Or.inr (hexit x hw a s' hex)

open MachineWP in
/-- `ProcSpec.of_cfg_post` for a `ProcSpecK` whose `Spec` quantifies the
caller's data existentially: `Spec ra K t` gives a witness `x` with `W ra K t
x` (the data's side conditions, and the continuation's: `∀ s', Post' x ra t s'
→ K s'`) and the entry `T x ra t l₀ t`. The table and the exit are stated in
`x` as a logical variable, so the block obligations are the ones of the ghost
style, verbatim, with `W` in hand (a recursive procedure's bound lives there). -/
theorem Kraken.Executable.ProcSpecK.of_cfg_exists [CodeEnv] {p p' : Program} {l₀ : Label}
    {β : Type} {Spec : Int64 → (MachineData → Prop) → MachineData → Prop}
    (T : β → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : β → Int64 → MachineData → MachineData → Prop)
    (W : Int64 → (MachineData → Prop) → MachineData → β → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : β) (ra : Int64) (K : MachineData → Prop) (t₀ : MachineData),
      W ra K t₀ x → ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ ra K t, Spec ra K t → ∃ x, W ra K t x ∧ T x ra t l₀ t)
    (hpost : ∀ ra K t₀ x, W ra K t₀ x → ∀ s, Post' x ra t₀ s → K s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label l₀) Spec :=
  Kraken.Executable.ProcSpecK.of_cfg
    (fun ra K t₀ l s => ∃ x, W ra K t₀ x ∧ T x ra t₀ l s) var
    (fun ra K _ a s => a = ra ∧ K s)
    (fun ra K t₀ => MachineWP.cfg_blocks_exists (fun x l s => T x ra t₀ l s) (W ra K t₀) var
      (fun x a s => a = ra ∧ Post' x ra t₀ s) (fun a s => a = ra ∧ K s)
      (fun x hw => hblocks x ra K t₀ hw)
      (fun x hw a s h => ⟨h.1, hpost ra K t₀ x hw s h.2⟩))
    hpre (by rintro ra K t₀ a s ⟨rfl, h⟩; exact Eventually.done _ ⟨rfl, h⟩) hp hwf hpl

-- Smoke test: the walk steps a placed fragment through the registered specs.
set_option mvcgen.warning false in
open MachineWP in
example [CodeEnv] :
    ⦃ fun (_ : MachineData) => True ⦄
      ([Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low .rax .W64)) (.imm (.int64 1))))] : Program)
    ⦃ fun _ s => s.regs.rax.toNat = 1 ⦄ := by
  vcgen simplifying_assumptions with finish

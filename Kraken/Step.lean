/-
The machine's step relation, and procedure specifications over it.

`instrStep` runs one instruction of the ambient code; `Eventually instrStep`
(`Kraken.OmniSemantics`) is the run. A procedure specification `ProcSpec`
says that a run entered at an address reaches the return address with a
postcondition — a proposition about the executable alone, in these terms and
nothing else. This file is the interface between a procedure's proof and its
callers and linker: a caller or a linker imports this; how a body is shown to
meet its `ProcSpec` is a separate matter (`Kraken.MachineWP`'s `wp` and
`ProcSpec.of_cfg_post`, or any other method that concludes `Eventually`).
-/
import Kraken.SegmentExtract

open Kraken

/-! ## The ambient code -/

/-- The ambient executable. -/
class CodeEnv where
  env : _root_.Executable

/-- The ambient code. -/
abbrev cenv [CodeEnv] : Kraken.Executable Directive := CodeEnv.env

/- Upstream marks `Executable.labels` reducible for the kstep pipeline. The
grind patterns of the spec dictionary key on `labels` as a stable head, so it
is semireducible here and in every file that consumes the dictionary. -/
set_option allowUnsafeReducibility true in
attribute [semireducible] _root_.Executable.labels

/-! ## The step relation

`instrStep` runs exactly the cell at the current pc: the machine's own
interpreter, with the fall-through and jump continuations both stopping. It
refines kraken's `straightlineStep`, which runs a whole segment burst, into
the granularity the per-instruction rules need. -/

/-- The cells at an address, past the labels that share it. A label occupies
no bytes, so several cells sit at one address; the machine runs the first one
that is not a label. -/
def Kraken.Executable.codeAt (e : Kraken.Executable Directive) (pc : Int64) : List (Directive × Nat) :=
  (e.directivesFromAddress pc).dropWhile (fun c => c.1.isLabel)

/-- Running the cell `(d, z)` at `st`: either every resolution falls through,
into `post` at the address behind the cell, or every resolution jumps, into
`post` at the target. Each disjunct poisons the other continuation, which is
the shape `Directive.interp_sound` consumes. -/
def Kraken.Executable.stepAt (e : Kraken.Executable Directive) (d : Directive) (z : Nat) (st : MachineState)
    (post : @Post MachineState) : Prop :=
  (@Directive.interp (_root_.Executable.labels e) d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun s' => .done (s', 0)) (fun _ _ => .unimplemented "jump")).All
    (fun m => post (m.1, st.2 + .ofNat z))
  ∨ (@Directive.interp (_root_.Executable.labels e) d st.1 (.mk st.2 (st.2 + .ofNat z))
      (fun _ => .unimplemented "fallthrough") (fun pc' s' => .done (s', pc'))).All post

/-- One instruction of the ambient code, run from `st`. -/
def Kraken.Executable.instrStep (e : Kraken.Executable Directive) (st : MachineState) (post : @Post MachineState) :
    Prop :=
  ∃ d z rest, e.codeAt st.2 = (d, z) :: rest ∧ e.stepAt d z st post

/-! ## The stack at a call -/

/-- The state a call leaves behind: the return address on the stack. -/
def MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - Width.W64.bytesv),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes ra.toBitVec.toInt }

/-- The address the stack top holds. -/
def MachineData.retAddr (t : MachineData) : Option Int64 :=
  (Mem.loadInt t.dmem (t.regs.get64 .rsp) Width.W64.bytes).map
    (fun i => Int64.ofBitVec (BitVec.ofInt Width.W64.bits i))

@[grind =] theorem MachineData.retAddr_eq (t : MachineData) :
    t.retAddr = (Mem.loadInt t.dmem (t.regs.get64 .rsp) Width.W64.bytes).map
      (fun i => Int64.ofBitVec (BitVec.ofInt Width.W64.bits i)) := rfl

@[grind =] theorem MachineData.regs_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - Width.W64.bytesv) := rfl

@[grind =] theorem MachineData.dmem_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
      Width.W64.bytes ra.toBitVec.toInt := rfl

/-- Registers after the push, read directly: `rsp` moved by a word, the rest
as they were. (`regs_pushRa` with `get64_set64` says the same in two steps,
through a `UInt64` field; `grind` reaches the bitvector there only as a
`toNat`, which does not merge the address with the cells of the caller's
tree.) -/
@[grind =] theorem MachineData.get64_pushRa (s : MachineData) (ra : Int64) (r : Reg64) :
    (s.pushRa ra).regs.get64 r =
      if r = .rsp then s.regs.get64 .rsp - Width.W64.bytesv else s.regs.get64 r := by
  simp [MachineData.pushRa]

/-! ## Procedures by specification

`call_spec` takes the callee's text. A procedure that calls one that is not
yet verified — itself, or its partner in a mutual recursion — needs the callee
as a *specification* instead. `ProcSpec` is that: a proposition about the
executable alone, so it can be assumed by one proof and established by
another, and be the subject of an induction.

The specification is stated at the callee's entry state `t` and the address
`ra` the run must reach. Nothing in it mentions the stack: how `ra` is handed
over is part of `Pre` (`t.retAddr = some ra` under the SysV convention; a
register, under another), and `Post` relates `t` to the exit state however
the convention has it. A tail call `jmp f` is a run that reaches `ra` through
`f`, so it is covered by `f`'s `ProcSpec` at the same `ra`.

Two forms. `ProcSpec` carries a logical variable `x : α` (the argument, the
caller's memory frame) that a call site instantiates. `ProcSpecK` packs the
logical variables inside `Spec`, existentially, with the continuation `K` the
run must end in, in the style of `fun_spec_from_label`. They are
interderivable (`ProcSpec.toK`); the examples show both. -/

/-- A run of `e` entered at `entry` in a state `t` with `Pre x ra t` reaches
`ra` in a state `s'` with `Post x ra t s'`. -/
def Kraken.Executable.ProcSpec (e : Kraken.Executable Directive) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually e.instrStep (fun st => st.2 = ra ∧ Post x ra t st.1) (t, entry)

/-- The continuation form: `Spec ra K t` is what the procedure asks of its
entry state `t` for a run that reaches `ra` in a state satisfying `K`. -/
def Kraken.Executable.ProcSpecK (e : Kraken.Executable Directive) (entry : Int64)
    (Spec : Int64 → (MachineData → Prop) → MachineData → Prop) : Prop :=
  ∀ (ra : Int64) (K : MachineData → Prop) (t : MachineData), Spec ra K t →
    Eventually e.instrStep (fun st => st.2 = ra ∧ K st.1) (t, entry)

theorem Kraken.Executable.ProcSpec.toK {e : Kraken.Executable Directive} {entry : Int64}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : e.ProcSpec entry Pre Post) :
    e.ProcSpecK entry (fun ra K t => ∃ x, Pre x ra t ∧ ∀ s', Post x ra t s' → K s') := by
  rintro ra K t ⟨x, hpre, hk⟩
  exact eventually_weaken _ _ _ _ (fun st ⟨ha, hp⟩ => ⟨ha, hk _ hp⟩) (h x ra t hpre)

theorem Kraken.Executable.ProcSpecK.toGhost {e : Kraken.Executable Directive} {entry : Int64}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : e.ProcSpecK entry (fun ra K t => ∃ x, Pre x ra t ∧ ∀ s', Post x ra t s' → K s')) :
    e.ProcSpec entry Pre Post :=
  fun x ra t hpre => h ra (Post x ra t) t ⟨x, hpre, fun _ hp => hp⟩

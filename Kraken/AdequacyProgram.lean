/-
Whole-program adequacy: the `execDirs` driver against the baseline
`Directives.interpM`.

The baseline threads the program counter functionally, running each directive at
`.mk pc (pc+sz)` and returning the final `pc`. The driver threads `rip` through
the `StateT`, sets `curSize := sz` on the reader so the position range read for an
instruction is that same `.mk pc (pc+sz)`, and advances `rip` by `sz`. Under a
per-directive adequacy hypothesis (each directive's encoded step equals its
baseline step), the fold of the two agrees.
-/
import Kraken.Adequacy

open Std.WP

set_option linter.unusedSimpArgs false

namespace Kraken

/-- Baseline single directive, lifted: read the environment and `rip`, then run
the directive at the position range `.mk pc (pc+sz)`. -/
def liftDir {D : Type} (d : Directive) (sz : Nat) : X64M D Unit := do
  let env ← read
  let pc ← getThe Int64
  liftMachine (d.interpM env.labels (.mk pc (pc + Int64.ofNat sz)))

/-- Baseline directive list, lifted: each directive's baseline step in sequence,
`rip` advancing by the encoded size, mirroring the driver's own recursion. -/
def liftDirs {D : Type} (ds : List (Directive × Nat)) : X64M D Unit :=
  match ds with
  | [] => pure ()
  | (d, sz) :: ds => do
    liftDir d sz
    modifyThe Int64 (· + Int64.ofNat sz)
    liftDirs ds

/-- On a label the driver's step matches the baseline's: both leave the state
untouched. -/
theorem liftDir_label {D} (l : Label) (sz : Nat) :
    (withCurSize sz (execDir (.label l)) : X64M D Unit)
      = liftDir (.label l) sz := by
  funext env rip s
  simp only [execDir, liftDir, Directive.interpM, lm_pure, withCurSize, withReader_apply, read_apply,
    getThe_apply, pure_apply]

/-- On an encoded 64-bit instruction the driver's step matches the baseline's,
given the operation is adequate. The `withReader` sets `curSize := sz`, so
the range read is `.mk pc (pc+sz)`, the one the baseline supplies. -/
theorem liftDir_instr {D} (op : Operation .W64) (sz : Nat)
    (hop : (Op.exec op : X64M D Unit) = liftBaseline op) :
    (withCurSize sz (execDir (.instr (.regular .W64 .W64 op)))
        : X64M D Unit)
      = liftDir (.instr (.regular .W64 .W64 op)) sz := by
  funext env rip s
  simp only [execDir, liftDir, Directive.interpM, Instr.interpM, withCurSize, withReader_apply, hop,
    liftBaseline, read_apply, getThe_apply]
  rfl

/-- The fold: with each directive's step adequate, the driver equals the lifted
baseline over the whole list. -/
theorem execDirs_eq_liftDirs {D} (ds : List (Directive × Nat))
    (h : ∀ d sz, (d, sz) ∈ ds →
      (withCurSize sz (execDir d) : X64M D Unit) = liftDir d sz) :
    (execDirs ds : X64M D Unit) = liftDirs ds := by
  induction ds with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    have hhd := h d sz (by simp)
    have htl : ∀ d sz, (d, sz) ∈ tl →
        (withCurSize sz (execDir d) : X64M D Unit) = liftDir d sz :=
      fun d sz hmem => h d sz (by simp [hmem])
    simp only [execDirs, liftDirs, hhd, ih htl]

/-- Lifted baseline of a straightline segment: from the current `rip`, run the
lifted baseline of the directives at that address. -/
def liftStraightlineFrom {D : Type} (e : _root_.Executable) : X64M D Unit := do
  let pc ← getThe Int64
  liftDirs (e.directivesFromAddress pc)

/-- A straightline segment of the control-flow driver equals its lifted baseline
whenever the directives at that address are encoded. This is the body each fuel
step of `execProgram` runs, so it carries the driver's per-segment adequacy. -/
theorem execStraightlineFrom_eq {D} (e : _root_.Executable)
    (h : ∀ pc d sz, (d, sz) ∈ e.directivesFromAddress pc →
      (withCurSize sz (execDir d) : X64M D Unit) = liftDir d sz) :
    (execStraightlineFrom e : X64M D Unit) = liftStraightlineFrom e := by
  simp only [execStraightlineFrom, liftStraightlineFrom]
  congr 1
  funext pc
  exact execDirs_eq_liftDirs _ (h pc)

/-- Lifted baseline control-flow driver: the fuel-bounded loop that catches a
jump and resumes at the target, built from lifted baseline segments. -/
def liftProgram {D : Type} (e : _root_.Executable) : Nat → X64M D Unit
  | 0 => pure ()
  | fuel + 1 =>
    tryCatch (liftStraightlineFrom e) fun exc =>
      match exc with
      | .jump pc => do modifyThe Int64 (fun _ => pc); liftProgram e fuel
      | exc => throw exc

/-- Whole-run control-flow adequacy: the k-fold driver equals the lifted baseline
driver at every fuel, whenever the reachable directives are encoded. A jump is
caught identically on both sides, so the fuel induction closes by congruence. -/
theorem execProgram_eq_liftProgram {D} (e : _root_.Executable) (fuel : Nat)
    (h : ∀ pc d sz, (d, sz) ∈ e.directivesFromAddress pc →
      (withCurSize sz (execDir d) : X64M D Unit) = liftDir d sz) :
    (execProgram e fuel : X64M D Unit) = liftProgram e fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [execProgram, liftProgram, execStraightlineFrom_eq e h, ih]; rfl

/-! ## End-to-end: a concrete encoded program

A laid-out straightline program of encoded directives, discharged directive by
directive against `Op.exec`'s per-instruction corollaries. -/

def demoProg : List (Directive × Nat) :=
  [ (.instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.imm (.int64 5)))), 7),
    (.instr (.regular .W64 .W64 (.dec (.reg (.low .rax .W64)))), 3),
    (.label "done", 0) ]

theorem demoProg_adequate : (execDirs demoProg : X64M Unit Unit) = liftDirs demoProg := by
  apply execDirs_eq_liftDirs
  intro d sz hmem
  simp only [demoProg, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact liftDir_instr _ _ (Op.exec_mov_reg_imm_adequate _ _)
  · exact liftDir_instr _ _ (Op.exec_dec_reg_adequate _)
  · exact liftDir_label _ _

/-! ## End-to-end: a loop through the k-fold driver

A backward-jumping loop `loop: dec %rax; jnz loop`. Every address the driver can
reach lands in a suffix of the program, so each reachable directive is one of the
three, each adequate. The k-fold driver on the loop equals the lifted baseline at
every fuel. -/

def loopExe : _root_.Executable :=
  ( 0,
    [ (.label "loop", 0),
      (.instr (.regular .W64 .W64 (.dec (.reg (.low .rax .W64)))), 3),
      (.instr (.regular .W64 .W64 (.jcc .nz "loop")), 2) ] )

theorem loopExe_adequate (fuel : Nat) :
    (execProgram loopExe fuel : X64M Unit Unit) = liftProgram loopExe fuel := by
  apply execProgram_eq_liftProgram
  intro pc d sz hmem
  simp only [loopExe, Executable.directivesFromAddress] at hmem
  have hmem2 : (d, sz) ∈ (Kraken.Executable.withAddresses
      ((0 : Int64), [((Directive.label "loop" : Directive), 0),
        (.instr (.regular .W64 .W64 (.dec (.reg (.low .rax .W64)))), 3),
        (.instr (.regular .W64 .W64 (.jcc .nz "loop")), 2)])).map (·.2) :=
    List.map_subset _ (List.dropWhile_subset _) hmem
  rw [Kraken.Executable.withAddresses_map_snd] at hmem2
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem2
  rcases hmem2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact liftDir_label _ _
  · exact liftDir_instr _ _ (Op.exec_dec_reg_adequate _)
  · exact liftDir_instr _ _ (Op.exec_jcc_adequate _ _)

end Kraken

import SbrClient.Machine.Frame
import Iris.ProgramLogic.Language

namespace SbrClient
open Kraken Iris.ProgramLogic

/-- Fixed decoded code and a designated final halt boundary. Library return
addresses remain ordinary instruction addresses. -/
structure Model where
  code : Kraken.Executable Directive
  halt : Int64
  halt_empty : code.codeAt halt = []

/-- Thread-local execution state, carried by `Expr.run`. The Iris language
state contains only the shared byte heap; immutable code is supplied by `Model`. -/
structure CPU where
  regs : Reg64s
  zmms : RegZmms
  status : StatusFlags
  pc : Int64

/-- Combine the expression's CPU and the shared heap into Kraken's state.
This is a semantic representation change, not a runtime memory copy. -/
def CPU.pack (c : CPU) (m : Mem 64) : MachineState :=
  (⟨c.regs, c.zmms, c.status, m⟩, c.pc)

/-- Recover the thread-local component after a native instruction. The step
rule separately installs `s.1.dmem` as the new shared heap. -/
def CPU.ofMachine (s : MachineState) : CPU :=
  ⟨s.1.regs, s.1.zmms, s.1.status, s.2⟩

@[simp] theorem CPU.pack_ofMachine (s : MachineState) :
    (CPU.ofMachine s).pack s.1.dmem = s := by cases s; rfl

@[simp] theorem CPU.ofMachine_pack (c : CPU) (m : Mem 64) :
    CPU.ofMachine (c.pack m) = c := rfl

inductive Expr (M : Model) where
  | run (cpu : CPU)
  | done (cpu : CPU)
  | fault

def Expr.toVal {M : Model} : Expr M → Option CPU
  | .done c => some c
  | _ => none

/-- Instruction outcomes are physical steps. A fault becomes a stuck
expression; it cannot disappear from safety reasoning. -/
inductive Step (M : Model) : Expr M × Mem 64 → List Empty → Expr M × Mem 64 × List (Expr M) → Prop
  | execute {c m s} (hne : c.pc ≠ M.halt) (h : InstrOutcome M.code (c.pack m) (some s)) :
      Step M (.run c, m) [] (.run (CPU.ofMachine s), s.1.dmem, [])
  | fault {c m} (hne : c.pc ≠ M.halt) (h : InstrOutcome M.code (c.pack m) none) :
      Step M (.run c, m) [] (.fault, m, [])
  | halt {c m} (heq : c.pc = M.halt) : Step M (.run c, m) [] (.done c, m, [])

instance (M : Model) : Language (Expr M) (Mem 64) Empty CPU where
  toVal := Expr.toVal
  ofVal := .done
  coe_of_toVal_eq_some := by intro e v h; cases e <;> cases h; rfl
  toVal_coe _ := rfl
  primStep := Step M
  val_stuck h := by cases h <;> rfl

/-- The pure producer semantics: every instruction is safe and the selected
successor is an outcome of the exact Kraken interpreter. -/
inductive LocalStep (M : Model) : Expr M × Mem 64 → Expr M × Mem 64 → Prop
  | execute {c m s} (hne : c.pc ≠ M.halt)
      (safe : (instruction M.code (c.pack m)).All (fun _ => True))
      (h : InstrOutcome M.code (c.pack m) (some s)) :
      LocalStep M (.run c, m) (.run (CPU.ofMachine s), s.1.dmem)
  | halt {c m} (heq : c.pc = M.halt) : LocalStep M (.run c, m) (.done c, m)


/-- The local byte map is a disjoint part of physical memory. -/
def Agrees (p σ : Mem 64) : Prop := ∃ f, Disjoint p f ∧ σ = p.union f

/-- An owned-map replacement with an unchanged physical frame. -/
def Change (p σ p' σ' : Mem 64) : Prop :=
  ∃ f, Disjoint p f ∧ σ = p.union f ∧ Disjoint p' f ∧ σ' = p'.union f ∧ SameDomain p p'

theorem all_own_outcomes {t : Effects} (h : t.All (fun _ => True)) :
    t.All (fun s => Outcome t (some s)) := by
  apply (all_iff_outcomes _ _).mpr
  intro r hr
  obtain ⟨s, rfl, _⟩ := hr.of_all h
  exact ⟨s, rfl, hr⟩

theorem local_progress {M : Model} {e : Expr M} {p σ : Mem 64}
    (ha : Agrees p σ) (hl : ∃ c, LocalStep M (e, p) c) :
    PrimStep.Reducible (e, σ) := by
  obtain ⟨f, hd, rfl⟩ := ha
  obtain ⟨c', hl⟩ := hl
  cases hl with
  | @execute c _ _ hne safe hr =>
    obtain ⟨r, hr⟩ := Outcome.exists (instruction M.code (c.pack (p.union f)))
    obtain ⟨s, heq, hs⟩ := hr.of_all (instruction_frame hd safe)
    subst r
    exact ⟨[], .run (CPU.ofMachine s), s.1.dmem, [], Step.execute hne hr⟩
  | halt heq => exact ⟨[], _, _, [], Step.halt heq⟩

theorem local_simulate {M : Model} {e e' : Expr M} {p σ σ' : Mem 64}
    {obs : List Empty} {efs : List (Expr M)}
    (ha : Agrees p σ) (hl : ∃ c, LocalStep M (e, p) c)
    (hs : Step M (e, σ) obs (e', σ', efs)) :
    obs = [] ∧ efs = [] ∧ ∃ p', LocalStep M (e, p) (e', p') ∧ Change p σ p' σ' := by
  obtain ⟨f, hd, rfl⟩ := ha
  obtain ⟨c', hl⟩ := hl
  cases hl with
  | @execute c m s hne safe hr =>
    have framed := instruction_frame hd (all_own_outcomes safe)
    cases hs with
    | execute hne' hout =>
      obtain ⟨st, heq, t, ht, hdom, hdis, hp⟩ := hout.of_all framed
      cases heq
      cases ht
      refine ⟨rfl, rfl, t.1.dmem, LocalStep.execute hne safe hp, ?_⟩
      exact ⟨f, hd, rfl, hdis, rfl, hdom⟩
    | fault hne' hout =>
      obtain ⟨_, heq, _⟩ := hout.of_all framed
      cases heq
    | halt heq => exact (hne heq).elim
  | @halt c m heq =>
    cases hs with
    | execute hne _ | fault hne _ => exact (hne heq).elim
    | halt _ =>
      exact ⟨rfl, rfl, p, LocalStep.halt heq, f, hd, rfl, hd, rfl, fun _ => Iff.rfl⟩

end SbrClient

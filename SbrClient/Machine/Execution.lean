import Kraken.Step
import Kraken.InterpSound

/-! Relational instruction semantics for the exact Kraken interpreter.
Fault outcomes are explicit: they must not disappear when a nondeterministic
instruction also has a successful outcome. Access annotations follow the
same ordinary-memory policy as upstream `Effects.All`. -/
namespace SbrClient
open Kraken

inductive Outcome : Effects → Option MachineState → Prop
  | done (s) : Outcome (.done s) (some s)
  | unimplemented (msg) : Outcome (.unimplemented msg) none
  | unaligned (a w) : Outcome (.gp_unaligned a w) none
  | trap (what) : Outcome (.trap what) none
  | nonmemLoad (m a w k) : Outcome (.nonmem_load m a w k) none
  | nonmemStore {w : Width} (m a) (v : w.type) (k) : Outcome (.nonmem_store m a v k) none
  | undefined {α} [NondetSupportingType α] (k : α → Effects) (v : α) {r}
      (h : Outcome (k v) r) : Outcome (.undefined k) r
  | read (a w k) {r} (h : Outcome (k ()) r) : Outcome (.require_read_access a w k) r
  | write (a w k) {r} (h : Outcome (k ()) r) : Outcome (.require_write_access a w k) r
  | execute (p k) {r} (h : Outcome (k ()) r) : Outcome (.require_exec_access p k) r

theorem Outcome.exists (t : Effects) : ∃ r, Outcome t r := by
  induction t with
  | done s => exact ⟨_, .done s⟩
  | unimplemented msg => exact ⟨_, .unimplemented msg⟩
  | gp_unaligned a w => exact ⟨_, .unaligned a w⟩
  | trap what => exact ⟨_, .trap what⟩
  | nonmem_load m a w k _ => exact ⟨_, .nonmemLoad m a w k⟩
  | nonmem_store m a v k _ => exact ⟨_, .nonmemStore m a v k⟩
  | @undefined α inst k ih =>
      let v : α := @NondetSupportingType.from_hash α inst 0
      obtain ⟨r, hr⟩ := ih v
      exact ⟨r, .undefined k v hr⟩
  | require_read_access a w k ih =>
      obtain ⟨r, hr⟩ := ih ()
      exact ⟨r, .read a w k hr⟩
  | require_write_access a w k ih =>
      obtain ⟨r, hr⟩ := ih ()
      exact ⟨r, .write a w k hr⟩
  | require_exec_access p k ih =>
      obtain ⟨r, hr⟩ := ih ()
      exact ⟨r, .execute p k hr⟩

theorem Outcome.of_all {t : Effects} {r : Option MachineState} {Q : MachineState → Prop}
    (h : Outcome t r) (hq : t.All Q) : ∃ s, r = some s ∧ Q s := by
  induction h with
  | done s => exact ⟨s, rfl, hq⟩
  | unimplemented | unaligned | trap | nonmemLoad | nonmemStore => cases hq
  | undefined k v _ ih => exact ih (hq v)
  | read _ _ _ _ ih | write _ _ _ _ ih | execute _ _ _ ih => exact ih hq

theorem all_iff_outcomes (t : Effects) (Q : MachineState → Prop) :
    t.All Q ↔ ∀ r, Outcome t r → ∃ s, r = some s ∧ Q s := by
  constructor
  · intro h r hr
    exact hr.of_all h
  · induction t with
    | done s =>
        intro h
        obtain ⟨s', hs, hq⟩ := h _ (.done s)
        cases hs
        exact hq
    | unimplemented msg => intro h; obtain ⟨_, h, _⟩ := h _ (.unimplemented msg); cases h
    | gp_unaligned a w => intro h; obtain ⟨_, h, _⟩ := h _ (.unaligned a w); cases h
    | trap what => intro h; obtain ⟨_, h, _⟩ := h _ (.trap what); cases h
    | nonmem_load m a w k _ => intro h; obtain ⟨_, h, _⟩ := h _ (.nonmemLoad m a w k); cases h
    | nonmem_store m a v k _ => intro h; obtain ⟨_, h, _⟩ := h _ (.nonmemStore m a v k); cases h
    | undefined k ih => exact fun h v => ih v (fun r hr => h r (.undefined k v hr))
    | require_read_access a w k ih => exact fun h => ih () (fun r hr => h r (.read a w k hr))
    | require_write_access a w k ih => exact fun h => ih () (fun r hr => h r (.write a w k hr))
    | require_exec_access p k ih => exact fun h => ih () (fun r hr => h r (.execute p k hr))

/-- Exactly one decoded instruction, with both real successor channels. -/
def instruction (e : Kraken.Executable Directive) (s : MachineState) : Effects :=
  match e.codeAt s.2 with
  | [] => .unimplemented "no instruction at PC"
  | (d, z) :: _ =>
      @Directive.interp (_root_.Executable.labels e) d s.1 (.mk s.2 (s.2 + .ofNat z))
        (fun t => .done (t, s.2 + .ofNat z)) (fun pc t => .done (t, pc))

def InstrOutcome (e : Kraken.Executable Directive) (s : MachineState)
    (r : Option MachineState) : Prop := Outcome (instruction e s) r

theorem instrStep_all {e : Kraken.Executable Directive} {s : MachineState}
    {Q : MachineState → Prop} (h : e.instrStep s Q) : (instruction e s).All Q := by
  letI : Labels := _root_.Executable.labels e
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  unfold instruction
  rw [hcode]
  exact Directive.interp_sound (fun _ h => h) (fun _ h => h) hstep

theorem instrStep_outcome {e : Kraken.Executable Directive} {s : MachineState}
    {Q : MachineState → Prop} (h : e.instrStep s Q) {r} (hr : InstrOutcome e s r) :
    ∃ t, r = some t ∧ Q t := hr.of_all (instrStep_all h)

theorem instrStep_progress {e : Kraken.Executable Directive} {s : MachineState}
    {Q : MachineState → Prop} (h : e.instrStep s Q) :
    ∃ t, InstrOutcome e s (some t) ∧ Q t := by
  obtain ⟨r, hr⟩ := Outcome.exists (instruction e s)
  obtain ⟨t, rfl, ht⟩ := instrStep_outcome h hr
  exact ⟨t, hr, ht⟩

/-- A library return sentinel is outside its instruction map. -/
def ReturnBoundary (e : Kraken.Executable Directive) (ra : Int64) : Prop := e.codeAt ra = []

theorem boundary_no_step {e : Kraken.Executable Directive} {ra : Int64}
    (h : ReturnBoundary e ra) (s : MachineData) (Q : MachineState → Prop) :
    ¬ e.instrStep (s, ra) Q := by
  rintro ⟨d, z, rest, hc, _⟩
  rw [h] at hc
  cases hc

/-- At an actual return boundary, eventual postconditions hold on the first
arrival. This condition is necessary: plain Eventually alone says nothing
about an earlier visit to a PC at which the machine can keep executing. -/
theorem eventually_at_boundary {e : Kraken.Executable Directive} {ra : Int64}
    {Q : MachineState → Prop} (h : ReturnBoundary e ra) (s : MachineData)
    (cert : Eventually e.instrStep Q (s, ra)) : Q (s, ra) := by
  cases cert with
  | done _ hq => exact hq
  | step _ mid hs _ => exact (boundary_no_step h s mid hs).elim

end SbrClient

/-
Minimal standalone reproducer: `vcgen` loops when told to unfold a `liftM` of an
anonymous state transformer. No dependencies beyond `Std`.

`liftMach c = liftM (fun s => match c s.machine with
   | .ok a m => .ok a { s with machine := m } | .error e m => .error e { s with machine := m })`
lifts an anonymous `Sys → EStateM.Result` function through `StateT` and `ReaderT`.
Handing `liftMach` to `vcgen`'s unfold list makes `vcgen` diverge: it never
returns a goal. (This mirrors `Kraken`'s `liftMachine`, the encoding↔baseline
bridge that blocks outlining `Op.*` memory cases onto the baseline primitives.)

It is a non-termination, not linear slowness, and it is specific to `vcgen`:

  vcgen [prog]            (liftMach absent)  -> ~1s, "No spec found for program liftMach"
  vcgen [prog, liftMach]                     -> 20s+ TIMEOUT, no error emitted
  mvcgen [prog, liftMach] (same everything)  -> ~0s, terminates leaving `wp⟦monadLift …⟧`

Three facts pin the diagnosis:
  * `maxHeartbeats 100000` never trips. A path merely elaborating a large term
    exhausts a 100k budget in well under a second and reports "maxHeartbeats
    exceeded"; the work is not ticking heartbeats, as an unguarded Meta loop does
    not.
  * `mvcgen` on the identical goal terminates (it stops at `wp⟦monadLift …⟧`); only
    the experimental `vcgen` diverges.
  * The inner computation is irrelevant: lifting a bare `get` loops just as a
    `get; match … | throw` does. The trigger is unfolding `liftMach` itself.

`getM`/`modifyM`-style lifts of *named* ops (`getThe`/`modify`) that `vcgen` has
specs for step in one shot; `liftMach` lifts the anonymous `fun s => match …`, and
stepping that is what diverges.

To reproduce: change the `vcgen [prog]` below to `vcgen [prog, liftMach]` and run
  timeout 20 lake env lean vcgen-liftMachine-loop-mwe.lean
Left as `sorry` here so a plain run terminates.
-/
import Std.Tactic.Do
import Std.Internal.Do

open Std.Internal.Do

set_option mvcgen.warning false
set_option maxHeartbeats 100000

structure Sys where
  machine : Nat

abbrev Base := EStateM Unit Nat
abbrev M := ReaderT Unit (StateT Unit (EStateM Unit Sys))

/-- Lift a `Base` computation over `Sys.machine`, via the anonymous state
transformer `fun s => match c s.machine with ...`. -/
def liftMach {α} (c : Base α) : M α :=
  liftM (m := EStateM Unit Sys) (fun s => match c s.machine with
    | .ok a m => .ok a { s with machine := m }
    | .error e m => .error e { s with machine := m })

def prog : M Unit := do
  let v ← liftMach (get : Base Nat)
  liftMach (set v)

section
variable (Q : Unit → Unit → Unit → Sys → Prop) (E : Unit → Sys → Prop)

theorem prog_spec : ⦃ fun r n s => Q () r n s ⦄ prog ⦃ Q; E ⦄ := by
  -- Reproduce the loop by adding `, liftMach`:  vcgen [prog, liftMach]
  -- Left as `sorry` so running this file terminates.
  sorry

end

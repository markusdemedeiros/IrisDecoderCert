import Kraken.X64.Examples.EvenOddGhost.Spec

/-!
# `even`/`odd`: the specifications, existential style

The same two procedures as `EvenOddGhost/`, specified in the *continuation*
form `ProcSpecK`: what the caller knows — the argument `n` and its memory
`R` — is quantified existentially inside the specification, and the run must
end in a continuation `K`, in the style of `fun_spec_from_label`. The
conditions themselves (`CallPre`, `CallPost`, the cells, the reservation) are
those of `EvenOddGhost/Spec.lean`, imported, so the two styles differ only in
how the data is bound:

* ghost: `EvenSpec n := ProcSpec entry (EvenPre n) (EvenPost n)`, `R` a logical
  variable fixed by the call site (`call_proc_spec_at R`), `n` an index;
* existential: `EvenSpecK N := ProcSpecK entry (EvenK N)` with
  `EvenK N ra K t := ∃ n R, n < N ∧ EvenPre n R ra t ∧ ∀ s', EvenPost n R ra t s' → K s'`.

The bound `N` is what the recursion is on: `EvenSpecK N` is the specification
of `even` *for arguments below `N`*, a single proposition, so that `Odd.lean`
can assume `EvenSpecK N` and prove `OddSpecK (N + 1)`, and `Link.lean` runs an
ordinary induction on `N` (the ghost version needs strong induction on `n`).
`EvenSpecK_all` in `Link.lean` then drops the bound.

What the existential costs: at the call the caller must *produce* the
witnesses (`⟨n - 1, R', …⟩`). What it buys: the specification reads as one
sentence, and the induction is on a bound, not an index. Establishing the
spec is the same work as in the ghost style: `ProcSpecK.of_cfg_exists`
(`MachineWP`, general) states the blocks in the witness as a logical
variable, and the tables are those of the ghost proofs.
-/

open Kraken
open Kraken.SysV
open Mem

namespace Kraken.Examples.EvenOddExistential

open EvenOddGhost

/-- `even` for arguments below `N`, continuation form. -/
abbrev EvenK (N : Nat) (ra : Int64) (K : MachineData → Prop) (t : MachineData) : Prop :=
  ∃ (n : Nat) (R : Mem 64 → Prop), n < N ∧ EvenPre n R ra t ∧ ∀ s', EvenPost n R ra t s' → K s'

/-- `odd` for arguments below `N`, continuation form. -/
abbrev OddK (N : Nat) (ra : Int64) (K : MachineData → Prop) (t : MachineData) : Prop :=
  ∃ (n : Nat) (R : Mem 64 → Prop), n < N ∧ OddPre n R ra t ∧ ∀ s', OddPost n R ra t s' → K s'

abbrev EvenSpecK [CodeEnv] (N : Nat) : Prop :=
  cenv.ProcSpecK ((_root_.Executable.labels cenv).label "even") (EvenK N)

abbrev OddSpecK [CodeEnv] (N : Nat) : Prop :=
  cenv.ProcSpecK ((_root_.Executable.labels cenv).label "odd") (OddK N)

end Kraken.Examples.EvenOddExistential

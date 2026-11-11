import Kraken.X64.Examples.EvenOddExistential.Even
import Kraken.X64.Examples.EvenOddExistential.Odd

/-!
# `even`/`odd`, existential style: tying the two proofs

`Even.lean` proves `even` below `N + 1` from `odd` below `N`; `Odd.lean` the
converse. Since each specification is one proposition about *all* arguments
below a bound, an ordinary induction on the bound discharges both at once
(the ghost version, indexed by the argument, needs strong induction); the
base case is vacuous. `EvenSpecK_all` drops the bound: the specification of
`even` with nothing but the calling convention and the parity in it.

What remains assumed is the placement of both bodies (`PlacedIn`), as in the
ghost version.
-/

open Kraken

namespace Kraken.Examples.EvenOddExistential

open EvenOddGhost

variable [CodeEnv]

/-- Both specifications, below every bound. -/
theorem even_odd_specK (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body)
    (N : Nat) : EvenSpecK N ∧ OddSpecK N := by
  induction N with
  | zero => exact ⟨fun _ _ _ ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _),
      fun _ _ _ ⟨_, _, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | succ N ih => exact ⟨Even.even_specK hpe N ih.2, Odd.odd_specK hpo N ih.1⟩

/-- `even`, with the bound gone: for a caller with any argument `n` and any
memory `R`, a run from `EvenPre n R` ends at `ra` in the continuation. -/
theorem EvenSpecK_all (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label "even")
      (fun ra K t => ∃ (n : Nat) (R : Mem 64 → Prop),
        EvenPre n R ra t ∧ ∀ s', EvenPost n R ra t s' → K s') :=
  fun ra K t ⟨n, R, hpre, hK⟩ =>
    (even_odd_specK hpe hpo (n + 1)).1 ra K t ⟨n, R, Nat.lt_succ_self n, hpre, hK⟩

theorem OddSpecK_all (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body) :
    cenv.ProcSpecK ((_root_.Executable.labels cenv).label "odd")
      (fun ra K t => ∃ (n : Nat) (R : Mem 64 → Prop),
        OddPre n R ra t ∧ ∀ s', OddPost n R ra t s' → K s') :=
  fun ra K t ⟨n, R, hpre, hK⟩ =>
    (even_odd_specK hpe hpo (n + 1)).2 ra K t ⟨n, R, Nat.lt_succ_self n, hpre, hK⟩

end Kraken.Examples.EvenOddExistential

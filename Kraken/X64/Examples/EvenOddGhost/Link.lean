import Kraken.X64.Examples.EvenOddGhost.Even
import Kraken.X64.Examples.EvenOddGhost.Odd

/-!
# `even`/`odd`: tying the two proofs

`Even.lean` proves `even` at `n` from `odd` at every `m < n`; `Odd.lean` the
converse. Strong induction on `n` discharges both assumptions at once: at `n`,
the induction hypothesis gives both specs at every smaller argument.

What remains assumed is the placement of both bodies in the ambient code
(`PlacedIn`): the two may sit anywhere, in either order, with anything
between; each `call` reaches its target through the target's `ProcSpec`,
which is stated at the target's address.
-/

open Kraken

namespace Kraken.Examples.EvenOddGhost

variable [CodeEnv]

/-- Both specifications, at every argument. -/
theorem even_odd_spec (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body) (n : Nat) : EvenSpec n ∧ OddSpec n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    exact ⟨Even.even_spec hpe n (fun m hm => (ih m hm).2),
      Odd.odd_spec hpo n (fun m hm => (ih m hm).1)⟩

theorem even_spec_all (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body) (n : Nat) : EvenSpec n := (even_odd_spec hpe hpo n).1

theorem odd_spec_all (hpe : Program.PlacedIn Even.even_body)
    (hpo : Program.PlacedIn Odd.odd_body) (n : Nat) : OddSpec n := (even_odd_spec hpe hpo n).2

end Kraken.Examples.EvenOddGhost

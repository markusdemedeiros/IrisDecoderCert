import Lean

/-!
# `info_off`: stop collecting info trees for the rest of a tactic proof

The command-line driver keeps the info tree of every command until the end of the file (it is
needed for the `.ilean`). For the large generated block proofs these trees hold every goal of
every tactic step and dominate the peak memory of a module (GainAsm: 9.2 → 6.1 GB).

`info_off` as the first tactic of a proof disables info-tree collection for the remaining
tactics of that proof. It does not change the proof term, the elaborated statement, or error
reporting: errors are messages, not info-tree nodes. The only loss is editor information inside
the proof (hover, go-to-definition from the `.ilean`) and linters that read info trees (e.g.
unused `simp` arguments) going silent there.
-/

namespace Kraken

open Lean Elab Tactic in
/-- Disable info-tree collection for the rest of this tactic proof (memory; see module doc). -/
elab "info_off" : tactic => modifyInfoState fun s => { s with enabled := false }

end Kraken

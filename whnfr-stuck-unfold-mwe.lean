/-
`whnfR` unfolds a `@[reducible]` definition by cases although its scrutinee is a
metavariable, returning a stuck `match` where the input was a compact constant
application. Smart unfolding exists to refuse exactly this; it is not consulted
on the reducible-transparency path.

Consequence: the stuck match is stored wherever the caller keeps the whnf result
(unification assignments, instance arguments). When the metavariable is assigned
later, the stranded match ships in the term; nothing re-normalizes stored
subterms, and downstream consumers that read the position syntactically (such as
`bv_decide` reading a `BitVec` width) see an opaque match instead of a literal.

Output of this file:

  reducible def: whnfR (bits ?w) = match ?w with ... ; after ?w := W64: stranded match; whnfR again = 64
  plain def:     whnfR (bits ?w) = bits ?w           ; after ?w := W64: bits W64      ; whnfR again = bits W64

The expected behavior for the reducible case is that of the plain case: leave
`bits ?w` folded while the scrutinee is unknown.
-/
import Lean
open Lean Meta Elab

inductive W | W8 | W64

@[reducible] def bitsR : W → Nat | .W8 => 8 | .W64 => 64
def bitsD : W → Nat | .W8 => 8 | .W64 => 64

run_cmd Command.liftTermElabM do
  for (label, bits) in [("reducible def", ``bitsR), ("plain def", ``bitsD)] do
    let w ← mkFreshExprMVar (mkConst ``W)
    let e := mkApp (mkConst bits) w
    let e' ← whnfR e
    w.mvarId!.assign (mkConst ``W.W64)
    let stranded ← instantiateMVars e'
    logInfo m!"{label}: whnfR (bits ?w) = {e'} ; stranded = {stranded} ; whnfR again = {← whnfR stranded}"

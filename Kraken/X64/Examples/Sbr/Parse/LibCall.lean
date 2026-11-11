import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# Callee contracts for the parser proofs

`memcpy(dst, src, n)` with its effect: the destination holds the source bytes afterwards.
(`MemcpySpec` of `Spec.lean` only keeps the two regions owned, which is all `ff_aac_sbr_apply`
needs; a parser routine that builds a table by copying needs the values.) Assumed, like the
other library contracts: it is what the C standard specifies for non-overlapping regions.
`memset(dst, c, n)` likewise: `dst[n]` holds `n` copies of `(unsigned char)c` afterwards
(`MemsetSpec` of `Spec.lean` only keeps the region owned).
-/

open Kraken Kraken.SysV Mem
open Kraken.Examples.Sbr

namespace Kraken.Examples.Sbr.Parse

/-- The bound of a reservation one cell down a tree (`CallPre`'s shape). -/
theorem res_le_mid {d : Nat} {r : BitVec 64} {A K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ A ⋆ (Reserve d r ⋆ K)) : d ≤ r.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h1, _⟩ := h; exact h1.1

/-- The bound of a reservation anywhere in a tree, through an `ac` rearrangement. -/
theorem res_le_of {d : Nat} {r : BitVec 64} {P K : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ P) (e : P = Reserve d r ⋆ K) : d ≤ r.toNat :=
  Reserve.le_head (e ▸ h)

variable [CodeEnv]

end Kraken.Examples.Sbr.Parse

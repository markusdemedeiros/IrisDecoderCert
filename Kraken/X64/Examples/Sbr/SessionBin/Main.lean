import Kraken.X64.Examples.Sbr.SessionBin.SDec
import Kraken.X64.Examples.Sbr.SessionBin.SConfig
import Kraken.X64.Examples.Sbr.SessionBin.SApply
import Kraken.X64.Examples.Sbr.SessionBin.SUsac

/-!
# A decoding session over the binary

`Session.lean`'s session with its abstract parse step replaced by the machine-code
specifications of the linked binary's entries. The values `SV` (the model's `Args` and the raw
scalars `HV`) evolve by `Step`: `ff_aac_sbr_decode_extension` (`DecOut`),
`ff_aac_sbr_decode_usac_data` (`UsacOut`), `ff_aac_sbr_config_usac` (`sbr_turnoff`),
`ff_aac_sbr_apply` (`ApplyRel`), and the caller's changes (`FrameStep`); `SReach (σInit i)` are
the values reachable from the allocation.

* `sreach_init_inv` (`Inv.lean`): every reachable value satisfies `SInv` (`MI`, `PsInv` of
  `ps->common`, `bs_limiter_bands ≤ 3`, the array lengths) and, with the flag set, `LiveC`;
  `sreach_wf`: `SbrWF` at every reachable value with the flag set.
* `session_dec` (`SDec.lean`), `session_usac` (`SUsac.lean`), `session_config`
  (`SConfig.lean`), `session_apply` (`SApply.lean`): at every reachable value, a call of the
  entry from a state with the caller's frame (`DecFrame`, `UsacFrame`, `ConfigFrame`,
  `ApplyFrame`) over the element `SessW` returns to the caller with the element at reachable
  values (flag set; for `decode_usac_data`, set iff it returns `0`), or (decode_extension,
  decode_usac_data) stops at a safe stop (`abort`, the bounds trap of `read_sbr_envelope`).

The theorems are over the placed texts (`SessPlaced`) and the assumed external contracts and
data facts (`SessionAssumed`); they use no axioms beyond Lean's standard ones.
-/

namespace Kraken.Examples.Sbr.SessionBin

end Kraken.Examples.Sbr.SessionBin

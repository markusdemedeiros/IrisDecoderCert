import Kraken.X64.Examples.Sbr.Parse.DecExtSpec

/-!
# `ff_aac_sbr_decode_extension`: the postcondition gives `SbrWF`

`DecOut` (the values a return leaves) implies `ff_aac_sbr_apply`'s decoder invariant `SbrWF`
(with `GridInv` and `Inv2`), through `ParseModel.wf_of_mi`.
-/

open Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

theorem decOut_wf {PI : List UInt8 → Prop} {X : XA} {d' : DS} (h : DecOut PI X d') :
    SbrWF d'.a ∧ GridInv d'.a ∧ ParseModel.Inv2 d'.a :=
  wf_of_mi (s := (d'.a, d'.h)) h.1 h.2.1

end Kraken.Examples.Sbr.DecExt

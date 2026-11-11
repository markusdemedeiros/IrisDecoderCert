/-
Register add chain: `vcgen -internalize simplifying_assumptions`, discharged by
`bv_decide`. One bitvector identity survives to the discharge, since the chain
carries a symbolic start.

Open this file to run the benchmark; the `#eval` reports stepping, discharge and
kernel time at each size.
-/
import Cases.AddChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize simplifying_assumptions)) `(tactic| bv_decide) [40, 160, 640]

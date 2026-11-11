/-
Register decrement chain: `vcgen -internalize simplifying_assumptions`,
discharged by `bv_decide`.

Open this file to run the benchmark; the `#eval` reports stepping, discharge and
kernel time at each size.
-/
import Cases.DecChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval runBenchUsingTactic ``DecChain.Goal [``DecChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [40, 160, 640]

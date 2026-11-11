/-
Carry chain: `vcgen -internalize simplifying_assumptions`. The program is ground,
so the state-simplification pass reaches the postcondition's value and closes the
goal during stepping, leaving no verification condition for `bv_decide`.

Open this file to run the benchmark; the `#eval` reports stepping and kernel time
at each size.
-/
import Cases.AdcChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval runBenchUsingTactic ``AdcChain.Goal [``AdcChain.prog, ``AdcChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [40, 160, 640]

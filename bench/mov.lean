/-
Immediate-mov chain: `vcgen -internalize simplifying_assumptions`, discharged by
`grind`. Each state read is projected through the `Sys` wrapper the framework
adds.

Open this file to run the benchmark; the `#eval` reports stepping and kernel time
at each size.
-/
import Cases.MovChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval runBenchUsingTactic ``MovChain.Goal [``MovChain.chain]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| grind) [40, 160]

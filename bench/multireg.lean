/-
Multi-register chain: `n` rounds of fifteen register writes each,
`vcgen -internalize simplifying_assumptions`. The program is ground, so the
state-simplification pass closes the goal during stepping.

Open this file to run the benchmark; the `#eval` reports stepping and kernel time
at each size.
-/
import Cases.MultiReg
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval runBenchUsingTactic ``MultiReg.Goal [``MultiReg.chain, ``MultiReg.round]
  `(tactic| vcgen -internalize simplifying_assumptions) `(tactic| bv_decide) [4, 10, 40]

/-
Where the time goes on one workload: the register add chain, stepped and
discharged four ways.

`sorry` discharge isolates the cost of the stepping certificate alone; the other
rows add the cost of a checked proof. Without `simplifying_assumptions` the state
literals reach the discharge unfolded, so the fold has to run over the finished
verification condition instead of over each state as it is produced.

Open this file to run the benchmark; each `#eval` reports one pipeline.
-/
import Cases.AddChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP

#eval do IO.println "== stepping only, no state simplification"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| sorry) [40, 160, 640]

#eval do IO.println "== stepping only, with state simplification"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize simplifying_assumptions)) `(tactic| sorry) [40, 160, 640]

#eval do IO.println "== kfold_discharge, no state simplification"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize)) `(tactic| kfold_discharge) [40, 160, 640]

#eval do IO.println "== bv_decide, with state simplification"; (← IO.getStdout).flush
#eval runBenchUsingTactic ``AddChain.Goal [``AddChain.chain]
  `(tactic| (intro k; vcgen -internalize simplifying_assumptions)) `(tactic| bv_decide) [40, 160, 640]

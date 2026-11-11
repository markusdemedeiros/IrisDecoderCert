/-
Carry chain through the deep embedding. Open this file to run the benchmark;
the `#eval` reports stepping and kernel time at each size.
-/
import Cases.SegAdcChain
import Driver
import KrakenTactics.Fold

set_option mvcgen.warning false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Lean Order Parser Meta Elab Tactic Sym Std Std.WP
open MachineWP

#eval runBenchUsingTactic ``SegAdcChain.Goal [``SegAdcChain.prog, ``SegAdcChain.chain]
  `(tactic| (intro _; vcgen -internalize simplifying_assumptions)) `(tactic| grind)
  [40, 160, 640]

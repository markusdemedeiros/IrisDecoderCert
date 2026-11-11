/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/X64M.lean re-encodes it as the straightline interpreter
`Operation.interpM` over `MachineM` (error-state on `MachineData`), and builds
the spec monad `X64M D` on top: a reader over the label/layout environment and
a state over `rip`, above the error-state machine over `Sys D` (the CPU state
plus a device state that a jump preserves). The per-constructor `Op.*` actions
and `@[spec]` triples (Kraken/X64M.lean, Kraken/Device.lean) are discharged by
the `Std.WP` weakest-precondition `vcgen` pipeline and the `easm` memory
tactic (Kraken/Easm.lean). Kraken/MachineWP.lean is the machine-founded
weakest precondition on the deep embedding.
-/

import Kraken.X64.Semantics
import Kraken.X64.Parser
import Kraken.X64.OmniSemantics
import Kraken.X64.Sep
import Kraken.Specs
import Kraken.X64M
import Kraken.Device
import Kraken.Tactics
import Kraken.Easm
import Kraken.Step
import Kraken.MachineWP
import Kraken.Rules.GenericMem
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.IndirectCall
import Kraken.Rules.ScalarFloat
import Kraken.Rules.LeafLemmas
import Kraken.Rules.CfgList
import Kraken.Rules.CallFrame
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.SepWP
import Kraken.SepSpecs
import Kraken.SepFrameProc
import Kraken.SysV
import Kraken.X64.Examples.SepAluMem
import Kraken.X64.Examples.SepDynamicStack
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.Dsp.NegOdd64
import Kraken.X64.Examples.Sbr.Dsp.Sum64x5
import Kraken.X64.Examples.Sbr.Dsp.SumSquare
import Kraken.X64.Examples.Sbr.Dsp.QmfPreShuffle
import Kraken.X64.Examples.Sbr.Dsp.QmfPostShuffle
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintNeg
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintBfly
import Kraken.X64.Examples.Sbr.Dsp.Autocorrelate
import Kraken.X64.Examples.Sbr.Dsp.HfGen
import Kraken.X64.Examples.Sbr.Dsp.HfGFilt
import Kraken.X64.Examples.Sbr.Dsp.HfApplyNoise
import Kraken.X64.Examples.Sbr.Dsp
import Kraken.X64.Examples.Sbr.QmfSynthesis
import Kraken.X64.Examples.Sbr.LfGen
import Kraken.X64.Examples.Sbr.HfInverseFilter
import Kraken.X64.Examples.Sbr.XGen
import Kraken.X64.Examples.Sbr.HfAssemble
import Kraken.X64.Examples.Sbr.DequantFloat

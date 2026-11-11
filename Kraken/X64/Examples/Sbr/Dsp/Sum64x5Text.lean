import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `Sum64x5`: the program text

The program text (`body`) of `Dsp/Sum64x5.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.Sum64x5

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_sum64x5_sse:
    lea 0x100(%rdi),%rsi
ff_sbr_sum64x5_sse.loop:
    movaps (%rdi),%xmm0
    movaps 0x10(%rdi),%xmm2
    movaps 0x100(%rdi),%xmm1
    movaps 0x110(%rdi),%xmm3
    addps 0x200(%rdi),%xmm0
    addps 0x210(%rdi),%xmm2
    addps 0x300(%rdi),%xmm1
    addps 0x310(%rdi),%xmm3
    addps 0x400(%rdi),%xmm0
    addps 0x410(%rdi),%xmm2
    addps %xmm1,%xmm0
    addps %xmm3,%xmm2
    movaps %xmm0,(%rdi)
    movaps %xmm2,0x10(%rdi)
    add $0x20,%rdi
    cmp %rsi,%rdi
    jne ff_sbr_sum64x5_sse.loop
ff_sbr_sum64x5_sse.done:
    ret
")

end Kraken.Examples.Sbr.Sum64x5

import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `NegOdd64`: the program text

The program text (`body`) of `Dsp/NegOdd64.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.NegOdd64

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_neg_odd_64_sse:
    lea 0x100(%rdi),%rsi
ff_sbr_neg_odd_64_sse.loop:
    movaps (%rdi),%xmm0
    movaps 0x10(%rdi),%xmm1
    movaps 0x20(%rdi),%xmm2
    movaps 0x30(%rdi),%xmm3
    xorps ps_mask2(%rip),%xmm0
    xorps ps_mask2(%rip),%xmm1
    xorps ps_mask2(%rip),%xmm2
    xorps ps_mask2(%rip),%xmm3
    movaps %xmm0,(%rdi)
    movaps %xmm1,0x10(%rdi)
    movaps %xmm2,0x20(%rdi)
    movaps %xmm3,0x30(%rdi)
    add $0x40,%rdi
    cmp %rsi,%rdi
    jne ff_sbr_neg_odd_64_sse.loop
ff_sbr_neg_odd_64_sse.done:
    ret
")

end Kraken.Examples.Sbr.NegOdd64

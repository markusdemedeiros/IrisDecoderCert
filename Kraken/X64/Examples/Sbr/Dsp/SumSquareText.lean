import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `SumSquare`: the program text

The program text (`body`) of `Dsp/SumSquare.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.SumSquare

def body : Program := parse("
ff_sbr_sum_square_sse:
    mov %esi,%edx
    xorps %xmm0,%xmm0
    xorps %xmm1,%xmm1
    sar $0x3,%rdx
    je ff_sbr_sum_square_sse.prepare
ff_sbr_sum_square_sse.loop:
    movups (%rdi),%xmm2
    movups 0x10(%rdi),%xmm3
    movups 0x20(%rdi),%xmm4
    movups 0x30(%rdi),%xmm5
    mulps %xmm2,%xmm2
    mulps %xmm3,%xmm3
    mulps %xmm4,%xmm4
    mulps %xmm5,%xmm5
    addps %xmm2,%xmm0
    addps %xmm3,%xmm1
    addps %xmm4,%xmm0
    addps %xmm5,%xmm1
    add $0x40,%rdi
    dec %rdx
    jne ff_sbr_sum_square_sse.loop
ff_sbr_sum_square_sse.prepare:
    and $0x7,%rsi
    sar $1,%rsi
    je ff_sbr_sum_square_sse.end
ff_sbr_sum_square_sse.endloop:
    movups (%rdi),%xmm2
    add $0x10,%rdi
    mulps %xmm2,%xmm2
    dec %rsi
    addps %xmm2,%xmm0
    jne ff_sbr_sum_square_sse.endloop
ff_sbr_sum_square_sse.end:
    addps %xmm1,%xmm0
    movhlps %xmm0,%xmm2
    addps %xmm2,%xmm0
    movss %xmm0,%xmm1
    shufps $0x1,%xmm0,%xmm0
    addss %xmm1,%xmm0
ff_sbr_sum_square_sse.done:
    ret
")

end Kraken.Examples.Sbr.SumSquare

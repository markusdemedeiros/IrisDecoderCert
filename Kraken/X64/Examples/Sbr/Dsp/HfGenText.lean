import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `HfGen`: the program text

The program text (`body`) of `Dsp/HfGen.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.HfGen

/-- The routine from the object file, labels prefixed with the symbol, the
`.rodata` operand as `ps_mask(%rip)`, a label `….pre` before the first load,
the final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_hf_gen_sse:
    movlps (%rcx),%xmm2
    movlps (%rdx),%xmm1
    shufps $0x0,%xmm0,%xmm0
    mulps %xmm0,%xmm2
    mulps %xmm0,%xmm1
    mulps %xmm0,%xmm2
    movaps %xmm1,%xmm3
    movaps %xmm2,%xmm4
    movslq %r8d,%r8
    movslq %r9d,%r9
    sub %r9,%r8
    lea (%rdi,%r9,8),%rdi
    lea -0x10(%rsi,%r9,8),%rsi
    shl $0x3,%r8
ff_sbr_hf_gen_sse.pre:
    movaps (%rsi,%r8,1),%xmm0
    shufps $0x55,%xmm3,%xmm3
    shufps $0x55,%xmm4,%xmm4
    xorps ps_mask(%rip),%xmm3
    shufps $0x0,%xmm1,%xmm1
    shufps $0x0,%xmm2,%xmm2
    xorps ps_mask(%rip),%xmm4
ff_sbr_hf_gen_sse.loop2:
    movups 0x8(%rsi,%r8,1),%xmm7
    movaps %xmm0,%xmm6
    movaps %xmm7,%xmm5
    shufps $0xb1,%xmm0,%xmm0
    shufps $0xb1,%xmm7,%xmm7
    mulps %xmm4,%xmm0
    mulps %xmm3,%xmm7
    mulps %xmm2,%xmm6
    mulps %xmm1,%xmm5
    addps %xmm0,%xmm7
    movaps 0x10(%rsi,%r8,1),%xmm0
    addps %xmm0,%xmm7
    addps %xmm5,%xmm6
    addps %xmm6,%xmm7
    movaps %xmm7,(%rdi,%r8,1)
    add $0x10,%r8
    jne ff_sbr_hf_gen_sse.loop2
ff_sbr_hf_gen_sse.done:
    ret
")

end Kraken.Examples.Sbr.HfGen

import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `Autocorrelate`: the program text

The program texts (`body`, `body3`) of `Dsp/Autocorrelate.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.Autocorrelate

def body : Program := parse("
ff_sbr_autocorrelate_sse:
    sub $0x28,%rsp
    mov $0x128,%edx
    add %rdx,%rdi
    neg %rdx
    movlps (%rdi,%rdx,1),%xmm5
    movlhps %xmm5,%xmm5
    movlps 0x8(%rdi,%rdx,1),%xmm7
    movlps 0x10(%rdi,%rdx,1),%xmm1
    shufps $0x14,%xmm7,%xmm7
    shufps $0x14,%xmm1,%xmm1
    movaps %xmm5,%xmm3
    mulps %xmm7,%xmm3
    movaps %xmm5,%xmm4
    mulps %xmm5,%xmm4
    mulps %xmm1,%xmm5
    movaps %xmm3,(%rsp)
    movaps %xmm4,0x10(%rsp)
    add $0x8,%rdx
    movlps 0x10(%rdi,%rdx,1),%xmm2
    movlhps %xmm7,%xmm7
    shufps $0x14,%xmm2,%xmm2
    movaps %xmm7,%xmm6
    mulps %xmm1,%xmm6
    movaps %xmm7,%xmm4
    mulps %xmm2,%xmm4
    mulps %xmm7,%xmm7
    addps %xmm4,%xmm5
    nop
    nop
ff_sbr_autocorrelate_sse.loop:
    add $0x8,%rdx
    movlps 0x10(%rdi,%rdx,1),%xmm0
    movlhps %xmm1,%xmm1
    shufps $0x14,%xmm0,%xmm0
    movaps %xmm1,%xmm3
    mulps %xmm2,%xmm3
    movaps %xmm1,%xmm4
    mulps %xmm0,%xmm4
    mulps %xmm1,%xmm1
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm1,%xmm7
    add $0x8,%rdx
    movlps 0x10(%rdi,%rdx,1),%xmm1
    movlhps %xmm2,%xmm2
    shufps $0x14,%xmm1,%xmm1
    movaps %xmm2,%xmm3
    mulps %xmm0,%xmm3
    movaps %xmm2,%xmm4
    mulps %xmm1,%xmm4
    mulps %xmm2,%xmm2
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm2,%xmm7
    add $0x8,%rdx
    movlps 0x10(%rdi,%rdx,1),%xmm2
    movlhps %xmm0,%xmm0
    shufps $0x14,%xmm2,%xmm2
    movaps %xmm0,%xmm3
    mulps %xmm1,%xmm3
    movaps %xmm0,%xmm4
    mulps %xmm2,%xmm4
    mulps %xmm0,%xmm0
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm0,%xmm7
    jl ff_sbr_autocorrelate_sse.loop
ff_sbr_autocorrelate_sse.tail:
    movlhps %xmm1,%xmm1
    mulps %xmm1,%xmm2
    mulps %xmm1,%xmm1
    addps %xmm6,%xmm2
    addps %xmm7,%xmm1
    addps (%rsp),%xmm6
    addps 0x10(%rsp),%xmm7
    xorps ps_mask3(%rip),%xmm2
    xorps ps_mask3(%rip),%xmm5
    xorps ps_mask3(%rip),%xmm6
    movaps %xmm2,%xmm3
    shufps $0x88,%xmm5,%xmm2
    shufps $0xdd,%xmm5,%xmm3
    addps %xmm3,%xmm2
    movaps %xmm7,%xmm4
    shufps $0x88,%xmm6,%xmm7
    shufps $0xdd,%xmm6,%xmm4
    addps %xmm4,%xmm7
    movss %xmm1,%xmm0
    shufps $0x1,%xmm1,%xmm1
    addss %xmm0,%xmm1
    movaps %xmm2,(%rsi)
    movhps %xmm7,0x18(%rsi)
    movss %xmm7,0x28(%rsi)
    movss %xmm1,0x10(%rsi)
    add $0x28,%rsp
ff_sbr_autocorrelate_sse.done:
    ret
")

def body3 : Program := parse("
ff_sbr_autocorrelate_sse3:
    sub $0x28,%rsp
    mov $0x128,%edx
    add %rdx,%rdi
    neg %rdx
    movddup (%rdi,%rdx,1),%xmm5
    movsd 0x8(%rdi,%rdx,1),%xmm7
    movsd 0x10(%rdi,%rdx,1),%xmm1
    shufps $0x14,%xmm7,%xmm7
    shufps $0x14,%xmm1,%xmm1
    movaps %xmm5,%xmm3
    mulps %xmm7,%xmm3
    movaps %xmm5,%xmm4
    mulps %xmm5,%xmm4
    mulps %xmm1,%xmm5
    movaps %xmm3,(%rsp)
    movaps %xmm4,0x10(%rsp)
    add $0x8,%rdx
    movsd 0x10(%rdi,%rdx,1),%xmm2
    movlhps %xmm7,%xmm7
    shufps $0x14,%xmm2,%xmm2
    movaps %xmm7,%xmm6
    mulps %xmm1,%xmm6
    movaps %xmm7,%xmm4
    mulps %xmm2,%xmm4
    mulps %xmm7,%xmm7
    addps %xmm4,%xmm5
    nop
    nop
ff_sbr_autocorrelate_sse3.loop:
    add $0x8,%rdx
    movsd 0x10(%rdi,%rdx,1),%xmm0
    movlhps %xmm1,%xmm1
    shufps $0x14,%xmm0,%xmm0
    movaps %xmm1,%xmm3
    mulps %xmm2,%xmm3
    movaps %xmm1,%xmm4
    mulps %xmm0,%xmm4
    mulps %xmm1,%xmm1
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm1,%xmm7
    add $0x8,%rdx
    movsd 0x10(%rdi,%rdx,1),%xmm1
    movlhps %xmm2,%xmm2
    shufps $0x14,%xmm1,%xmm1
    movaps %xmm2,%xmm3
    mulps %xmm0,%xmm3
    movaps %xmm2,%xmm4
    mulps %xmm1,%xmm4
    mulps %xmm2,%xmm2
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm2,%xmm7
    add $0x8,%rdx
    movsd 0x10(%rdi,%rdx,1),%xmm2
    movlhps %xmm0,%xmm0
    shufps $0x14,%xmm2,%xmm2
    movaps %xmm0,%xmm3
    mulps %xmm1,%xmm3
    movaps %xmm0,%xmm4
    mulps %xmm2,%xmm4
    mulps %xmm0,%xmm0
    addps %xmm3,%xmm6
    addps %xmm4,%xmm5
    addps %xmm0,%xmm7
    jl ff_sbr_autocorrelate_sse3.loop
ff_sbr_autocorrelate_sse3.tail:
    movlhps %xmm1,%xmm1
    mulps %xmm1,%xmm2
    mulps %xmm1,%xmm1
    addps %xmm6,%xmm2
    addps %xmm7,%xmm1
    addps (%rsp),%xmm6
    addps 0x10(%rsp),%xmm7
    xorps ps_mask3(%rip),%xmm2
    xorps ps_mask3(%rip),%xmm5
    xorps ps_mask3(%rip),%xmm6
    haddps %xmm5,%xmm2
    haddps %xmm6,%xmm7
    movshdup %xmm1,%xmm0
    addss %xmm0,%xmm1
    movaps %xmm2,(%rsi)
    movhps %xmm7,0x18(%rsi)
    movss %xmm7,0x28(%rsi)
    movss %xmm1,0x10(%rsi)
    add $0x28,%rsp
ff_sbr_autocorrelate_sse3.done:
    ret
")

end Kraken.Examples.Sbr.Autocorrelate

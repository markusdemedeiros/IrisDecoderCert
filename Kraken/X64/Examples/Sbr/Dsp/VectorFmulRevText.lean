import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `VectorFmulRev`: the program text

The program texts (`bodySse`, `bodyAvx`, `bodyAvx2`) of `Dsp/VectorFmulRev.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.VectorFmulRev

/-- `ff_vector_fmul_reverse_sse` from the object. -/
def bodySse : Program := parse("
ff_vector_fmul_reverse_sse:
    lea -0x20(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_reverse_sse.loop:
    movaps (%rdx),%xmm0
    movaps 0x10(%rdx),%xmm1
    shufps $0x1b,%xmm0,%xmm0
    shufps $0x1b,%xmm1,%xmm1
    mulps 0x10(%rsi,%rcx),%xmm0
    mulps (%rsi,%rcx),%xmm1
    movaps %xmm0,0x10(%rdi,%rcx)
    movaps %xmm1,(%rdi,%rcx)
    add $0x20,%rdx
    sub $0x20,%rcx
    jge ff_vector_fmul_reverse_sse.loop
ff_vector_fmul_reverse_sse.done:
    ret
")

/-- `ff_vector_fmul_reverse_avx` from the object. -/
def bodyAvx : Program := parse("
ff_vector_fmul_reverse_avx:
    lea -0x40(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_reverse_avx.loop:
    vmovaps 0x10(%rdx),%xmm0
    vinsertf128 $0x1,(%rdx),%ymm0,%ymm0
    vshufps $0x1b,%ymm0,%ymm0,%ymm0
    vmovaps 0x30(%rdx),%xmm1
    vinsertf128 $0x1,0x20(%rdx),%ymm1,%ymm1
    vshufps $0x1b,%ymm1,%ymm1,%ymm1
    vmulps 0x20(%rsi,%rcx),%ymm0,%ymm0
    vmulps (%rsi,%rcx),%ymm1,%ymm1
    vmovaps %ymm0,0x20(%rdi,%rcx)
    vmovaps %ymm1,(%rdi,%rcx)
    add $0x40,%rdx
    sub $0x40,%rcx
    jge ff_vector_fmul_reverse_avx.loop
ff_vector_fmul_reverse_avx.done:
    vzeroupper
    ret
")

/-- `ff_vector_fmul_reverse_avx2` from the object, with a free label `.lea`
behind the load of the mask `pd_reverse`. -/
def bodyAvx2 : Program := parse("
ff_vector_fmul_reverse_avx2:
    vmovaps pd_reverse(%rip),%ymm2
ff_vector_fmul_reverse_avx2.lea:
    lea -0x40(,%ecx,4),%rcx
    nop 8
    nop 7
ff_vector_fmul_reverse_avx2.loop:
    vpermps (%rdx),%ymm2,%ymm0
    vpermps 0x20(%rdx),%ymm2,%ymm1
    vmulps 0x20(%rsi,%rcx),%ymm0,%ymm0
    vmulps (%rsi,%rcx),%ymm1,%ymm1
    vmovaps %ymm0,0x20(%rdi,%rcx)
    vmovaps %ymm1,(%rdi,%rcx)
    add $0x40,%rdx
    sub $0x40,%rcx
    jge ff_vector_fmul_reverse_avx2.loop
ff_vector_fmul_reverse_avx2.done:
    vzeroupper
    ret
")

end Kraken.Examples.Sbr.VectorFmulRev

import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `VectorFmul`: the program text

The program texts (`bodySse`, `bodyAvx`) of `Dsp/VectorFmul.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.VectorFmul

/-- `ff_vector_fmul_sse` from the object. -/
def bodySse : Program := parse("
ff_vector_fmul_sse:
    lea -0x40(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_sse.loop:
    movaps (%rsi,%rcx),%xmm0
    movaps 0x10(%rcx,%rsi),%xmm1
    mulps (%rdx,%rcx),%xmm0
    mulps 0x10(%rcx,%rdx),%xmm1
    movaps %xmm0,(%rdi,%rcx)
    movaps %xmm1,0x10(%rcx,%rdi)
ff_vector_fmul_sse.loop2:
    movaps 0x20(%rcx,%rsi),%xmm0
    movaps 0x30(%rcx,%rsi),%xmm1
    mulps 0x20(%rcx,%rdx),%xmm0
    mulps 0x30(%rcx,%rdx),%xmm1
    movaps %xmm0,0x20(%rcx,%rdi)
    movaps %xmm1,0x30(%rcx,%rdi)
    sub $0x40,%rcx
    jge ff_vector_fmul_sse.loop
ff_vector_fmul_sse.done:
    ret
")

/-- `ff_vector_fmul_avx` from the object. -/
def bodyAvx : Program := parse("
ff_vector_fmul_avx:
    lea -0x40(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_avx.loop:
    vmovaps (%rsi,%rcx),%ymm0
    vmovaps 0x20(%rcx,%rsi),%ymm1
    vmulps (%rdx,%rcx),%ymm0,%ymm0
    vmulps 0x20(%rcx,%rdx),%ymm1,%ymm1
    vmovaps %ymm0,(%rdi,%rcx)
    vmovaps %ymm1,0x20(%rcx,%rdi)
    sub $0x40,%rcx
    jge ff_vector_fmul_avx.loop
ff_vector_fmul_avx.done:
    vzeroupper
    ret
")

end Kraken.Examples.Sbr.VectorFmul

import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `VectorFmulAdd`: the program text

The program texts (`bodySse`, `bodyAvx`, `bodyFma3`) of `Dsp/VectorFmulAdd.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.VectorFmulAdd

/-- `ff_vector_fmul_add_sse` from the object. -/
def bodySse : Program := parse("
ff_vector_fmul_add_sse:
    lea -0x20(,%r8d,4),%r8
    nop 7
ff_vector_fmul_add_sse.loop:
    movaps (%rsi,%r8),%xmm0
    movaps 0x10(%rsi,%r8),%xmm1
    mulps (%rdx,%r8),%xmm0
    mulps 0x10(%rdx,%r8),%xmm1
    addps (%rcx,%r8),%xmm0
    addps 0x10(%rcx,%r8),%xmm1
    movaps %xmm0,(%rdi,%r8)
    movaps %xmm1,0x10(%rdi,%r8)
    sub $0x20,%r8
    jge ff_vector_fmul_add_sse.loop
ff_vector_fmul_add_sse.done:
    ret
")

/-- `ff_vector_fmul_add_avx` from the object. -/
def bodyAvx : Program := parse("
ff_vector_fmul_add_avx:
    lea -0x40(,%r8d,4),%r8
    nop 7
ff_vector_fmul_add_avx.loop:
    vmovaps (%rsi,%r8),%ymm0
    vmovaps 0x20(%rsi,%r8),%ymm1
    vmulps (%rdx,%r8),%ymm0,%ymm0
    vmulps 0x20(%rdx,%r8),%ymm1,%ymm1
    vaddps (%rcx,%r8),%ymm0,%ymm0
    vaddps 0x20(%rcx,%r8),%ymm1,%ymm1
    vmovaps %ymm0,(%rdi,%r8)
    vmovaps %ymm1,0x20(%rdi,%r8)
    sub $0x40,%r8
    jge ff_vector_fmul_add_avx.loop
ff_vector_fmul_add_avx.done:
    vzeroupper
    ret
")

/-- `ff_vector_fmul_add_fma3` from the object. -/
def bodyFma3 : Program := parse("
ff_vector_fmul_add_fma3:
    lea -0x40(,%r8d,4),%r8
    nop 7
ff_vector_fmul_add_fma3.loop:
    vmovaps (%rsi,%r8),%ymm0
    vmovaps 0x20(%rsi,%r8),%ymm1
    vmovaps (%rcx,%r8),%ymm2
    vmovaps 0x20(%rcx,%r8),%ymm3
    vfmadd132ps (%rdx,%r8),%ymm2,%ymm0
    vfmadd132ps 0x20(%rdx,%r8),%ymm3,%ymm1
    vmovaps %ymm0,(%rdi,%r8)
    vmovaps %ymm1,0x20(%rdi,%r8)
    sub $0x40,%r8
    jge ff_vector_fmul_add_fma3.loop
ff_vector_fmul_add_fma3.done:
    vzeroupper
    ret
")

end Kraken.Examples.Sbr.VectorFmulAdd

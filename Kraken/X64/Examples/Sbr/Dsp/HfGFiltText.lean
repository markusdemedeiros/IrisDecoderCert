import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `HfGFilt`: the program text

The program text (`body`) of `Dsp/HfGFilt.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.HfGFilt

/-- The routine from the object file, labels prefixed with the symbol; its own
`.end` label is the final `ret`. -/
def body : Program := parse("
ff_sbr_hf_g_filt_sse:
    lea (%rsi,%r8,8),%rsi
    mov %rcx,%r9
    and $0xfc,%rcx
    lea (%rdx,%rcx,4),%rdx
    lea (%rdi,%rcx,8),%rdi
    neg %rcx
    je ff_sbr_hf_g_filt_sse.loop1
ff_sbr_hf_g_filt_sse.loop4:
    movlps (%rdx,%rcx,4),%xmm0
    movlps 0x8(%rdx,%rcx,4),%xmm1
    movlps (%rsi),%xmm2
    movlps 0x280(%rsi),%xmm3
    movhps 0x140(%rsi),%xmm2
    movhps 0x3c0(%rsi),%xmm3
    unpcklps %xmm0,%xmm0
    unpcklps %xmm1,%xmm1
    mulps %xmm2,%xmm0
    mulps %xmm3,%xmm1
    movups %xmm0,(%rdi,%rcx,8)
    movups %xmm1,0x10(%rdi,%rcx,8)
    add $0x500,%rsi
    add $0x4,%rcx
    jne ff_sbr_hf_g_filt_sse.loop4
    and $0x3,%r9
    je ff_sbr_hf_g_filt_sse.end
ff_sbr_hf_g_filt_sse.loop1:
    movss (%rdx),%xmm0
    movlps (%rsi),%xmm2
    unpcklps %xmm0,%xmm0
    mulps %xmm0,%xmm2
    movlps %xmm2,(%rdi)
    add $0x8,%rdi
    add $0x4,%rdx
    add $0x140,%rsi
    dec %r9
    jne ff_sbr_hf_g_filt_sse.loop1
ff_sbr_hf_g_filt_sse.end:
    ret
")

end Kraken.Examples.Sbr.HfGFilt

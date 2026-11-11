import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `QmfPreShuffle`: the program text

The program text (`body`) of `Dsp/QmfPreShuffle.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.QmfPreShuffle

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`), the two-store tail
behind `….tail`. -/
def body : Program := parse("
ff_sbr_qmf_pre_shuffle_sse2:
    mov $0x60,%ecx
    lea 0x84(%rdi),%rsi
    lea 0x100(%rdi),%rdx
    movdqa ff_ps_neg(%rip),%xmm5
ff_sbr_qmf_pre_shuffle_sse2.loop:
    movdqu (%rsi),%xmm0
    movdqu 0x10(%rsi),%xmm2
    movdqu 0x14(%rcx,%rdi,1),%xmm1
    movdqu 0x4(%rdi,%rcx,1),%xmm3
    pxor %xmm5,%xmm2
    pxor %xmm5,%xmm0
    pshufd $0x1b,%xmm2,%xmm2
    pshufd $0x1b,%xmm0,%xmm0
    movdqa %xmm2,%xmm4
    punpckldq %xmm3,%xmm2
    punpckhdq %xmm3,%xmm4
    movdqa %xmm0,%xmm3
    punpckldq %xmm1,%xmm0
    punpckhdq %xmm1,%xmm3
    movdqa %xmm2,(%rdx,%rcx,2)
    movdqa %xmm4,0x10(%rdx,%rcx,2)
    movdqa %xmm0,0x20(%rdx,%rcx,2)
    movdqa %xmm3,0x30(%rdx,%rcx,2)
    add $0x20,%rsi
    sub $0x20,%rcx
    jge ff_sbr_qmf_pre_shuffle_sse2.loop
ff_sbr_qmf_pre_shuffle_sse2.tail:
    movq (%rdi),%xmm2
    movq %xmm2,(%rdx)
ff_sbr_qmf_pre_shuffle_sse2.done:
    ret
")

end Kraken.Examples.Sbr.QmfPreShuffle

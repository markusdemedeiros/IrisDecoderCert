import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `QmfDeintBfly`: the program text

The program text (`body`) of `Dsp/QmfDeintBfly.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.QmfDeintBfly

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_qmf_deint_bfly_sse2:
    mov $0xe0,%r8d
    lea 0x100(%rdi),%rcx
ff_sbr_qmf_deint_bfly_sse2.loop:
    movdqa (%rsi,%r8,1),%xmm0
    movdqa (%rdx),%xmm1
    movdqa 0x10(%rsi,%r8,1),%xmm4
    movdqa 0x10(%rdx),%xmm5
    pshufd $0x1b,%xmm0,%xmm2
    pshufd $0x1b,%xmm1,%xmm3
    pshufd $0x1b,%xmm4,%xmm6
    pshufd $0x1b,%xmm5,%xmm7
    addps %xmm2,%xmm5
    subps %xmm7,%xmm0
    addps %xmm6,%xmm1
    subps %xmm3,%xmm4
    movdqa %xmm1,(%rcx)
    movdqa %xmm5,0x10(%rcx)
    movdqa %xmm0,(%rdi,%r8,1)
    movdqa %xmm4,0x10(%rdi,%r8,1)
    add $0x20,%rdx
    add $0x20,%rcx
    sub $0x20,%r8
    jge ff_sbr_qmf_deint_bfly_sse2.loop
ff_sbr_qmf_deint_bfly_sse2.done:
    ret
")

end Kraken.Examples.Sbr.QmfDeintBfly

import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `QmfDeintNeg`: the program text

The program text (`body`) of `Dsp/QmfDeintNeg.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.QmfDeintNeg

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_qmf_deint_neg_sse:
    mov $0xffffffffffffff80,%rcx
    lea 0x100(%rdi),%rdx
    add $0x70,%rdi
    add $0x100,%rsi
    movaps ff_ps_neg(%rip),%xmm3
ff_sbr_qmf_deint_neg_sse.loop:
    movaps (%rsi,%rcx,2),%xmm0
    movaps 0x10(%rsi,%rcx,2),%xmm1
    movaps %xmm0,%xmm2
    shufps $0x88,%xmm1,%xmm2
    shufps $0x77,%xmm0,%xmm1
    xorps %xmm3,%xmm2
    movaps %xmm1,(%rdi)
    movaps %xmm2,(%rdx,%rcx,1)
    sub $0x10,%rdi
    add $0x10,%rcx
    jl ff_sbr_qmf_deint_neg_sse.loop
ff_sbr_qmf_deint_neg_sse.done:
    ret
")

end Kraken.Examples.Sbr.QmfDeintNeg

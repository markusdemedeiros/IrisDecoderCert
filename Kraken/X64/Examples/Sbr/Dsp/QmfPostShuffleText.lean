import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `QmfPostShuffle`: the program text

The program text (`body`) of `Dsp/QmfPostShuffle.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.QmfPostShuffle

/-- The routine from the object file, labels prefixed with the symbol, three free
labels cutting the loop (`.step`, `.cmp`), the final `ret` behind `.done`. -/
def body : Program := parse("
ff_sbr_qmf_post_shuffle_sse:
    lea 0xf0(%rsi),%rdx
    movaps ff_ps_neg(%rip),%xmm3
ff_sbr_qmf_post_shuffle_sse.loop:
    movaps (%rsi),%xmm1
    movaps (%rdx),%xmm0
    xorps %xmm3,%xmm0
    shufps $0x1b,%xmm0,%xmm0
    movaps %xmm0,%xmm2
    unpcklps %xmm1,%xmm2
    unpckhps %xmm1,%xmm0
    movaps %xmm2,(%rdi)
    movaps %xmm0,0x10(%rdi)
ff_sbr_qmf_post_shuffle_sse.step:
    add $0x20,%rdi
    sub $0x10,%rdx
    add $0x10,%rsi
ff_sbr_qmf_post_shuffle_sse.cmp:
    cmp %rdx,%rsi
    jl ff_sbr_qmf_post_shuffle_sse.loop
ff_sbr_qmf_post_shuffle_sse.done:
    ret
")

end Kraken.Examples.Sbr.QmfPostShuffle

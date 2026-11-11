import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `HfInverseFilter`: the program text

The program text (`body`) of `HfInverseFilter.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.HfInverseFilter

/-- The procedure from the `-c opt` object (`aacsbr.o`), labels prefixed with
the symbol, a free label after the call (`.c1`) and one inside the long
`.Lc02f` block (`.c2`); the rip constants as ambient labels `LCPI19_*`; the
final `ret` (dropped by the extraction; present in the object at `+0x1eb`)
behind `….done`. -/
def body : Program := parse("
sbr_hf_inverse_filter:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x48,%rsp
    mov %rdi,-0x38(%rbp)
    test %r8d,%r8d
    jle sbr_hf_inverse_filter.Lc0dd
sbr_hf_inverse_filter.e1:
    mov %rcx,%rbx
    mov %rdx,%r14
    mov %rsi,%r15
    mov %r8d,%eax
    shl $0x3,%rax
    mov %rax,-0x30(%rbp)
    xor %r12d,%r12d
    xor %r13d,%r13d
    jmp sbr_hf_inverse_filter.Lbf6f
    nop
sbr_hf_inverse_filter.Lbf40:
    movl $0x0,(%rax)
    movl $0x0,0x4(%r14,%r12,1)
    movq $0x0,(%r15,%r12,1)
sbr_hf_inverse_filter.Lbf57:
    inc %r13
    add $0x8,%r12
    add $0x140,%rbx
    cmp %r12,-0x30(%rbp)
    je sbr_hf_inverse_filter.Lc0dd
sbr_hf_inverse_filter.Lbf6f:
    mov %rbx,%rdi
    lea -0x70(%rbp),%rsi
    mov -0x38(%rbp),%rax
    call *0x38(%rax)
sbr_hf_inverse_filter.c1:
    vxorps %xmm7,%xmm7,%xmm7
    vmovss -0x60(%rbp),%xmm0
    vmulss -0x48(%rbp),%xmm0,%xmm3
    vmovsd -0x58(%rbp),%xmm2
    vshufps $0xe1,%xmm2,%xmm2,%xmm1
    vmulps %xmm2,%xmm2,%xmm4
    vmovshdup %xmm4,%xmm5
    vaddss %xmm5,%xmm4,%xmm4
    vdivss LCPI19_0(%rip),%xmm4,%xmm4
    vaddss %xmm4,%xmm3,%xmm3
    vucomiss %xmm7,%xmm3
    jne sbr_hf_inverse_filter.Lbfb5
    jnp sbr_hf_inverse_filter.Lc000
sbr_hf_inverse_filter.Lbfb5:
    vbroadcastss -0x70(%rbp),%xmm4
    vmulps %xmm4,%xmm2,%xmm4
    vbroadcastss -0x6c(%rbp),%xmm5
    vmulps %xmm5,%xmm1,%xmm5
    vaddsubps %xmm5,%xmm4,%xmm4
    vmovsd -0x68(%rbp),%xmm5
    vmovsldup %xmm0,%xmm6
    vmulps %xmm5,%xmm6,%xmm5
    vsubps %xmm5,%xmm4,%xmm4
    vmovsldup %xmm3,%xmm3
    vdivps %xmm3,%xmm4,%xmm4
    vmovss %xmm4,(%r14,%r12,1)
    vmovaps %xmm4,%xmm3
    jmp sbr_hf_inverse_filter.Lc010
    nop
sbr_hf_inverse_filter.Lc000:
    movl $0x0,(%r14,%r12,1)
    vxorps %xmm3,%xmm3,%xmm3
    vxorps %xmm4,%xmm4,%xmm4
sbr_hf_inverse_filter.Lc010:
    vmovshdup %xmm3,%xmm5
    vmovss %xmm5,0x4(%r14,%r12,1)
    vucomiss %xmm7,%xmm0
    vmovss LCPI19_1(%rip),%xmm6
    jne sbr_hf_inverse_filter.Lc02f
    jnp sbr_hf_inverse_filter.Lc0b0
sbr_hf_inverse_filter.Lc02f:
    vmulss %xmm4,%xmm2,%xmm4
    vaddss -0x70(%rbp),%xmm4,%xmm4
    vmovshdup %xmm2,%xmm2
    vmulss %xmm5,%xmm2,%xmm2
    vaddss %xmm2,%xmm4,%xmm2
    vxorps LCPI19_2(%rip),%xmm2,%xmm2
    vmulps %xmm3,%xmm1,%xmm1
    vmovshdup %xmm1,%xmm3
    vaddss -0x6c(%rbp),%xmm3,%xmm3
    vsubss %xmm3,%xmm1,%xmm1
    vinsertps $0x1c,%xmm1,%xmm2,%xmm1
    vmovsldup %xmm0,%xmm0
    vdivps %xmm0,%xmm1,%xmm0
    vmovlps %xmm0,(%r15,%r12,1)
sbr_hf_inverse_filter.c2:
    lea (%r14,%r13,8),%rax
    vmovsd (%r14,%r12,1),%xmm1
    vmulps %xmm1,%xmm1,%xmm1
    vmovshdup %xmm1,%xmm2
    vaddss %xmm2,%xmm1,%xmm1
    vucomiss %xmm6,%xmm1
    jae sbr_hf_inverse_filter.Lbf40
    vmulps %xmm0,%xmm0,%xmm0
    vmovshdup %xmm0,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vucomiss %xmm6,%xmm0
    jb sbr_hf_inverse_filter.Lbf57
    jmp sbr_hf_inverse_filter.Lbf40
    nop
sbr_hf_inverse_filter.Lc0b0:
    movq $0x0,(%r15,%r12,1)
    vmovsd (%r14,%r12,1),%xmm0
    vmulps %xmm0,%xmm0,%xmm0
    vmovshdup %xmm0,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vucomiss %xmm6,%xmm0
    jb sbr_hf_inverse_filter.Lbf57
    lea (%r14,%r12,1),%rax
    jmp sbr_hf_inverse_filter.Lbf40
sbr_hf_inverse_filter.Lc0dd:
    add $0x48,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
sbr_hf_inverse_filter.done:
    ret
")

end Kraken.Examples.Sbr.HfInverseFilter

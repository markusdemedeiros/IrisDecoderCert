import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `QmfSynthesis`: the program text

The program text (`body`) of `QmfSynthesis.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.QmfSynthesis

/-- The procedure from the `-c opt` object (`aacsbr.o`), labels prefixed with
the symbol and a free label after every call; the `-mcmodel=medium` window
addresses (`lea _GLOBAL_OFFSET_TABLE_(%rip)` + `movabs $sym@GOTOFF` + `add`)
as label differences; `.LCPI15_1` as the ambient label `LCPI15_1`; the final
`ret` behind `….done`. -/
def body : Program := parse("
sbr_qmf_synthesis:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0xf8,%rsp
sbr_qmf_synthesis.e1:
    mov %r9,%rbx
    mov %r8,%r14
    mov %rcx,-0x118(%rbp)
    mov %rdx,-0x30(%rbp)
    mov %rsi,-0x40(%rbp)
    mov %rdi,-0x38(%rbp)
    lea _GLOBAL_OFFSET_TABLE_(%rip),%rax
    mov 0x28(%rbp),%ecx
    movabs $sbr_qmf_window_ds-_GLOBAL_OFFSET_TABLE_,%rdx
    add %rax,%rdx
    movabs $sbr_qmf_window_us-_GLOBAL_OFFSET_TABLE_,%rsi
    add %rax,%rsi
    test %ecx,%ecx
    cmovne %rdx,%rsi
sbr_qmf_synthesis.e2:
    mov $0x80,%r13d
    shr %cl,%r13d
    mov $0x480,%eax
    shr %cl,%eax
    mov $0x900,%edi
    sub %eax,%edi
    shl $0x2,%eax
    mov %rax,-0x60(%rbp)
    mov $0x40,%r8d
    shr %cl,%r8d
    mov $0xc0,%r9d
    shr %cl,%r9d
    mov $0x100,%r10d
    shr %cl,%r10d
    mov $0x1c0,%r11d
    shr %cl,%r11d
    mov $0x200,%r12d
    shr %cl,%r12d
sbr_qmf_synthesis.e3:
    mov $0x2c0,%eax
    shr %cl,%eax
    mov %rax,-0xd8(%rbp)
    mov $0x140,%eax
    shr %cl,%eax
    lea (%rsi,%rax,4),%rax
    mov %rax,-0xd0(%rbp)
    mov $0x300,%eax
    shr %cl,%eax
    mov %rax,-0xc8(%rbp)
    mov $0x180,%eax
    shr %cl,%eax
    mov $0x3c0,%edx
    shr %cl,%edx
    mov %rdx,-0xc0(%rbp)
sbr_qmf_synthesis.e4:
    mov $0x400,%edx
    shr %cl,%edx
    mov %rdx,-0xb8(%rbp)
    mov $0x4c0,%edx
    shr %cl,%edx
    mov %rdx,-0xb0(%rbp)
    mov $0x240,%edx
    shr %cl,%edx
    lea (%rsi,%rax,4),%rax
    mov %rax,-0xa8(%rbp)
    lea (%rsi,%rdx,4),%rax
    mov %rax,-0xa0(%rbp)
sbr_qmf_synthesis.e5:
    mov 0x18(%rbp),%rax
    mov 0x10(%rbp),%rcx
    mov %rdi,-0x58(%rbp)
    lea (%rax,%rdi,4),%rax
    mov %rax,-0x50(%rbp)
    lea 0x100(%rcx),%rax
    mov %rax,-0x48(%rbp)
    mov %r8,-0x100(%rbp)
sbr_qmf_synthesis.e6:
    lea 0x0(,%r8,4),%eax
    mov %rax,-0x98(%rbp)
    lea (%rsi,%rax,1),%rax
    mov %rax,-0x90(%rbp)
    lea (%rsi,%r13,4),%rax
    mov %rax,-0x88(%rbp)
    mov %r9,-0xf8(%rbp)
    lea (%rsi,%r9,4),%rax
    mov %rax,-0x80(%rbp)
    mov %r10,-0xf0(%rbp)
    lea (%rsi,%r10,4),%rax
    mov %rax,-0x78(%rbp)
    mov %r11,-0xe8(%rbp)
sbr_qmf_synthesis.e7:
    lea (%rsi,%r11,4),%rax
    mov %rax,-0x70(%rbp)
    mov %rsi,-0x110(%rbp)
    mov %r12,-0xe0(%rbp)
    lea (%rsi,%r12,4),%rax
    mov %rax,-0x68(%rbp)
    mov $0x20,%eax
    mov %r13,-0x108(%rbp)
    jmp sbr_qmf_synthesis.L9fd2
    nop
sbr_qmf_synthesis.L9df0:
    lea 0x2600(%rbx),%rdi
    mov -0x30(%rbp),%rax
    call *0x10(%rax)
sbr_qmf_synthesis.c1:
    mov $0x4,%ecx
    mov -0x38(%rbp),%r12
    mov %r12,%rdi
    mov 0x10(%rbp),%rsi
    mov %rbx,%rdx
    mov -0x40(%rbp),%r15
    call *%r15
sbr_qmf_synthesis.c2:
    mov $0x4,%ecx
    mov %r12,%rdi
    mov -0x48(%rbp),%r12
    mov %r12,%rsi
    lea 0x2600(%rbx),%rdx
    call *%r15
sbr_qmf_synthesis.c3:
    mov %r13,%rdi
    mov %r12,%rsi
    mov 0x10(%rbp),%rdx
    mov -0x30(%rbp),%rax
    call *0x30(%rax)
sbr_qmf_synthesis.L9e42:
    mov %r14,%rdi
    mov %r13,%rsi
    mov -0x110(%rbp),%rdx
    mov -0x100(%rbp),%r12
    mov %r12d,%ecx
    mov -0x118(%rbp),%r15
    call *(%r15)
sbr_qmf_synthesis.f1:
    mov -0xf8(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x90(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f2:
    mov -0xf0(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x88(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f3:
    mov -0xe8(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x80(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f4:
    mov -0xe0(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x78(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f5:
    mov -0xd8(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0xd0(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f6:
    mov -0xc8(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0xa8(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f7:
    mov -0xc0(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x70(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f8:
    mov -0xb8(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0x68(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.f9:
    mov -0xb0(%rbp),%rax
    lea 0x0(,%rax,4),%rsi
    add %r13,%rsi
    mov %r14,%rdi
    mov -0xa0(%rbp),%rdx
    mov %r14,%rcx
    mov %r12d,%r8d
    call *0x30(%r15)
sbr_qmf_synthesis.lend:
    add $0x100,%rbx
    add -0x98(%rbp),%r14
    mov -0x120(%rbp),%rax
    dec %rax
    mov -0x108(%rbp),%r13
    je sbr_qmf_synthesis.La125
sbr_qmf_synthesis.L9fd2:
    mov %rax,-0x120(%rbp)
    mov 0x20(%rbp),%rax
    mov (%rax),%eax
    cmp %r13d,%eax
    jge sbr_qmf_synthesis.L9ff9
sbr_qmf_synthesis.mc:
    mov -0x50(%rbp),%rdi
    mov 0x18(%rbp),%rsi
    mov -0x60(%rbp),%rdx
    call memcpy
sbr_qmf_synthesis.mc1:
    mov -0x58(%rbp),%rax
sbr_qmf_synthesis.L9ff9:
    sub %r13d,%eax
    mov 0x20(%rbp),%rcx
    mov %eax,(%rcx)
    cltq
    mov 0x18(%rbp),%rcx
    lea (%rcx,%rax,4),%r13
    cmpl $0x0,0x28(%rbp)
    je sbr_qmf_synthesis.L9df0
sbr_qmf_synthesis.ds:
    vbroadcastss LCPI15_1(%rip),%xmm1
    vxorps (%rbx),%xmm1,%xmm0
    vmovups %xmm0,(%rbx)
    vpermilps $0x1b,0x2670(%rbx),%xmm0
    vmovups %xmm0,0x80(%rbx)
    vxorps 0x10(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x10(%rbx)
    vpermilps $0x1b,0x2660(%rbx),%xmm0
    vmovups %xmm0,0x90(%rbx)
    vxorps 0x20(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x20(%rbx)
    vpermilps $0x1b,0x2650(%rbx),%xmm0
    vmovups %xmm0,0xa0(%rbx)
    vxorps 0x30(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x30(%rbx)
    vpermilps $0x1b,0x2640(%rbx),%xmm0
    vmovups %xmm0,0xb0(%rbx)
    vxorps 0x40(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x40(%rbx)
    vpermilps $0x1b,0x2630(%rbx),%xmm0
    vmovups %xmm0,0xc0(%rbx)
    vxorps 0x50(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x50(%rbx)
    vpermilps $0x1b,0x2620(%rbx),%xmm0
    vmovups %xmm0,0xd0(%rbx)
    vxorps 0x60(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x60(%rbx)
    vpermilps $0x1b,0x2610(%rbx),%xmm0
    vmovups %xmm0,0xe0(%rbx)
    vxorps 0x70(%rbx),%xmm1,%xmm0
    vmovups %xmm0,0x70(%rbx)
    vpermilps $0x1b,0x2600(%rbx),%xmm0
    vmovups %xmm0,0xf0(%rbx)
sbr_qmf_synthesis.ds1:
    mov $0x4,%ecx
    mov -0x38(%rbp),%rdi
    mov 0x10(%rbp),%r12
    mov %r12,%rsi
    mov %rbx,%rdx
    call *-0x40(%rbp)
sbr_qmf_synthesis.ds2:
    mov %r13,%rdi
    mov %r12,%rsi
    mov -0x30(%rbp),%rax
    call *0x28(%rax)
sbr_qmf_synthesis.ds3:
    jmp sbr_qmf_synthesis.L9e42
sbr_qmf_synthesis.La125:
    add $0xf8,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
sbr_qmf_synthesis.done:
    ret
    int3
    int3
    int3
    int3
    int3
    int3
    int3
    int3
    int3
")

end Kraken.Examples.Sbr.QmfSynthesis

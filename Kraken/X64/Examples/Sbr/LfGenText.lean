import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `LfGen`: the program text

The program text (`body`) of `LfGen.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.LfGen

def body : Program := parse("
sbr_lf_gen:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r12
    push %rbx
    mov %ecx,%r12d
    mov %rdx,%rbx
    mov %rsi,%r14
    mov %rdi,%r15
sbr_lf_gen.c:
    mov $0x2800,%edx
    mov %rsi,%rdi
    xor %esi,%esi
    call memset
sbr_lf_gen.m1:
    cmpl $0x0,0x58(%r15)
    movslq %r12d,%rax
    je sbr_lf_gen.La588
    mov %rax,%rcx
    shl $0xd,%rcx
    add %rbx,%rcx
    lea 0x13c(%r14),%rdx
    mov $0x1,%esi
    nop
sbr_lf_gen.La190:
    vmovss -0x8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xfc(%rdx)
    vmovss -0x4(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xf8(%rdx)
    vmovss 0xf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xf4(%rdx)
    vmovss 0xfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xf0(%rdx)
    vmovss 0x1f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xec(%rdx)
    vmovss 0x1fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xe8(%rdx)
    vmovss 0x2f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xe4(%rdx)
    vmovss 0x2fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xe0(%rdx)
sbr_lf_gen.a1:
    vmovss 0x3f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xdc(%rdx)
    vmovss 0x3fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xd8(%rdx)
    vmovss 0x4f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xd4(%rdx)
    vmovss 0x4fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xd0(%rdx)
    vmovss 0x5f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xcc(%rdx)
    vmovss 0x5fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xc8(%rdx)
    vmovss 0x6f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xc4(%rdx)
    vmovss 0x6fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xc0(%rdx)
sbr_lf_gen.a2:
    vmovss 0x7f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xbc(%rdx)
    vmovss 0x7fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xb8(%rdx)
    vmovss 0x8f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xb4(%rdx)
    vmovss 0x8fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xb0(%rdx)
    vmovss 0x9f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xac(%rdx)
    vmovss 0x9fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xa8(%rdx)
    vmovss 0xaf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xa4(%rdx)
    vmovss 0xafc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xa0(%rdx)
sbr_lf_gen.a3:
    vmovss 0xbf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x9c(%rdx)
    vmovss 0xbfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x98(%rdx)
    vmovss 0xcf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x94(%rdx)
    vmovss 0xcfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x90(%rdx)
    vmovss 0xdf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x8c(%rdx)
    vmovss 0xdfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x88(%rdx)
    vmovss 0xef8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x84(%rdx)
    vmovss 0xefc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x80(%rdx)
sbr_lf_gen.a4:
    vmovss 0xff8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x7c(%rdx)
    vmovss 0xffc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x78(%rdx)
    vmovss 0x10f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x74(%rdx)
    vmovss 0x10fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x70(%rdx)
    vmovss 0x11f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x6c(%rdx)
    vmovss 0x11fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x68(%rdx)
    vmovss 0x12f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x64(%rdx)
    vmovss 0x12fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x60(%rdx)
sbr_lf_gen.a5:
    vmovss 0x13f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x5c(%rdx)
    vmovss 0x13fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x58(%rdx)
    vmovss 0x14f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x54(%rdx)
    vmovss 0x14fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x50(%rdx)
    vmovss 0x15f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x4c(%rdx)
    vmovss 0x15fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x48(%rdx)
    vmovss 0x16f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x44(%rdx)
    vmovss 0x16fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x40(%rdx)
sbr_lf_gen.a6:
    vmovss 0x17f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x3c(%rdx)
    vmovss 0x17fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x38(%rdx)
    vmovss 0x18f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x34(%rdx)
    vmovss 0x18fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x30(%rdx)
    vmovss 0x19f8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x2c(%rdx)
    vmovss 0x19fc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x28(%rdx)
    vmovss 0x1af8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x24(%rdx)
    vmovss 0x1afc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x20(%rdx)
sbr_lf_gen.a7:
    vmovss 0x1bf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x1c(%rdx)
    vmovss 0x1bfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x18(%rdx)
    vmovss 0x1cf8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x14(%rdx)
    vmovss 0x1cfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x10(%rdx)
    vmovss 0x1df8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0xc(%rdx)
    vmovss 0x1dfc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x8(%rdx)
    vmovss 0x1ef8(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,-0x4(%rdx)
    vmovss 0x1efc(%rcx,%rsi,8),%xmm0
    vmovss %xmm0,(%rdx)
sbr_lf_gen.a8:
    mov 0x58(%r15),%edi
    cmp %rdi,%rsi
    jae sbr_lf_gen.La588
    inc %rsi
    add $0x140,%rdx
    cmp $0x21,%rsi
    jne sbr_lf_gen.La190
sbr_lf_gen.t1:
    ud1 0x12(%eax),%eax
sbr_lf_gen.La588:
    cmpl $0x0,0x54(%r15)
    je sbr_lf_gen.La6ba
    add $0x3c,%r14
    shl $0xd,%rax
    sub %rax,%rbx
    add $0x3f04,%rbx
    mov $0xffffffffffffffe0,%rax
    nop
sbr_lf_gen.La5b0:
    vmovss -0x604(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x3c(%r14)
    vmovss -0x600(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x38(%r14)
    vmovss -0x504(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x34(%r14)
    vmovss -0x500(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x30(%r14)
    vmovss -0x404(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x2c(%r14)
    vmovss -0x400(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x28(%r14)
    vmovss -0x304(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x24(%r14)
    vmovss -0x300(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x20(%r14)
sbr_lf_gen.b1:
    vmovss -0x204(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x1c(%r14)
    vmovss -0x200(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x18(%r14)
    vmovss -0x104(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x14(%r14)
    vmovss -0x100(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x10(%r14)
    vmovss -0x4(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0xc(%r14)
    vmovss (%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x8(%r14)
    vmovss 0xfc(%rbx,%rax,8),%xmm0
    vmovss %xmm0,-0x4(%r14)
    vmovss 0x100(%rbx,%rax,8),%xmm0
    vmovss %xmm0,(%r14)
sbr_lf_gen.b2:
    lea 0x21(%rax),%rcx
    mov 0x54(%r15),%edx
    cmp %rdx,%rcx
    jae sbr_lf_gen.La6ba
    add $0x140,%r14
    inc %rax
    jne sbr_lf_gen.La5b0
sbr_lf_gen.t2:
    ud1 0x12(%eax),%eax
sbr_lf_gen.La6ba:
    xor %eax,%eax
    pop %rbx
    pop %r12
    pop %r14
    pop %r15
    pop %rbp
sbr_lf_gen.done:
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
    int3
    int3
")

end Kraken.Examples.Sbr.LfGen

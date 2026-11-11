import Kraken.X64.Parser
import Kraken.MachineWP

/-!
# `XGen`: the program text

The program text (`body`) of `XGen.lean`, as compared with the object
by translation validation (`scripts/sbr/tv`). This module imports only the parser and the
machine model; the proof is in the module of the same name without `Text`.
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.XGen

/-- The procedure from the `-c opt` object (`aacsbr.o`), labels prefixed with
the symbol, extra cut labels (`.e1`, `.e2`, `.m1`, …), each `ud1` behind a
label of its own, the `ret` behind `sbr_x_gen.done` where the object has it. -/
def body : Program := parse("
sbr_x_gen:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x28,%rsp
    mov %rcx,-0x38(%rbp)
    cmp $0x2,%r9d
    jae sbr_x_gen.Lbef3
sbr_x_gen.e1:
    mov %r8,%r12
    mov %rdx,%r13
    mov %rdi,%rbx
    mov %r9d,%eax
    imul $0x15ac0,%rax,%rax
    movzbl 0x15b25(%rdi,%rax,1),%eax
    xor %r15d,%r15d
    cmp $0x11,%eax
    lea -0x20(%rax,%rax,1),%r14d
    cmovb %r15d,%r14d
sbr_x_gen.e2:
    mov $0x4c00,%edx
    mov %rsi,-0x30(%rbp)
    mov %rsi,%rdi
    xor %esi,%esi
    call memset
sbr_x_gen.m1:
    mov 0x54(%rbx),%eax
    mov $0x0,%esi
    test %eax,%eax
    je sbr_x_gen.Lb9cc
    mov %eax,%r15d
    mov %eax,%esi
    test %r14d,%r14d
    jle sbr_x_gen.Lb9cc
sbr_x_gen.a0:
    mov %r14d,%eax
    shl $0x8,%rax
    mov -0x30(%rbp),%rcx
    add $0x2800,%rcx
    lea 0x24(%r12),%rdx
    lea -0x200(%rax),%rdi
    lea -0x100(%rax),%r8
    xor %esi,%esi
    nop
sbr_x_gen.Lb910:
    mov %rdx,%r9
    xor %r10d,%r10d
    nop
sbr_x_gen.Lb920:
    vmovss -0x14(%r9),%xmm0
    vmovss %xmm0,-0x2800(%rcx,%r10,1)
    vmovss -0x10(%r9),%xmm0
    vmovss %xmm0,-0x200(%rcx,%r10,1)
    cmp %r10,%r8
    je sbr_x_gen.Lb9a6
sbr_x_gen.a2:
    vmovss -0xc(%r9),%xmm0
    vmovss %xmm0,-0x2700(%rcx,%r10,1)
    vmovss -0x8(%r9),%xmm0
    vmovss %xmm0,-0x100(%rcx,%r10,1)
    cmp %r10,%rdi
    je sbr_x_gen.Lb9a6
    cmp $0x2400,%r10
    je sbr_x_gen.Lbee9
sbr_x_gen.a3:
    vmovss -0x4(%r9),%xmm0
    vmovss %xmm0,-0x2600(%rcx,%r10,1)
    vmovss (%r9),%xmm0
    vmovss %xmm0,(%rcx,%r10,1)
    add $0x300,%r10
    add $0x18,%r9
    cmp %r10,%rax
    jne sbr_x_gen.Lb920
sbr_x_gen.Lb9a6:
    inc %rsi
    mov 0x54(%rbx),%r15d
    cmp %r15,%rsi
    jae sbr_x_gen.Lb9cc
    add $0x4,%rcx
    add $0x140,%rdx
    cmp $0x40,%rsi
    jne sbr_x_gen.Lb910
sbr_x_gen.t1:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lb9cc:
    add 0x5c(%rbx),%r15d
    cmp %r15d,%esi
    jae sbr_x_gen.Lbba9
    test %r14d,%r14d
    jle sbr_x_gen.Lbba9
    lea -0x1(%r14),%ecx
    cmp $0x26,%ecx
    mov $0x26,%eax
    cmovb %ecx,%eax
    cmp $0x41,%esi
    mov $0x40,%ecx
    cmovae %esi,%ecx
    cmp $0x3f,%esi
    ja sbr_x_gen.Lbba4
sbr_x_gen.b0:
    mov %r14d,%edi
    mov %esi,%esi
    mov %rdi,-0x48(%rbp)
    and $0x7ffffffc,%edi
    lea 0x0(,%rsi,4),%rdx
    mov %rdx,-0x40(%rbp)
    mov -0x30(%rbp),%rdx
    lea 0x2900(%rdx),%r9
    lea (%rdx,%rsi,4),%r10
    lea 0x4000(,%rsi,8),%r11
    add %r13,%r11
    add $0x4604,%r13
    nop
sbr_x_gen.Lba50:
    cmp $0x26,%eax
    je sbr_x_gen.Lbeee
    cmp $0x4,%r14d
    jae sbr_x_gen.Lba70
    xor %r15d,%r15d
    jmp sbr_x_gen.Lbb30
    nop
sbr_x_gen.Lba70:
    mov -0x40(%rbp),%r8
    xor %r15d,%r15d
    nop
sbr_x_gen.Lba80:
    vmovss -0x604(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x2900(%r9,%r8,1)
    vmovss -0x600(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x300(%r9,%r8,1)
    vmovss -0x404(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x2800(%r9,%r8,1)
    vmovss -0x400(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x200(%r9,%r8,1)
sbr_x_gen.b2:
    vmovss -0x204(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x2700(%r9,%r8,1)
    vmovss -0x200(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x100(%r9,%r8,1)
    vmovss -0x4(%r13,%r8,2),%xmm0
    vmovss %xmm0,-0x2600(%r9,%r8,1)
    vmovss 0x0(%r13,%r8,2),%xmm0
    vmovss %xmm0,(%r9,%r8,1)
sbr_x_gen.b3:
    add $0x4,%r15
    add $0x400,%r8
    cmp %r15,%rdi
    jne sbr_x_gen.Lba80
    testb $0x2,-0x48(%rbp)
    je sbr_x_gen.Lbb7d
sbr_x_gen.Lbb30:
    mov %r15,%r8
    shl $0x8,%r8
    add %r10,%r8
    shl $0x9,%r15
    add %r11,%r15
    xor %edx,%edx
    nop
sbr_x_gen.Lbb50:
    vmovss (%r15,%rdx,2),%xmm0
    vmovss %xmm0,(%r8,%rdx,1)
    vmovss 0x4(%r15,%rdx,2),%xmm0
    vmovss %xmm0,0x2600(%r8,%rdx,1)
    add $0x100,%rdx
    cmp $0x200,%rdx
    jne sbr_x_gen.Lbb50
sbr_x_gen.Lbb7d:
    inc %rsi
    mov 0x5c(%rbx),%edx
    add 0x54(%rbx),%edx
    cmp %rdx,%rsi
    jae sbr_x_gen.Lbba9
    add $0x8,%r13
    add $0x4,%r9
    add $0x4,%r10
    add $0x8,%r11
    cmp %rcx,%rsi
    jne sbr_x_gen.Lba50
sbr_x_gen.Lbba4:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lbba9:
    mov 0x58(%rbx),%r11d
    test %r11d,%r11d
    je sbr_x_gen.Lbd11
    mov %r11d,%eax
    cmp $0x25,%r14d
    jg sbr_x_gen.Lbd16
sbr_x_gen.c0:
    movslq %r14d,%rcx
    mov $0x2,%edx
    sub %rcx,%rdx
    lea -0x23(%rcx),%rsi
    mov %rcx,%rax
    shl $0x8,%rax
    mov -0x30(%rbp),%r10
    lea (%rax,%r10,1),%rdi
    add $0x2600,%rdi
    lea 0x14(%r12),%r8
    mov %edx,%r9d
    shl $0x5,%r9d
    and $0x40,%r9d
    xor %eax,%eax
    nop
sbr_x_gen.Lbc00:
    mov %rcx,%r11
    test $0x2,%dl
    je sbr_x_gen.Lbc39
    xor %r15d,%r15d
    mov %rcx,%r11
    nop
sbr_x_gen.Lbc10:
    vmovss -0x4(%r8,%r11,8),%xmm0
    vmovss %xmm0,-0x2600(%rdi,%r15,8)
    vmovss (%r8,%r11,8),%xmm0
    vmovss %xmm0,(%rdi,%r15,8)
    inc %r11
    add $0x20,%r15
    cmp %r15,%r9
    jne sbr_x_gen.Lbc10
sbr_x_gen.Lbc39:
    cmp $0x3,%esi
    jb sbr_x_gen.Lbce0
    lea 0x5(%r11),%r15
    shl $0x8,%r11
    add %r10,%r11
    nop
sbr_x_gen.Lbc50:
    vmovss -0x18(%r12,%r15,8),%xmm0
    vmovss %xmm0,(%r11)
    vmovss -0x14(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x2600(%r11)
    vmovss -0x10(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x100(%r11)
    vmovss -0xc(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x2700(%r11)
sbr_x_gen.c2:
    vmovss -0x8(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x200(%r11)
    vmovss -0x4(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x2800(%r11)
    vmovss (%r12,%r15,8),%xmm0
    vmovss %xmm0,0x300(%r11)
    vmovss 0x4(%r12,%r15,8),%xmm0
    vmovss %xmm0,0x2900(%r11)
sbr_x_gen.c3:
    add $0x4,%r15
    add $0x400,%r11
    cmp $0x2b,%r15
    jne sbr_x_gen.Lbc50
sbr_x_gen.Lbce0:
    inc %rax
    mov 0x58(%rbx),%r11d
    cmp %r11,%rax
    jae sbr_x_gen.Lbd16
    add $0x4,%rdi
    add $0x140,%r8
    add $0x4,%r10
    add $0x140,%r12
    cmp $0x40,%rax
    jne sbr_x_gen.Lbc00
sbr_x_gen.t2:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lbd11:
    xor %r11d,%r11d
    xor %eax,%eax
sbr_x_gen.Lbd16:
    add 0x60(%rbx),%r11d
    cmp %r11d,%eax
    jae sbr_x_gen.Lbed8
    cmp $0x1f,%r14d
    jg sbr_x_gen.Lbed8
    cmp $0x41,%eax
    mov $0x40,%ecx
    cmovae %eax,%ecx
    cmp $0x3f,%eax
    ja sbr_x_gen.Lbed3
sbr_x_gen.d0:
    mov %r14d,%edx
    mov %eax,%eax
    mov %r14d,%esi
    neg %esi
    and $0x2,%esi
    add $0xffffffe3,%r14d
    mov %rdx,%rdi
    shl $0x8,%rdi
    lea (%rdi,%rax,4),%rdi
    mov -0x30(%rbp),%r11
    add %r11,%rdi
    add $0x2600,%rdi
sbr_x_gen.d1:
    mov %rdx,%r8
    shl $0x9,%r8
    mov -0x38(%rbp),%r15
    lea (%r15,%rax,8),%r9
    add %r9,%r8
    add $0x4,%r8
    mov %esi,%r9d
    shl $0x8,%r9d
    lea -0x2(%rsi),%r10d
    add %rdx,%r10
    add $0x2,%r10
    lea (%r11,%rax,4),%r11
    lea (%r15,%rax,8),%r15
    add $0x604,%r15
    nop
sbr_x_gen.Lbdb0:
    mov %rdx,%r12
    test %esi,%esi
    je sbr_x_gen.Lbdec
    xor %r12d,%r12d
    nop
sbr_x_gen.Lbdc0:
    vmovss -0x4(%r8,%r12,2),%xmm0
    vmovss %xmm0,-0x2600(%rdi,%r12,1)
    vmovss (%r8,%r12,2),%xmm0
    vmovss %xmm0,(%rdi,%r12,1)
    add $0x100,%r12
    cmp %r12d,%r9d
    jne sbr_x_gen.Lbdc0
    mov %r10,%r12
sbr_x_gen.Lbdec:
    cmp $0x3,%r14d
    jb sbr_x_gen.Lbeaa
    lea -0x1(%r12),%r13d
    shl $0x8,%r12
    nop
sbr_x_gen.Lbe00:
    vmovss -0x604(%r15,%r12,2),%xmm0
    vmovss %xmm0,(%r11,%r12,1)
    vmovss -0x600(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x2600(%r11,%r12,1)
    vmovss -0x404(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x100(%r11,%r12,1)
    vmovss -0x400(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x2700(%r11,%r12,1)
sbr_x_gen.d2:
    vmovss -0x204(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x200(%r11,%r12,1)
    vmovss -0x200(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x2800(%r11,%r12,1)
    vmovss -0x4(%r15,%r12,2),%xmm0
    vmovss %xmm0,0x300(%r11,%r12,1)
    vmovss (%r15,%r12,2),%xmm0
    vmovss %xmm0,0x2900(%r11,%r12,1)
sbr_x_gen.d3:
    add $0x4,%r13d
    add $0x400,%r12
    cmp $0x1f,%r13d
    jl sbr_x_gen.Lbe00
sbr_x_gen.Lbeaa:
    inc %rax
    mov 0x60(%rbx),%r12d
    add 0x58(%rbx),%r12d
    cmp %r12,%rax
    jae sbr_x_gen.Lbed8
    add $0x4,%rdi
    add $0x8,%r8
    add $0x4,%r11
    add $0x8,%r15
    cmp %rcx,%rax
    jne sbr_x_gen.Lbdb0
sbr_x_gen.Lbed3:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lbed8:
    xor %eax,%eax
    add $0x28,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
sbr_x_gen.done:
    ret
sbr_x_gen.Lbee9:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lbeee:
    ud1 0x12(%eax),%eax
sbr_x_gen.Lbef3:
    ud1 0x12(%eax),%eax
    int3
    int3
    int3
    int3
    int3
    int3
    int3
    int3
")

end Kraken.Examples.Sbr.XGen

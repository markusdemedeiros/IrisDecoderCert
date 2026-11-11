import Kraken.X64.Parser

/-!
# `ff_aac_sbr_decode_extension`: the program text

The compiled `ff_aac_sbr_decode_extension(ac, che, gb_host, crc, cnt, id_aac)` of
`libavcodec/aacsbr_template.c` (FFmpeg n8.1, `aacsbr.o`, see `scripts/sbr/README.md`), with
`read_sbr_data`, `read_sbr_single_channel_element`, `read_sbr_channel_pair_element`,
`copy_sbr_grid`, `read_sbr_extension` and `sbr_turnoff` inlined. Output of
`scripts/sbr/parse/decext/gen.py` (labels at the objdump labels, after every `call`, and at the
cut points).
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.DecExt

def body : Program := parse("
ff_aac_sbr_decode_extension:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x38,%rsp
    mov %r9d,%r13d
    mov %rsi,%r14
    mov %rdi,%r12
    lea 0x28920(%rsi),%rdi
ff_aac_sbr_decode_extension.L21:
    mov 0x10(%rdx),%rax
    mov %rax,-0x30(%rbp)
    vmovups (%rdx),%xmm0
    vmovaps %xmm0,-0x40(%rbp)
    mov %r8,-0x50(%rbp)
ff_aac_sbr_decode_extension.L36:
    lea -0x4(,%r8,8),%eax
    mov 0x8(%rdx),%esi
    mov 0x10(%rdx),%r9d
    mov %esi,%r8d
    neg %r8d
    sub %esi,%r9d
    cmp %r9d,%eax
    cmovl %eax,%r9d
    cmp %r8d,%eax
    cmovl %r8d,%r9d
    add %esi,%r9d
    mov %r9d,0x8(%rdx)
ff_aac_sbr_decode_extension.L63:
    movl $0x0,0x28938(%r14)
    cmpl $0x0,0x28920(%r14)
    je ff_aac_sbr_decode_extension.L301
    cmpl $0x0,0x57f4(%r12)
    je ff_aac_sbr_decode_extension.L31c
ff_aac_sbr_decode_extension.L8b:
    mov -0x38(%rbp),%edx
    mov -0x30(%rbp),%esi
    lea 0xa(%rdx),%eax
    cmp %eax,%esi
    cmovb %esi,%eax
    test %ecx,%ecx
    cmove %edx,%eax
    mov $0x1,%ecx
    mov $0xb,%r15d
    cmove %ecx,%r15d
ff_aac_sbr_decode_extension.Lad:
    mov 0x28978(%r14),%ecx
    mov 0x28980(%r14),%edx
    mov %ecx,0x28974(%r14)
    mov %edx,0x2897c(%r14)
    movl $0x1,0x28984(%r14)
ff_aac_sbr_decode_extension.Ld4:
    mov -0x40(%rbp),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    xor %r8d,%r8d
    cmp %esi,%eax
    setl %r8b
    add %eax,%r8d
    movzbl (%rcx,%rdx,1),%edx
    mov %r8d,-0x38(%rbp)
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%edx
    test %dl,%dl
    jns ff_aac_sbr_decode_extension.L333
ff_aac_sbr_decode_extension.Lff:
    lea -0x40(%rbp),%rsi
    mov %rdi,%rbx
    xor %edx,%edx
    call read_sbr_header
ff_aac_sbr_decode_extension.L10d:
    add %r15d,%eax
    mov %eax,%r15d
    cmpl $0x0,0x28938(%r14)
    je ff_aac_sbr_decode_extension.L128
ff_aac_sbr_decode_extension.L11d:
    mov %r12,%rdi
    mov %rbx,%rsi
    call sbr_reset
ff_aac_sbr_decode_extension.L128:
    cmpl $0x0,0x28924(%r14)
    je ff_aac_sbr_decode_extension.L4ee
    mov %rbx,%rsi
    mov -0x38(%rbp),%r8d
    mov %r13d,0x2892c(%r14)
    movl $0x1,0x28928(%r14)
    test $0xfffffffd,%r13d
    mov %r12,-0x48(%rbp)
    mov %r8,-0x58(%rbp)
    je ff_aac_sbr_decode_extension.L349
ff_aac_sbr_decode_extension.L164:
    cmp $0x1,%r13d
    jne ff_aac_sbr_decode_extension.L466
ff_aac_sbr_decode_extension.L16e:
    mov -0x40(%rbp),%rax
    mov %r8d,%ecx
    shr $0x3,%ecx
    mov -0x30(%rbp),%edx
    xor %r9d,%r9d
    cmp %edx,%r8d
    setl %r9b
    movzbl (%rax,%rcx,1),%edi
    mov %r8d,%ecx
    and $0x7,%cl
    shl %cl,%edi
    lea (%r8,%r9,1),%ecx
    add $0x8,%ecx
    cmp %ecx,%edx
    cmovb %edx,%ecx
    add %r9d,%r8d
    test %dil,%dil
    cmovns %r8d,%ecx
ff_aac_sbr_decode_extension.L1a7:
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %edi,%edi
    cmp %edx,%ecx
    setl %dil
    add %ecx,%edi
    movzbl (%rax,%r8,1),%ebx
    and $0x7,%cl
    shl %cl,%ebx
    shr $0x7,%ebx
    mov %edi,-0x38(%rbp)
    mov %ebx,%eax
    and $0x1,%eax
    mov %eax,0x2895c(%r14)
ff_aac_sbr_decode_extension.L1d4:
    lea 0x289a0(%r14),%r13
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    mov %r13,%rcx
    call read_sbr_grid
ff_aac_sbr_decode_extension.L1ea:
    and $0x1,%ebx
    jne ff_aac_sbr_decode_extension.L483
    test %eax,%eax
    jne ff_aac_sbr_decode_extension.L48b
    lea 0x3e460(%r14),%rcx
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    call read_sbr_grid
ff_aac_sbr_decode_extension.L215:
    test %eax,%eax
    jne ff_aac_sbr_decode_extension.L48b
    mov 0x28930(%r14),%edi
    lea -0x40(%rbp),%r13
    mov %r13,%rsi
    lea 0x289a0(%r14),%rdx
    xor %ecx,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_extension.L239:
    mov 0x28930(%r14),%edi
    mov %r13,%rsi
    lea 0x3e460(%r14),%rdx
    xor %ecx,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_extension.L251:
    lea 0x28920(%r14),%rbx
    mov %rbx,%rdi
    mov %r13,%rsi
    lea 0x289a0(%r14),%rdx
    call read_sbr_invf
ff_aac_sbr_decode_extension.L26a:
    mov %rbx,%rdi
    mov %r13,%rsi
    lea 0x3e460(%r14),%rdx
    call read_sbr_invf
ff_aac_sbr_decode_extension.L27c:
    mov %r12,%rdi
    mov %rbx,%rsi
    mov %r13,%rdx
    lea 0x3e460(%r14),%r13
    lea 0x289a0(%r14),%rbx
    mov %rbx,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_extension.L29e:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    mov %r13,%rcx
    mov $0x1,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_extension.L2c2:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    mov %rbx,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_extension.L2e3:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    mov %r13,%rcx
    jmp ff_aac_sbr_decode_extension.L76e
ff_aac_sbr_decode_extension.L301:
    mov 0x57e0(%r12),%eax
    add %eax,%eax
    mov %eax,(%rdi)
    cmpl $0x0,0x57f4(%r12)
    jne ff_aac_sbr_decode_extension.L8b
ff_aac_sbr_decode_extension.L31c:
    mov 0x57e0(%r12),%eax
    add %eax,%eax
    mov %eax,0x57f4(%r12)
    jmp ff_aac_sbr_decode_extension.L8b
ff_aac_sbr_decode_extension.L333:
    mov %rdi,%rbx
    cmpl $0x0,0x28938(%r14)
    jne ff_aac_sbr_decode_extension.L11d
    jmp ff_aac_sbr_decode_extension.L128
ff_aac_sbr_decode_extension.L349:
    mov -0x40(%rbp),%rax
    mov %r8d,%ecx
    shr $0x3,%ecx
    mov -0x30(%rbp),%edx
    xor %r9d,%r9d
    cmp %edx,%r8d
    setl %r9b
    lea (%r8,%r9,1),%edi
    movzbl (%rax,%rcx,1),%eax
    mov %r8d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    lea (%r8,%r9,1),%ecx
    add $0x4,%ecx
    cmp %ecx,%edx
    cmovb %edx,%ecx
    test %al,%al
    cmovns %edi,%ecx
    mov %ecx,-0x38(%rbp)
ff_aac_sbr_decode_extension.L384:
    lea 0x289a0(%r14),%r13
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    mov %r13,%rcx
    mov %rsi,%r12
    call read_sbr_grid
ff_aac_sbr_decode_extension.L39d:
    test %eax,%eax
    jne ff_aac_sbr_decode_extension.L48b
    mov 0x28930(%r14),%edi
    lea -0x40(%rbp),%rbx
    mov %rbx,%rsi
    mov %r13,%rdx
    xor %ecx,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_extension.L3bd:
    mov %r12,%rdi
    mov %rbx,%rsi
    mov %r13,%rdx
    call read_sbr_invf
ff_aac_sbr_decode_extension.L3cb:
    mov -0x48(%rbp),%rdi
    mov %r12,%rsi
    mov %rbx,%rdx
    mov -0x48(%rbp),%rbx
    mov %r13,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_extension.L3e4:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %rbx,%rdi
    mov %r12,%rsi
    mov %r13,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_extension.L401:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
ff_aac_sbr_decode_extension.L409:
    mov -0x38(%rbp),%ecx
    mov -0x40(%rbp),%rdi
    mov %ecx,%edx
    shr $0x3,%edx
    mov -0x30(%rbp),%esi
    xor %eax,%eax
    cmp %esi,%ecx
    setl %al
    add %ecx,%eax
    movzbl (%rdi,%rdx,1),%edx
    and $0x7,%cl
    shl %cl,%edx
    shr $0x7,%edx
    and $0x1,%edx
    mov %edx,0x289a4(%r14)
    je ff_aac_sbr_decode_extension.Lb1a
ff_aac_sbr_decode_extension.L43d:
    movslq 0x74b04(%r14),%r9
    test %r9,%r9
    jle ff_aac_sbr_decode_extension.Lb1a
    mov %r9d,%r8d
    and $0x3,%r8d
    cmp $0x4,%r9d
    jae ff_aac_sbr_decode_extension.L7de
    xor %r10d,%r10d
    jmp ff_aac_sbr_decode_extension.L898
ff_aac_sbr_decode_extension.L466:
    mov 0x8(%r12),%rdi
    lea L_str_21(%rip),%rdx
    mov $0x10,%esi
    mov %r13d,%ecx
    xor %eax,%eax
    call av_log
ff_aac_sbr_decode_extension.L481:
    jmp ff_aac_sbr_decode_extension.L48b
ff_aac_sbr_decode_extension.L483:
    test %eax,%eax
    je ff_aac_sbr_decode_extension.L591
ff_aac_sbr_decode_extension.L48b:
    movq $0x0,0x28924(%r14)
    movl $0x0,0x28930(%r14)
ff_aac_sbr_decode_extension.L4a1:
    movl $0x20,0x28978(%r14)
    movl $0x0,0x28980(%r14)
ff_aac_sbr_decode_extension.L4b7:
    movl $0xffffffff,0x41d68(%r14)
    movl $0xffffffff,0x2c2a8(%r14)
ff_aac_sbr_decode_extension.L4cd:
    movl $0xffffffff,0x2893c(%r14)
    movw $0xffff,0x28940(%r14)
ff_aac_sbr_decode_extension.L4e2:
    sub -0x58(%rbp),%r15d
    add -0x38(%rbp),%r15d
    mov -0x48(%rbp),%r12
ff_aac_sbr_decode_extension.L4ee:
    mov $0x4,%eax
    sub %r15d,%eax
    and $0x7,%eax
    lea (%r15,%rax,1),%r8d
    add $0x4,%r8d
    shr $0x3,%r8d
    cmp -0x50(%rbp),%r8d
    jbe ff_aac_sbr_decode_extension.L57e
ff_aac_sbr_decode_extension.L50b:
    mov 0x8(%r12),%rdi
    lea L_str(%rip),%rdx
    mov $0x10,%esi
    mov -0x50(%rbp),%rcx
    xor %eax,%eax
    call av_log
ff_aac_sbr_decode_extension.L527:
    movq $0x0,0x28924(%r14)
    movl $0x0,0x28930(%r14)
ff_aac_sbr_decode_extension.L53d:
    movl $0x20,0x28978(%r14)
    movl $0x0,0x28980(%r14)
ff_aac_sbr_decode_extension.L553:
    movl $0xffffffff,0x41d68(%r14)
    movl $0xffffffff,0x2c2a8(%r14)
ff_aac_sbr_decode_extension.L569:
    movl $0xffffffff,0x2893c(%r14)
    movw $0xffff,0x28940(%r14)
ff_aac_sbr_decode_extension.L57e:
    mov -0x50(%rbp),%rax
    add $0x38,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
ff_aac_sbr_decode_extension.done:
    ret
ff_aac_sbr_decode_extension.L591:
    mov 0x3e468(%r14),%eax
    cmp $0x9,%rax
    jae ff_aac_sbr_decode_extension.Lcf6
ff_aac_sbr_decode_extension.L5a2:
    mov %r13,%rdx
    lea 0x3e460(%r14),%rbx
    movzbl 0x3e46c(%r14,%rax,1),%ecx
    mov %cl,0x3e46c(%r14)
    movzbl 0x53efc(%r14,%rax,1),%ecx
    mov %cl,0x53f05(%r14)
ff_aac_sbr_decode_extension.L5cc:
    xor %ecx,%ecx
    cmp %eax,0x41d68(%r14)
    setne %cl
    neg %ecx
    mov %ecx,0x41d64(%r14)
ff_aac_sbr_decode_extension.L5e1:
    mov 0x289ad(%r14),%rax
    mov %rax,0x3e46d(%r14)
    mov 0x3e43c(%r14),%rax
    mov %rax,0x53efc(%r14)
ff_aac_sbr_decode_extension.L5fd:
    movzbl 0x3e444(%r14),%eax
    mov %al,0x53f04(%r14)
    movzwl 0x3e446(%r14),%eax
ff_aac_sbr_decode_extension.L614:
    mov %ax,0x53f06(%r14)
    movzbl 0x3e448(%r14),%eax
    mov %al,0x53f08(%r14)
ff_aac_sbr_decode_extension.L62b:
    mov 0x289a8(%r14),%eax
    mov %eax,0x3e468(%r14)
    mov 0x28a04(%r14),%eax
    mov %eax,0x3e4c4(%r14)
ff_aac_sbr_decode_extension.L647:
    mov 0x289b8(%r14),%eax
    mov %eax,0x3e478(%r14)
    mov 0x289a0(%r14),%eax
    mov %eax,0x3e460(%r14)
ff_aac_sbr_decode_extension.L663:
    mov 0x2c2a8(%r14),%eax
    mov %eax,0x41d68(%r14)
    mov 0x28930(%r14),%edi
    lea -0x40(%rbp),%r13
    mov %r13,%rsi
    xor %ecx,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_extension.L686:
    mov 0x28930(%r14),%edi
    mov %r13,%rsi
    mov %rbx,%rdx
    xor %ecx,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_extension.L69a:
    lea 0x28920(%r14),%rbx
    mov %rbx,%rdi
    mov %r13,%rsi
    lea 0x289a0(%r14),%rdx
    call read_sbr_invf
ff_aac_sbr_decode_extension.L6b3:
    movzbl 0x3e48b(%r14),%eax
    mov %al,0x3e490(%r14)
    mov 0x3e487(%r14),%eax
    mov %eax,0x3e48c(%r14)
ff_aac_sbr_decode_extension.L6d0:
    mov 0x289c7(%r14),%eax
    mov %eax,0x3e487(%r14)
    movzbl 0x289cb(%r14),%eax
    mov %al,0x3e48b(%r14)
ff_aac_sbr_decode_extension.L6ed:
    mov %r12,%rdi
    mov %rbx,%rsi
    mov %r13,%rdx
    lea 0x289a0(%r14),%rbx
    mov %rbx,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_extension.L708:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    mov %rbx,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_extension.L729:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    lea 0x3e460(%r14),%rcx
    mov $0x1,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_extension.L751:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
    lea -0x40(%rbp),%rdx
    mov %r12,%rdi
    lea 0x28920(%r14),%rsi
    lea 0x3e460(%r14),%rcx
ff_aac_sbr_decode_extension.L76e:
    mov $0x1,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_extension.L779:
    test %eax,%eax
    js ff_aac_sbr_decode_extension.L48b
ff_aac_sbr_decode_extension.L781:
    mov -0x38(%rbp),%ecx
    mov -0x40(%rbp),%rdi
    mov %ecx,%eax
    shr $0x3,%eax
    mov -0x30(%rbp),%esi
    xor %edx,%edx
    cmp %esi,%ecx
    setl %dl
    add %ecx,%edx
    movzbl (%rdi,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    and $0x1,%eax
    mov %eax,0x289a4(%r14)
    je ff_aac_sbr_decode_extension.L9d4
ff_aac_sbr_decode_extension.L7b5:
    movslq 0x74b04(%r14),%r9
    test %r9,%r9
    jle ff_aac_sbr_decode_extension.L9d4
    mov %r9d,%r8d
    and $0x3,%r8d
    cmp $0x4,%r9d
    jae ff_aac_sbr_decode_extension.L8e2
    xor %r10d,%r10d
    jmp ff_aac_sbr_decode_extension.L998
ff_aac_sbr_decode_extension.L7de:
    and $0x7ffffffc,%r9d
    xor %r10d,%r10d
ff_aac_sbr_decode_extension.L7e8:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d1(%r14,%r10,1)
ff_aac_sbr_decode_extension.L80e:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d2(%r14,%r10,1)
ff_aac_sbr_decode_extension.L835:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d3(%r14,%r10,1)
ff_aac_sbr_decode_extension.L85b:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d4(%r14,%r10,1)
    add $0x4,%r10
    cmp %r10,%r9
    jne ff_aac_sbr_decode_extension.L7e8
    test %r8,%r8
    je ff_aac_sbr_decode_extension.Lb1a
ff_aac_sbr_decode_extension.L898:
    lea (%r10,%r14,1),%rdx
    add $0x289d1,%rdx
    xor %r9d,%r9d
    nop
ff_aac_sbr_decode_extension.L8b0:
    mov %eax,%ecx
    mov %eax,%r10d
    shr $0x3,%r10d
    xor %eax,%eax
    cmp %esi,%ecx
    setl %al
    add %ecx,%eax
    movzbl (%rdi,%r10,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x7,%r10b
    mov %r10b,(%rdx,%r9,1)
    inc %r9
    cmp %r9,%r8
    jne ff_aac_sbr_decode_extension.L8b0
    jmp ff_aac_sbr_decode_extension.Lb1a
ff_aac_sbr_decode_extension.L8e2:
    and $0x7ffffffc,%r9d
    xor %r10d,%r10d
ff_aac_sbr_decode_extension.L8ec:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d1(%r14,%r10,1)
ff_aac_sbr_decode_extension.L913:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d2(%r14,%r10,1)
ff_aac_sbr_decode_extension.L939:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d3(%r14,%r10,1)
ff_aac_sbr_decode_extension.L960:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x289d4(%r14,%r10,1)
    add $0x4,%r10
    cmp %r10,%r9
    jne ff_aac_sbr_decode_extension.L8ec
    test %r8,%r8
    je ff_aac_sbr_decode_extension.L9d4
ff_aac_sbr_decode_extension.L998:
    lea (%r10,%r14,1),%rax
    add $0x289d1,%rax
    xor %r9d,%r9d
    mov %edx,%ecx
ff_aac_sbr_decode_extension.L9a7:
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %edx,%edx
    cmp %esi,%ecx
    setl %dl
    add %ecx,%edx
    movzbl (%rdi,%r10,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x7,%r10b
    mov %r10b,(%rax,%r9,1)
    inc %r9
    mov %edx,%ecx
    cmp %r9,%r8
    jne ff_aac_sbr_decode_extension.L9a7
ff_aac_sbr_decode_extension.L9d4:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r8d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r8d
    shr $0x7,%r8d
    and $0x1,%r8d
    mov %r8d,0x3e464(%r14)
    je ff_aac_sbr_decode_extension.Lb1a
ff_aac_sbr_decode_extension.La04:
    movslq 0x74b04(%r14),%r9
    test %r9,%r9
    jle ff_aac_sbr_decode_extension.Lb1a
    mov %r9d,%r8d
    and $0x3,%r8d
    cmp $0x4,%r9d
    jae ff_aac_sbr_decode_extension.La29
    xor %r10d,%r10d
    jmp ff_aac_sbr_decode_extension.Ladf
ff_aac_sbr_decode_extension.La29:
    and $0x7ffffffc,%r9d
    xor %r10d,%r10d
ff_aac_sbr_decode_extension.La33:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x3e491(%r14,%r10,1)
ff_aac_sbr_decode_extension.La59:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x3e492(%r14,%r10,1)
ff_aac_sbr_decode_extension.La80:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x3e493(%r14,%r10,1)
ff_aac_sbr_decode_extension.Laa6:
    mov %edx,%ecx
    shr $0x3,%ecx
    xor %eax,%eax
    cmp %esi,%edx
    setl %al
    add %edx,%eax
    movzbl (%rdi,%rcx,1),%r11d
    and $0x7,%dl
    mov %edx,%ecx
    shl %cl,%r11d
    shr $0x7,%r11b
    mov %r11b,0x3e494(%r14,%r10,1)
    add $0x4,%r10
    cmp %r10,%r9
    jne ff_aac_sbr_decode_extension.La33
    test %r8,%r8
    je ff_aac_sbr_decode_extension.Lb1a
ff_aac_sbr_decode_extension.Ladf:
    lea (%r10,%r14,1),%rdx
    add $0x3e491,%rdx
    xor %r9d,%r9d
ff_aac_sbr_decode_extension.Laed:
    mov %eax,%ecx
    mov %eax,%r10d
    shr $0x3,%r10d
    xor %eax,%eax
    cmp %esi,%ecx
    setl %al
    add %ecx,%eax
    movzbl (%rdi,%r10,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x7,%r10b
    mov %r10b,(%rdx,%r9,1)
    inc %r9
    cmp %r9,%r8
    jne ff_aac_sbr_decode_extension.Laed
ff_aac_sbr_decode_extension.Lb1a:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %edx,%edx
    cmp %esi,%eax
    setl %dl
    add %eax,%edx
    movzbl (%rdi,%rcx,1),%r8d
    mov %edx,-0x38(%rbp)
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r8d
    test %r8b,%r8b
    jns ff_aac_sbr_decode_extension.L4e2
ff_aac_sbr_decode_extension.Lb40:
    mov %edx,%eax
    shr $0x3,%eax
    mov (%rdi,%rax,1),%eax
    bswap %eax
    mov %edx,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1c,%eax
    add $0x4,%edx
    cmp %edx,%esi
    cmovb %esi,%edx
    mov %edx,-0x38(%rbp)
    cmp $0xf,%eax
    jne ff_aac_sbr_decode_extension.Lb86
ff_aac_sbr_decode_extension.Lb64:
    mov %edx,%eax
    shr $0x3,%eax
    mov (%rdi,%rax,1),%eax
    bswap %eax
    mov %edx,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x18,%eax
    add $0x8,%edx
    cmp %edx,%esi
    cmovb %esi,%edx
    mov %edx,-0x38(%rbp)
    add $0xf,%eax
ff_aac_sbr_decode_extension.Lb86:
    shl $0x3,%eax
    cmp $0x8,%eax
    jl ff_aac_sbr_decode_extension.Lc1c
    lea 0x53f20(%r14),%rbx
    mov -0x48(%rbp),%r13
ff_aac_sbr_decode_extension.Lb9d:
    lea -0x2(%rax),%r12d
    mov -0x38(%rbp),%edx
    mov -0x40(%rbp),%rdi
    mov %edx,%ecx
    shr $0x3,%ecx
    mov (%rdi,%rcx,1),%r8d
    bswap %r8d
    mov %edx,%ecx
    and $0x7,%cl
    shl %cl,%r8d
    mov -0x30(%rbp),%esi
    shr $0x1e,%r8d
    add $0x2,%edx
    cmp %edx,%esi
    cmovb %esi,%edx
    mov %edx,-0x38(%rbp)
    cmp $0x2,%r8d
    jne ff_aac_sbr_decode_extension.Lc41
ff_aac_sbr_decode_extension.Lbd4:
    cmpl $0x0,0x5800(%r13)
    mov 0x8(%r13),%rdi
    je ff_aac_sbr_decode_extension.Lcc0
ff_aac_sbr_decode_extension.Lbe6:
    lea -0x40(%rbp),%rsi
    mov %rbx,%rdx
    mov %r12d,%ecx
    call ff_ps_read_data
ff_aac_sbr_decode_extension.Lbf5:
    sub %eax,%r12d
    mov 0x8(%r13),%rax
    movl $0x1c,0x2b0(%rax)
    movl $0x1,0x8850(%r13)
    mov %r12d,%eax
    cmp $0x7,%r12d
    jg ff_aac_sbr_decode_extension.Lb9d
    jmp ff_aac_sbr_decode_extension.Lc1f
ff_aac_sbr_decode_extension.Lc1c:
    mov %eax,%r12d
ff_aac_sbr_decode_extension.Lc1f:
    test %r12d,%r12d
    js ff_aac_sbr_decode_extension.Lca0
    je ff_aac_sbr_decode_extension.L4e2
    mov -0x30(%rbp),%eax
    add -0x38(%rbp),%r12d
    cmp %r12d,%eax
    cmovb %eax,%r12d
    mov %r12d,-0x38(%rbp)
    jmp ff_aac_sbr_decode_extension.L4e2
ff_aac_sbr_decode_extension.Lc41:
    test %r8d,%r8d
    jne ff_aac_sbr_decode_extension.Lc67
    cmp $0x12,%eax
    ja ff_aac_sbr_decode_extension.Lc67
ff_aac_sbr_decode_extension.Lc4b:
    mov %edx,%eax
    shr $0x3,%eax
    mov (%rdi,%rax,1),%eax
    bswap %eax
    mov %edx,%ecx
    and $0x7,%cl
    shl %cl,%eax
    mov %r12d,%ecx
    neg %cl
    shr %cl,%eax
    test %eax,%eax
    je ff_aac_sbr_decode_extension.Lc83
ff_aac_sbr_decode_extension.Lc67:
    mov -0x48(%rbp),%rax
    mov 0x8(%rax),%rdi
    lea L_str_24(%rip),%rsi
    xor %eax,%eax
    call avpriv_request_sample
ff_aac_sbr_decode_extension.Lc7d:
    mov -0x38(%rbp),%edx
    mov -0x30(%rbp),%esi
ff_aac_sbr_decode_extension.Lc83:
    mov %edx,%eax
    neg %eax
    sub %edx,%esi
    cmp %esi,%r12d
    cmovl %r12d,%esi
    cmp %eax,%r12d
    cmovl %eax,%esi
    add %edx,%esi
    mov %esi,-0x38(%rbp)
    jmp ff_aac_sbr_decode_extension.L4e2
ff_aac_sbr_decode_extension.Lca0:
    mov -0x48(%rbp),%rax
    mov 0x8(%rax),%rdi
    lea L_str_22(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
ff_aac_sbr_decode_extension.Lcbb:
    jmp ff_aac_sbr_decode_extension.L4e2
ff_aac_sbr_decode_extension.Lcc0:
    lea L_str_23(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
ff_aac_sbr_decode_extension.Lcd3:
    mov -0x38(%rbp),%eax
    mov -0x30(%rbp),%ecx
    mov %eax,%edx
    neg %edx
    sub %eax,%ecx
    cmp %ecx,%r12d
    cmovl %r12d,%ecx
    cmp %edx,%r12d
    cmovl %edx,%ecx
    add %eax,%ecx
    mov %ecx,-0x38(%rbp)
    jmp ff_aac_sbr_decode_extension.L4e2
ff_aac_sbr_decode_extension.Lcf6:
    ud1 0x12(%eax),%eax
    int3
    int3
    int3
    int3
    int3
")

end Kraken.Examples.Sbr.DecExt

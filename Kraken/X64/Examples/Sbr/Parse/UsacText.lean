import Kraken.X64.Parser

/-!
# `ff_aac_sbr_decode_usac_data`, `ff_aac_sbr_config_usac`: program text

The compiled `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, sbr_ch, indep_flag)` and
`ff_aac_sbr_config_usac(ac, che, ue)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1, `aacsbr.o`,
see `scripts/sbr/README.md`), from `scripts/sbr/parse/usac/gen.py`: the labels are the objdump
labels plus cut points (each call ends a block; at most two stores per straight-line block).
-/

open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.Usac

def cbody : Program := parse("
ff_aac_sbr_config_usac:
    movq $0x0,0x28924(%rsi)
    movl $0x0,0x28930(%rsi)
    movl $0x20,0x28978(%rsi)
    movl $0x0,0x28980(%rsi)
    movl $0xffffffff,0x41d68(%rsi)
    movl $0xffffffff,0x2c2a8(%rsi)
    movl $0xffffffff,0x2893c(%rsi)
    movw $0xffff,0x28940(%rsi)
    xor %eax,%eax
ff_aac_sbr_config_usac.done:
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
    int3
    int3
")

def body : Program := parse("
ff_aac_sbr_decode_usac_data:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x18,%rsp
ff_aac_sbr_decode_usac_data.L3361:
    mov %r8d,%r15d
    mov %rcx,%r14
    mov %rsi,%rbx
    mov %rdi,%r12
    lea 0x28920(%rsi),%r13
    movl $0x0,0x28938(%rsi)
    movl $0x1,0x28930(%rsi)
ff_aac_sbr_decode_usac_data.L3388:
    mov 0x57f4(%rdi),%eax
    mov %eax,0x28920(%rsi)
    xor %eax,%eax
    cmp $0x2,%r8d
    sete %al
    mov %eax,0x2892c(%rsi)
ff_aac_sbr_decode_usac_data.L33a3:
    mov 0x8(%rcx),%ecx
    mov (%r14),%rsi
    mov %r9d,-0x2c(%rbp)
    test %r9d,%r9d
    je ff_aac_sbr_decode_usac_data.L33ba
    mov 0x10(%r14),%edi
    xor %eax,%eax
    jmp ff_aac_sbr_decode_usac_data.L3410
ff_aac_sbr_decode_usac_data.L33ba:
    mov %ecx,%r8d
    shr $0x3,%r8d
    mov 0x10(%r14),%edi
    xor %eax,%eax
    cmp %edi,%ecx
    setl %al
    add %ecx,%eax
    movzbl (%rsi,%r8,1),%r8d
    mov %eax,0x8(%r14)
    and $0x7,%cl
    shl %cl,%r8d
    test %r8b,%r8b
    jns ff_aac_sbr_decode_usac_data.L35bf
ff_aac_sbr_decode_usac_data.L33e6:
    mov %eax,%ecx
    shr $0x3,%ecx
    xor %r8d,%r8d
    cmp %edi,%eax
    setl %r8b
    add %eax,%r8d
    movzbl (%rsi,%rcx,1),%r9d
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%r9d
    mov %r8,%rcx
    mov %ecx,0x8(%r14)
    test %r9b,%r9b
    setns %al
ff_aac_sbr_decode_usac_data.L3410:
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %r9d,%r9d
    cmp %edi,%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rsi,%r8,1),%esi
    and $0x7,%cl
    shl %cl,%esi
    shr $0x7,%esi
    mov %r9d,0x8(%r14)
    and $0x1,%esi
    mov %esi,0x28944(%rbx)
ff_aac_sbr_decode_usac_data.L343d:
    mov 0x8(%r14),%esi
    mov 0x10(%r14),%edi
    mov (%r14),%rcx
    mov %esi,%r8d
    shr $0x3,%r8d
    mov (%rcx,%r8,1),%r8d
    bswap %r8d
    mov %esi,%ecx
    and $0x7,%cl
    shl %cl,%r8d
    shr $0x1c,%r8d
    add $0x4,%esi
    cmp %esi,%edi
    cmovb %edi,%esi
    mov %esi,0x8(%r14)
    mov %r8b,0x2893e(%rbx)
ff_aac_sbr_decode_usac_data.L3475:
    mov 0x8(%r14),%ecx
    mov (%r14),%rsi
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%r14),%ecx
    setl %r8b
    add %ecx,%r8d
    movzbl (%rsi,%rdi,1),%esi
    and $0x7,%cl
    shl %cl,%esi
    shr $0x7,%esi
    mov %r8d,0x8(%r14)
    and $0x1,%esi
    mov %esi,0x28948(%rbx)
    test %al,%al
    jne ff_aac_sbr_decode_usac_data.L35bf
ff_aac_sbr_decode_usac_data.L34b0:
    mov 0x8(%r14),%ecx
    mov (%r14),%rax
    mov %ecx,%esi
    shr $0x3,%esi
    xor %edi,%edi
    cmp 0x10(%r14),%ecx
    setl %dil
    add %ecx,%edi
    movzbl (%rax,%rsi,1),%eax
    mov %edi,0x8(%r14)
    and $0x7,%cl
    shl %cl,%eax
    test %al,%al
    jns ff_aac_sbr_decode_usac_data.L35a5
ff_aac_sbr_decode_usac_data.L34dd:
    mov 0x2894c(%rbx),%eax
    movzwl 0x28940(%rbx),%ecx
    mov %cx,-0x30(%rbp)
    mov 0x2893c(%rbx),%ecx
    mov %ecx,-0x34(%rbp)
ff_aac_sbr_decode_usac_data.L34f7:
    mov 0xc(%rdx),%ecx
    shr $1,%ecx
    and $0x1,%ecx
    mov %ecx,0x28934(%rbx)
    movzbl 0xd(%rdx),%ecx
    mov %cl,0x2893c(%rbx)
ff_aac_sbr_decode_usac_data.L350f:
    movzbl 0xe(%rdx),%ecx
    mov %cl,0x2893d(%rbx)
    movzbl 0xf(%rdx),%ecx
    mov %cl,0x2893f(%rbx)
ff_aac_sbr_decode_usac_data.L3523:
    movzbl 0x10(%rdx),%ecx
    and $0x1,%cl
    mov %cl,0x28940(%rbx)
    movzbl 0x11(%rdx),%ecx
    mov %cl,0x28941(%rbx)
ff_aac_sbr_decode_usac_data.L353a:
    movzbl 0x12(%rdx),%ecx
    mov %ecx,0x2894c(%rbx)
    movzbl 0x13(%rdx),%esi
    mov %esi,0x28950(%rbx)
ff_aac_sbr_decode_usac_data.L354e:
    movzbl 0x14(%rdx),%esi
    and $0x1,%esi
    mov %esi,0x28954(%rbx)
    mov 0x14(%rdx),%edx
    shr $1,%edx
    and $0x1,%edx
    mov %edx,0x28958(%rbx)
ff_aac_sbr_decode_usac_data.L3569:
    mov -0x34(%rbp),%edx
    xor 0x2893c(%rbx),%edx
    movzwl -0x30(%rbp),%esi
    xor 0x28940(%rbx),%si
    movzwl %si,%esi
    or %edx,%esi
    je ff_aac_sbr_decode_usac_data.L358e
    movl $0x1,0x28938(%rbx)
ff_aac_sbr_decode_usac_data.L358e:
    cmp %ecx,%eax
    je ff_aac_sbr_decode_usac_data.L35b5
    cmpl $0x0,0x28938(%rbx)
    jne ff_aac_sbr_decode_usac_data.L35b5
ff_aac_sbr_decode_usac_data.L359b:
    mov %r13,%rdi
    call sbr_make_f_tablelim
ff_aac_sbr_decode_usac_data.L35a3:
    jmp ff_aac_sbr_decode_usac_data.L35b5
ff_aac_sbr_decode_usac_data.L35a5:
    mov %r13,%rdi
    mov %r14,%rsi
    mov $0x1,%edx
    call read_sbr_header
ff_aac_sbr_decode_usac_data.L35b5:
    movl $0x1,0x28924(%rbx)
ff_aac_sbr_decode_usac_data.L35bf:
    mov 0x28978(%rbx),%eax
    mov 0x28980(%rbx),%ecx
    mov %eax,0x28974(%rbx)
    mov %ecx,0x2897c(%rbx)
ff_aac_sbr_decode_usac_data.L35d7:
    movl $0x1,0x28984(%rbx)
    cmpl $0x0,0x28938(%rbx)
    je ff_aac_sbr_decode_usac_data.L35f5
ff_aac_sbr_decode_usac_data.L35ea:
    mov %r12,%rdi
    mov %r13,%rsi
    call sbr_reset
ff_aac_sbr_decode_usac_data.L35f5:
    movl $0x1,0x28928(%rbx)
    cmp $0x1,%r15d
    jne ff_aac_sbr_decode_usac_data.L36c7
ff_aac_sbr_decode_usac_data.L3609:
    lea 0x289a0(%rbx),%r15
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    call read_sbr_grid
ff_aac_sbr_decode_usac_data.L3621:
    mov %eax,%ecx
    mov $0xffffffff,%eax
    test %ecx,%ecx
    jne ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3630:
    mov 0x28930(%rbx),%edi
    mov %r14,%rsi
    mov %r15,%rdx
    mov -0x2c(%rbp),%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_usac_data.L3644:
    mov %r13,%rdi
    mov %r14,%rsi
    mov %r15,%rdx
    call read_sbr_invf
ff_aac_sbr_decode_usac_data.L3652:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_usac_data.L3666:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L366e:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_usac_data.L3682:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3aac
ff_aac_sbr_decode_usac_data.L368a:
    mov 0x8(%r14),%ecx
    mov %ecx,%eax
    shr $0x3,%eax
    xor %edx,%edx
    cmp 0x10(%r14),%ecx
    mov (%r14),%rsi
    setl %dl
    add %ecx,%edx
    movzbl (%rsi,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    mov %edx,0x8(%r14)
    and $0x1,%eax
    mov %eax,0x289a4(%rbx)
    jne ff_aac_sbr_decode_usac_data.L3ab1
ff_aac_sbr_decode_usac_data.L36c0:
    xor %eax,%eax
    jmp ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L36c7:
    mov 0x8(%r14),%ecx
    mov %ecx,%eax
    shr $0x3,%eax
    xor %edx,%edx
    cmp 0x10(%r14),%ecx
    mov (%r14),%rsi
    setl %dl
    add %ecx,%edx
    movzbl (%rsi,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    mov %edx,0x8(%r14)
    lea 0x289a0(%rbx),%r15
    test %al,%al
    jns ff_aac_sbr_decode_usac_data.L3933
ff_aac_sbr_decode_usac_data.L36fa:
    movl $0x1,0x2895c(%rbx)
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    call read_sbr_grid
ff_aac_sbr_decode_usac_data.L3715:
    mov %eax,%ecx
    mov $0xffffffff,%eax
    test %ecx,%ecx
    jne ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3724:
    mov 0x3e468(%rbx),%eax
    cmp $0x9,%rax
    jae ff_aac_sbr_decode_usac_data.L3f00
ff_aac_sbr_decode_usac_data.L3734:
    movzbl 0x3e46c(%rbx,%rax,1),%ecx
    mov %cl,0x3e46c(%rbx)
    movzbl 0x53efc(%rbx,%rax,1),%ecx
    mov %cl,0x53f05(%rbx)
ff_aac_sbr_decode_usac_data.L3750:
    xor %ecx,%ecx
    cmp %eax,0x41d68(%rbx)
    setne %cl
    neg %ecx
    mov %ecx,0x41d64(%rbx)
ff_aac_sbr_decode_usac_data.L3763:
    mov 0x289ad(%rbx),%rax
    mov %rax,0x3e46d(%rbx)
    mov 0x3e43c(%rbx),%rax
    mov %rax,0x53efc(%rbx)
ff_aac_sbr_decode_usac_data.L377f:
    movzbl 0x3e444(%rbx),%eax
    mov %al,0x53f04(%rbx)
    movzwl 0x3e446(%rbx),%eax
    mov %ax,0x53f06(%rbx)
ff_aac_sbr_decode_usac_data.L379a:
    movzbl 0x3e448(%rbx),%eax
    mov %al,0x53f08(%rbx)
    mov 0x289a8(%rbx),%eax
    mov %eax,0x3e468(%rbx)
ff_aac_sbr_decode_usac_data.L37b3:
    mov 0x28a04(%rbx),%eax
    mov %eax,0x3e4c4(%rbx)
    mov 0x289b8(%rbx),%eax
    mov %eax,0x3e478(%rbx)
ff_aac_sbr_decode_usac_data.L37cb:
    mov 0x289a0(%rbx),%eax
    mov %eax,0x3e460(%rbx)
    mov 0x2c2a8(%rbx),%eax
    mov %eax,0x41d68(%rbx)
ff_aac_sbr_decode_usac_data.L37e3:
    mov 0x28930(%rbx),%edi
    mov %r14,%rsi
    mov %r15,%rdx
    mov %r15,%r13
    mov -0x2c(%rbp),%r15d
    mov %r15d,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_usac_data.L37fe:
    mov 0x28930(%rbx),%edi
    mov %r14,%rsi
    lea 0x3e460(%rbx),%rdx
    mov %r15d,%ecx
    mov %r13,%r15
    call read_sbr_dtdf
ff_aac_sbr_decode_usac_data.L3819:
    lea 0x28920(%rbx),%r13
    mov %r13,%rdi
    mov %r14,%rsi
    mov %r15,%rdx
    call read_sbr_invf
ff_aac_sbr_decode_usac_data.L382e:
    movzbl 0x3e48b(%rbx),%eax
    mov %al,0x3e490(%rbx)
    mov 0x3e487(%rbx),%eax
    mov %eax,0x3e48c(%rbx)
ff_aac_sbr_decode_usac_data.L3847:
    mov 0x289c7(%rbx),%eax
    mov %eax,0x3e487(%rbx)
    movzbl 0x289cb(%rbx),%eax
    mov %al,0x3e48b(%rbx)
ff_aac_sbr_decode_usac_data.L3860:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_usac_data.L3874:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L387c:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_usac_data.L3890:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3898:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    lea 0x3e460(%rbx),%r15
    mov %r15,%rcx
    mov $0x1,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_usac_data.L38b6:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L38be:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    mov $0x1,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_usac_data.L38d5:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L38dd:
    mov 0x8(%r14),%ecx
    mov %ecx,%eax
    shr $0x3,%eax
    xor %edx,%edx
    cmp 0x10(%r14),%ecx
    mov (%r14),%rsi
    setl %dl
    add %ecx,%edx
    movzbl (%rsi,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    mov %edx,0x8(%r14)
    and $0x1,%eax
    mov %eax,0x289a4(%rbx)
    je ff_aac_sbr_decode_usac_data.L3c4b
ff_aac_sbr_decode_usac_data.L3913:
    movslq 0x74b04(%rbx),%rdx
    test %rdx,%rdx
    jle ff_aac_sbr_decode_usac_data.L3c4b
    cmp $0x1,%edx
    jne ff_aac_sbr_decode_usac_data.L3b98
    xor %eax,%eax
    jmp ff_aac_sbr_decode_usac_data.L3c1c
ff_aac_sbr_decode_usac_data.L3933:
    movl $0x0,0x2895c(%rbx)
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    call read_sbr_grid
ff_aac_sbr_decode_usac_data.L394e:
    mov %eax,%ecx
    mov $0xffffffff,%eax
    test %ecx,%ecx
    jne ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L395d:
    lea 0x3e460(%rbx),%rcx
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    call read_sbr_grid
ff_aac_sbr_decode_usac_data.L3972:
    mov %eax,%ecx
    mov $0xffffffff,%eax
    test %ecx,%ecx
    jne ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3981:
    mov 0x28930(%rbx),%edi
    mov %r14,%rsi
    mov %r15,%rdx
    mov -0x2c(%rbp),%r15d
    mov %r15d,%ecx
    call read_sbr_dtdf
ff_aac_sbr_decode_usac_data.L3999:
    mov 0x28930(%rbx),%edi
    mov %r14,%rsi
    lea 0x3e460(%rbx),%rdx
    mov %r15d,%ecx
    lea 0x289a0(%rbx),%r15
    call read_sbr_dtdf
ff_aac_sbr_decode_usac_data.L39b8:
    mov %r13,%rdi
    mov %r14,%rsi
    mov %r15,%rdx
    call read_sbr_invf
ff_aac_sbr_decode_usac_data.L39c6:
    mov %r13,%rdi
    mov %r14,%rsi
    lea 0x3e460(%rbx),%rdx
    call read_sbr_invf
ff_aac_sbr_decode_usac_data.L39d8:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_usac_data.L39ec:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L39f4:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    lea 0x3e460(%rbx),%rcx
    mov $0x1,%r8d
    call read_sbr_envelope
ff_aac_sbr_decode_usac_data.L3a0f:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3a17:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    mov %r15,%rcx
    xor %r8d,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_usac_data.L3a2b:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3a33:
    mov %r12,%rdi
    mov %r13,%rsi
    mov %r14,%rdx
    lea 0x3e460(%rbx),%rcx
    mov $0x1,%r8d
    call read_sbr_noise
ff_aac_sbr_decode_usac_data.L3a4e:
    test %eax,%eax
    js ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3a56:
    mov 0x8(%r14),%ecx
    mov %ecx,%eax
    shr $0x3,%eax
    xor %edx,%edx
    cmp 0x10(%r14),%ecx
    mov (%r14),%rsi
    setl %dl
    add %ecx,%edx
    movzbl (%rsi,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    mov %edx,0x8(%r14)
    and $0x1,%eax
    mov %eax,0x289a4(%rbx)
    je ff_aac_sbr_decode_usac_data.L3e17
ff_aac_sbr_decode_usac_data.L3a8c:
    movslq 0x74b04(%rbx),%rdx
    test %rdx,%rdx
    jle ff_aac_sbr_decode_usac_data.L3e17
    cmp $0x1,%edx
    jne ff_aac_sbr_decode_usac_data.L3d64
    xor %eax,%eax
    jmp ff_aac_sbr_decode_usac_data.L3de8
ff_aac_sbr_decode_usac_data.L3aac:
    jmp ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3ab1:
    movslq 0x74b04(%rbx),%rsi
    test %rsi,%rsi
    mov $0x0,%eax
    jle ff_aac_sbr_decode_usac_data.L3ef1
    xor %eax,%eax
    cmp $0x1,%esi
    jne ff_aac_sbr_decode_usac_data.L3ad4
    xor %edx,%edx
    jmp ff_aac_sbr_decode_usac_data.L3b61
ff_aac_sbr_decode_usac_data.L3ad4:
    mov %esi,%edi
    and $0x7ffffffe,%edi
    xor %edx,%edx
    nop
ff_aac_sbr_decode_usac_data.L3ae0:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x289d1(%rbx,%rdx,1)
ff_aac_sbr_decode_usac_data.L3b17:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x289d2(%rbx,%rdx,1)
    add $0x2,%rdx
    cmp %rdx,%rdi
    jne ff_aac_sbr_decode_usac_data.L3ae0
    test $0x1,%sil
    je ff_aac_sbr_decode_usac_data.L36c0
ff_aac_sbr_decode_usac_data.L3b61:
    mov 0x8(%r14),%ecx
    mov %ecx,%esi
    shr $0x3,%esi
    xor %edi,%edi
    cmp 0x10(%r14),%ecx
    mov (%r14),%r8
    setl %dil
    add %ecx,%edi
    movzbl (%r8,%rsi,1),%esi
    and $0x7,%cl
    shl %cl,%esi
    mov %edi,0x8(%r14)
    shr $0x7,%sil
    mov %sil,0x289d1(%rbx,%rdx,1)
    jmp ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3b98:
    mov %edx,%esi
    and $0x7ffffffe,%esi
    xor %eax,%eax
ff_aac_sbr_decode_usac_data.L3ba2:
    mov 0x8(%r14),%ecx
    mov (%r14),%rdi
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %r9d,%r9d
    cmp 0x10(%r14),%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rdi,%r8,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r9d,0x8(%r14)
    shr $0x7,%dil
    mov %dil,0x289d1(%rbx,%rax,1)
ff_aac_sbr_decode_usac_data.L3bd8:
    mov 0x8(%r14),%ecx
    mov (%r14),%rdi
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %r9d,%r9d
    cmp 0x10(%r14),%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rdi,%r8,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r9d,0x8(%r14)
    shr $0x7,%dil
    mov %dil,0x289d2(%rbx,%rax,1)
    add $0x2,%rax
    cmp %rax,%rsi
    jne ff_aac_sbr_decode_usac_data.L3ba2
    test $0x1,%dl
    je ff_aac_sbr_decode_usac_data.L3c4b
ff_aac_sbr_decode_usac_data.L3c1c:
    mov 0x8(%r14),%ecx
    mov %ecx,%edx
    shr $0x3,%edx
    xor %esi,%esi
    cmp 0x10(%r14),%ecx
    mov (%r14),%rdi
    setl %sil
    add %ecx,%esi
    movzbl (%rdi,%rdx,1),%edx
    and $0x7,%cl
    shl %cl,%edx
    mov %esi,0x8(%r14)
    shr $0x7,%dl
    mov %dl,0x289d1(%rbx,%rax,1)
ff_aac_sbr_decode_usac_data.L3c4b:
    mov 0x8(%r14),%ecx
    mov (%r14),%rax
    mov %ecx,%edx
    shr $0x3,%edx
    xor %esi,%esi
    cmp 0x10(%r14),%ecx
    setl %sil
    add %ecx,%esi
    movzbl (%rax,%rdx,1),%edx
    and $0x7,%cl
    shl %cl,%edx
    shr $0x7,%edx
    mov %esi,0x8(%r14)
    xor %eax,%eax
    and $0x1,%edx
    mov %edx,0x3e464(%rbx)
    je ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3c84:
    movslq 0x74b04(%rbx),%rsi
    test %rsi,%rsi
    jle ff_aac_sbr_decode_usac_data.L3ef1
    xor %eax,%eax
    cmp $0x1,%esi
    jne ff_aac_sbr_decode_usac_data.L3ca2
ff_aac_sbr_decode_usac_data.L3c9b:
    xor %edx,%edx
    jmp ff_aac_sbr_decode_usac_data.L3d2d
ff_aac_sbr_decode_usac_data.L3ca2:
    mov %esi,%edi
    and $0x7ffffffe,%edi
    xor %edx,%edx
ff_aac_sbr_decode_usac_data.L3cac:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x3e491(%rbx,%rdx,1)
ff_aac_sbr_decode_usac_data.L3ce3:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x3e492(%rbx,%rdx,1)
    add $0x2,%rdx
    cmp %rdx,%rdi
    jne ff_aac_sbr_decode_usac_data.L3cac
ff_aac_sbr_decode_usac_data.L3d23:
    test $0x1,%sil
    je ff_aac_sbr_decode_usac_data.L36c0
ff_aac_sbr_decode_usac_data.L3d2d:
    mov 0x8(%r14),%ecx
    mov %ecx,%esi
    shr $0x3,%esi
    xor %edi,%edi
    cmp 0x10(%r14),%ecx
    mov (%r14),%r8
    setl %dil
    add %ecx,%edi
    movzbl (%r8,%rsi,1),%esi
    and $0x7,%cl
    shl %cl,%esi
    mov %edi,0x8(%r14)
    shr $0x7,%sil
    mov %sil,0x3e491(%rbx,%rdx,1)
    jmp ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3d64:
    mov %edx,%esi
    and $0x7ffffffe,%esi
    xor %eax,%eax
ff_aac_sbr_decode_usac_data.L3d6e:
    mov 0x8(%r14),%ecx
    mov (%r14),%rdi
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %r9d,%r9d
    cmp 0x10(%r14),%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rdi,%r8,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r9d,0x8(%r14)
    shr $0x7,%dil
    mov %dil,0x289d1(%rbx,%rax,1)
ff_aac_sbr_decode_usac_data.L3da4:
    mov 0x8(%r14),%ecx
    mov (%r14),%rdi
    mov %ecx,%r8d
    shr $0x3,%r8d
    xor %r9d,%r9d
    cmp 0x10(%r14),%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rdi,%r8,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r9d,0x8(%r14)
    shr $0x7,%dil
    mov %dil,0x289d2(%rbx,%rax,1)
    add $0x2,%rax
    cmp %rax,%rsi
    jne ff_aac_sbr_decode_usac_data.L3d6e
    test $0x1,%dl
    je ff_aac_sbr_decode_usac_data.L3e17
ff_aac_sbr_decode_usac_data.L3de8:
    mov 0x8(%r14),%ecx
    mov %ecx,%edx
    shr $0x3,%edx
    xor %esi,%esi
    cmp 0x10(%r14),%ecx
    mov (%r14),%rdi
    setl %sil
    add %ecx,%esi
    movzbl (%rdi,%rdx,1),%edx
    and $0x7,%cl
    shl %cl,%edx
    mov %esi,0x8(%r14)
    shr $0x7,%dl
    mov %dl,0x289d1(%rbx,%rax,1)
ff_aac_sbr_decode_usac_data.L3e17:
    mov 0x8(%r14),%ecx
    mov (%r14),%rax
    mov %ecx,%edx
    shr $0x3,%edx
    xor %esi,%esi
    cmp 0x10(%r14),%ecx
    setl %sil
    add %ecx,%esi
    movzbl (%rax,%rdx,1),%edx
    and $0x7,%cl
    shl %cl,%edx
    shr $0x7,%edx
    mov %esi,0x8(%r14)
    xor %eax,%eax
    and $0x1,%edx
    mov %edx,0x3e464(%rbx)
    je ff_aac_sbr_decode_usac_data.L3ef1
ff_aac_sbr_decode_usac_data.L3e50:
    movslq 0x74b04(%rbx),%rsi
    test %rsi,%rsi
    jle ff_aac_sbr_decode_usac_data.L3ef1
    xor %eax,%eax
    cmp $0x1,%esi
    je ff_aac_sbr_decode_usac_data.L3c9b
    mov %esi,%edi
    and $0x7ffffffe,%edi
    xor %edx,%edx
ff_aac_sbr_decode_usac_data.L3e75:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x3e491(%rbx,%rdx,1)
ff_aac_sbr_decode_usac_data.L3eac:
    mov 0x8(%r14),%ecx
    mov (%r14),%r8
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%r14),%ecx
    setl %r10b
    add %ecx,%r10d
    movzbl (%r8,%r9,1),%r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %r10d,0x8(%r14)
    shr $0x7,%r8b
    mov %r8b,0x3e492(%rbx,%rdx,1)
    add $0x2,%rdx
    cmp %rdx,%rdi
    jne ff_aac_sbr_decode_usac_data.L3e75
    jmp ff_aac_sbr_decode_usac_data.L3d23
ff_aac_sbr_decode_usac_data.L3ef1:
    add $0x18,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
ff_aac_sbr_decode_usac_data.done:
    ret
ff_aac_sbr_decode_usac_data.L3f00:
    ud1 0x12(%eax),%eax
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

end Kraken.Examples.Sbr.Usac

import Kraken.X64.Parser

/-!
# `read_sbr_grid`: the program text

The compiled `read_sbr_grid(ac, sbr, gb, ch_data)` of `libavcodec/aacsbr_template.c` (FFmpeg
n8.1, `aacsbr.o`, see `scripts/sbr/README.md`), the pilot of the parser proofs.
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Grid

def body : Program := parse("
read_sbr_grid:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r12
    push %rbx
read_sbr_grid.L440b:
    mov 0x8(%rcx),%r14d
    cmp $0x9,%r14
    jae read_sbr_grid.L50e3
read_sbr_grid.L4419:
    mov %rcx,%rbx
    movzbl 0xc(%rcx,%r14,1),%eax
read_sbr_grid.L4422:
    mov %al,0xc(%rcx)
    mov 0x24(%rsi),%eax
    mov %eax,0x64(%rcx)
read_sbr_grid.L442b:
    movzbl 0x15a9c(%rcx,%r14,1),%eax
read_sbr_grid.L4434:
    mov %al,0x15aa5(%rcx)
read_sbr_grid.L443a:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rax
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%r15d
    bswap %r15d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r15d
    mov 0x10(%rdx),%r8d
    shr $0x1e,%r15d
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov %r9d,0x8(%rdx)
    cmp $0x3,%r15d
    ja read_sbr_grid.L4de0
read_sbr_grid.L4478:
    mov %r15d,%ecx
    lea read_sbr_grid_jt(%rip),%r10
    movslq (%r10,%rcx,4),%rcx
    add %r10,%rcx
    jmp *%rcx
read_sbr_grid.L448b:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov $0x1,%r8d
    mov %eax,%ecx
    shl %cl,%r8
    mov %r9d,0x8(%rdx)
    xor %ecx,%ecx
    cmpl $0x0,0x10(%rsi)
    setne %cl
    lea (%rcx,%rcx,2),%ecx
    add $0x5,%ecx
    cmp %ecx,%r8d
    jle read_sbr_grid.L4cb0
    mov 0x8(%rdi),%rdi
    lea L_str_25(%rip),%rdx
    jmp read_sbr_grid.L4ec4
read_sbr_grid.L44e3:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov %r9d,0x8(%rdx)
    mov %al,0x15a9c(%rbx)
read_sbr_grid.L450e:
    mov 0x8(%rdx),%esi
    mov 0x10(%rdx),%r8d
    mov (%rdx),%rax
    mov %esi,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %esi,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%esi
    cmp %esi,%r8d
    cmovb %r8d,%esi
    mov %esi,0x8(%rdx)
read_sbr_grid.L4539:
    lea 0x1(%rax),%ecx
    mov %ecx,0x8(%rbx)
    cmp $0x9,%ecx
    jae read_sbr_grid.L5118
read_sbr_grid.L4548:
    mov %ecx,%esi
    movb $0x10,0x15a9c(%rbx,%rsi,1)
    test %eax,%eax
    jle read_sbr_grid.L45cb
read_sbr_grid.L4556:
    mov %eax,%eax
    movzbl 0x15a9c(%rbx),%esi
    xor %r8d,%r8d
    nop
read_sbr_grid.L4570:
    mov 0x8(%rdx),%r9d
    mov 0x10(%rdx),%r10d
    mov (%rdx),%rcx
    mov %r9d,%r11d
    shr $0x3,%r11d
    mov (%rcx,%r11,1),%r11d
    bswap %r11d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r11d
    shr $0x1e,%r11d
    add $0x2,%r9d
    cmp %r9d,%r10d
    cmovb %r10d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L45a5:
    add %r11b,%r11b
    add %r11b,%sil
    add $0x2,%sil
    mov %sil,0x15a9d(%rbx,%r8,1)
    inc %r8
    cmp %r8,%rax
    jne read_sbr_grid.L4570
read_sbr_grid.L45bf:
    mov 0x8(%rbx),%ecx
    cmp $0x6,%ecx
    jae read_sbr_grid.L5113
read_sbr_grid.L45cb:
    mov %ecx,%eax
    lea ceil_log2(%rip),%rcx
    movsbl (%rax,%rcx,1),%eax
read_sbr_grid.L45d8:
    mov 0x8(%rdx),%esi
    mov 0x10(%rdx),%r9d
    mov %esi,%r8d
    mov %esi,%ecx
    add %eax,%esi
    neg %al
    mov (%rdx),%r10
    shr $0x3,%r8d
    mov (%r10,%r8,1),%r8d
    bswap %r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %eax,%ecx
    shr %cl,%r8d
    cmp %esi,%r9d
    cmovb %r9d,%esi
    mov %esi,0x8(%rdx)
read_sbr_grid.L460b:
    movslq 0x8(%rbx),%rsi
    test %rsi,%rsi
    jle read_sbr_grid.L4ea2
    cmp $0x1,%esi
    je read_sbr_grid.L4ca9
read_sbr_grid.L4621:
    mov %esi,%r9d
    and $0x7ffffffe,%r9d
    xor %eax,%eax
    nop
read_sbr_grid.L4630:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%r10
    mov %ecx,%r11d
    shr $0x3,%r11d
    xor %r12d,%r12d
    cmp 0x10(%rdx),%ecx
    setl %r12b
    add %ecx,%r12d
    movzbl (%r10,%r11,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    mov %r12d,0x8(%rdx)
    shr $0x7,%r10b
    mov %r10b,0xd(%rbx,%rax,1)
read_sbr_grid.L4662:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%r10
    mov %ecx,%r11d
    shr $0x3,%r11d
    xor %r12d,%r12d
    cmp 0x10(%rdx),%ecx
    setl %r12b
    add %ecx,%r12d
    movzbl (%r10,%r11,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    mov %r12d,0x8(%rdx)
    shr $0x7,%r10b
    mov %r10b,0xe(%rbx,%rax,1)
read_sbr_grid.L4694:
    add $0x2,%rax
    cmp %rax,%r9
    jne read_sbr_grid.L4630
    jmp read_sbr_grid.L4e6d
read_sbr_grid.L46a2:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov %r9d,0x8(%rdx)
    mov %al,0x15a9c(%rbx)
read_sbr_grid.L46cd:
    mov 0x8(%rdx),%r9d
    mov 0x10(%rdx),%r10d
    mov (%rdx),%rax
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%r8d
    bswap %r8d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r8d
    shr $0x1e,%r8d
    add $0x2,%r9d
    cmp %r9d,%r10d
    cmovb %r10d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4701:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%esi
    bswap %esi
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%esi
    shr $0x1e,%esi
    add $0x2,%r9d
    cmp %r9d,%r10d
    cmovb %r10d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4726:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%r9d
    cmp %r9d,%r10d
    cmovb %r10d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L474b:
    lea (%rax,%rsi,1),%r9d
    lea (%rax,%rsi,1),%ecx
    inc %ecx
    cmp $0x5,%r9d
    jl read_sbr_grid.L4925
    mov 0x8(%rdi),%rdi
    lea L_str_26(%rip),%rdx
    mov $0x10,%esi
    jmp read_sbr_grid.L4ecc
read_sbr_grid.L4773:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%esi
    bswap %esi
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%esi
    shr $0x1e,%esi
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4798:
    mov %r9d,%ecx
    shr $0x3,%ecx
    mov (%rax,%rcx,1),%eax
    bswap %eax
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%eax
    shr $0x1e,%eax
    add $0x2,%r9d
    cmp %r9d,%r8d
    cmovb %r8d,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L47bd:
    lea 0x1(%rax),%ecx
    mov %ecx,0x8(%rbx)
    movb $0x0,0x15a9c(%rbx)
    cmp $0x9,%ecx
    jae read_sbr_grid.L511d
read_sbr_grid.L47d3:
    mov %ecx,%r8d
    add $0x10,%sil
    mov %sil,0x15a9c(%rbx,%r8,1)
    test %eax,%eax
    jle read_sbr_grid.L4873
read_sbr_grid.L47ea:
    neg %eax
    xor %esi,%esi
    nop
read_sbr_grid.L47f0:
    add %esi,%ecx
    cmp $0x9,%ecx
    jae read_sbr_grid.L50cf
read_sbr_grid.L47fb:
    mov %ecx,%ecx
    movzbl 0x15a9c(%rbx,%rcx,1),%r8d
read_sbr_grid.L4806:
    mov 0x8(%rdx),%r10d
    mov 0x10(%rdx),%r11d
    mov (%rdx),%rcx
    mov %r10d,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %r10d,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x1e,%r9d
    add $0x2,%r10d
    cmp %r10d,%r11d
    cmovb %r11d,%r10d
    mov %r10d,0x8(%rdx)
read_sbr_grid.L483b:
    mov 0x8(%rbx),%ecx
    lea (%rsi,%rcx,1),%r10d
    dec %r10d
    cmp $0x9,%r10d
    jae read_sbr_grid.L50ca
read_sbr_grid.L484f:
    mov %r10d,%r10d
    add %r9b,%r9b
    sub %r9b,%r8b
    add $0xfe,%r8b
    mov %r8b,0x15a9c(%rbx,%r10,1)
    dec %esi
    cmp %esi,%eax
    jne read_sbr_grid.L47f0
read_sbr_grid.L486a:
    cmp $0x6,%ecx
    jae read_sbr_grid.L5122
read_sbr_grid.L4873:
    mov %ecx,%eax
    lea ceil_log2(%rip),%rcx
    movsbl (%rax,%rcx,1),%eax
read_sbr_grid.L4880:
    mov 0x8(%rdx),%esi
    mov 0x10(%rdx),%r9d
    mov %esi,%r8d
    mov %esi,%ecx
    add %eax,%esi
    neg %al
    mov (%rdx),%r10
    shr $0x3,%r8d
    mov (%r10,%r8,1),%r8d
    bswap %r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %eax,%ecx
    shr %cl,%r8d
    cmp %esi,%r9d
    cmovb %r9d,%esi
    mov %esi,0x8(%rdx)
read_sbr_grid.L48b3:
    cmpl $0x0,0x8(%rbx)
    je read_sbr_grid.L4ea2
    xor %eax,%eax
    xor %esi,%esi
    nop
read_sbr_grid.L48d0:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    movzbl (%r9,%r10,1),%r9d
    xor %r10d,%r10d
    cmp 0x10(%rdx),%ecx
    setl %r10b
    add %ecx,%r10d
    mov %r10d,0x8(%rdx)
read_sbr_grid.L48f3:
    mov 0x8(%rbx),%r10d
    lea (%rax,%r10,1),%r11d
    cmp $0x9,%r11d
    jae read_sbr_grid.L50d4
read_sbr_grid.L4905:
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,%ecx
    shr $0x7,%r9b
    mov %r9b,0xc(%rbx,%rcx,1)
    inc %esi
    dec %eax
    cmp %r10d,%esi
    jb read_sbr_grid.L48d0
    jmp read_sbr_grid.L4ea2
read_sbr_grid.L4925:
    mov %ecx,0x8(%rbx)
    cmp $0x9,%ecx
    jae read_sbr_grid.L5127
    mov %ecx,%r9d
    add $0x10,%r8b
    mov %r8b,0x15a9c(%rbx,%r9,1)
    test %esi,%esi
    jle read_sbr_grid.L4bbc
read_sbr_grid.L4948:
    mov 0x8(%rdx),%r9d
    mov 0x10(%rdx),%r10d
    mov (%rdx),%rcx
    mov %r9d,%r8d
    shr $0x3,%r8d
    mov (%rcx,%r8,1),%r8d
    bswap %r8d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r8d
    shr $0x1e,%r8d
    add $0x2,%r9d
    cmp %r9d,%r10d
    cmovb %r10d,%r9d
read_sbr_grid.L4979:
    add %r8b,%r8b
    add 0x15a9c(%rbx),%r8b
    mov %r9d,0x8(%rdx)
    add $0x2,%r8b
    mov %r8b,0x15a9d(%rbx)
    cmp $0x1,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L499b:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L49cf:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15a9e(%rbx)
    cmp $0x2,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L49e9:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4a1d:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15a9f(%rbx)
    cmp $0x3,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L4a37:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4a6b:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15aa0(%rbx)
    cmp $0x4,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L4a85:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4ab9:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15aa1(%rbx)
    cmp $0x5,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L4ad3:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4b07:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15aa2(%rbx)
    cmp $0x6,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L4b21:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4b55:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15aa3(%rbx)
    cmp $0x7,%esi
    je read_sbr_grid.L4bb9
read_sbr_grid.L4b6b:
    mov 0x8(%rdx),%r9d
    mov (%rdx),%rcx
    mov %r9d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r9d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    mov 0x10(%rdx),%ecx
    shr $0x1e,%r10d
    add $0x2,%r9d
    cmp %r9d,%ecx
    cmovb %ecx,%r9d
    mov %r9d,0x8(%rdx)
read_sbr_grid.L4b9f:
    add %r10b,%r10b
    add %r10b,%r8b
    add $0x2,%r8b
    mov %r8b,0x15aa4(%rbx)
    cmp $0x8,%esi
    jne read_sbr_grid.L513b
read_sbr_grid.L4bb9:
    mov 0x8(%rbx),%ecx
read_sbr_grid.L4bbc:
    test %eax,%eax
    jle read_sbr_grid.L4c4a
    neg %eax
    xor %esi,%esi
    nop
read_sbr_grid.L4bd0:
    add %esi,%ecx
    cmp $0x9,%ecx
    jae read_sbr_grid.L50de
read_sbr_grid.L4bdb:
    mov %ecx,%ecx
    movzbl 0x15a9c(%rbx,%rcx,1),%r8d
read_sbr_grid.L4be6:
    mov 0x8(%rdx),%r10d
    mov 0x10(%rdx),%r11d
    mov (%rdx),%rcx
    mov %r10d,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %r10d,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x1e,%r9d
    add $0x2,%r10d
    cmp %r10d,%r11d
    cmovb %r11d,%r10d
    mov %r10d,0x8(%rdx)
read_sbr_grid.L4c1b:
    mov 0x8(%rbx),%ecx
    lea (%rsi,%rcx,1),%r10d
    dec %r10d
    cmp $0x9,%r10d
    jae read_sbr_grid.L50d9
read_sbr_grid.L4c2f:
    mov %r10d,%r10d
    add %r9b,%r9b
    sub %r9b,%r8b
    add $0xfe,%r8b
    mov %r8b,0x15a9c(%rbx,%r10,1)
    dec %esi
    cmp %esi,%eax
    jne read_sbr_grid.L4bd0
read_sbr_grid.L4c4a:
    cmp $0x6,%ecx
    jae read_sbr_grid.L512c
read_sbr_grid.L4c53:
    mov %ecx,%eax
    lea ceil_log2(%rip),%rcx
read_sbr_grid.L4c5c:
    movsbl (%rax,%rcx,1),%eax
    mov 0x8(%rdx),%esi
    mov 0x10(%rdx),%r9d
    mov %esi,%r8d
    mov %esi,%ecx
    add %eax,%esi
    neg %al
    mov (%rdx),%r10
    shr $0x3,%r8d
    mov (%r10,%r8,1),%r8d
    bswap %r8d
    and $0x7,%cl
    shl %cl,%r8d
    mov %eax,%ecx
    shr %cl,%r8d
    cmp %esi,%r9d
    cmovb %r9d,%esi
    mov %esi,0x8(%rdx)
read_sbr_grid.L4c93:
    movslq 0x8(%rbx),%rsi
    test %rsi,%rsi
    jle read_sbr_grid.L4ea2
    cmp $0x1,%esi
    jne read_sbr_grid.L4df1
read_sbr_grid.L4ca9:
    xor %eax,%eax
    jmp read_sbr_grid.L4e73
read_sbr_grid.L4cb0:
    mov %r8d,0x8(%rbx)
    test %eax,%eax
    je read_sbr_grid.L4cc9
    movb $0x0,0x15a9c(%rbx)
    cmp $0x4,%eax
    jb read_sbr_grid.L4cd7
    ud1 0x12(%eax),%eax
read_sbr_grid.L4cc9:
    movl $0x0,0x64(%rbx)
    movb $0x0,0x15a9c(%rbx)
read_sbr_grid.L4cd7:
    lea -0x1(%r8),%r9d
    movb $0x10,0x15a9c(%rbx,%r8,1)
    mov %r8d,%esi
    shr $1,%esi
    add $0x10,%sil
    mov %eax,%ecx
    shr %cl,%sil
    test %r9d,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4cfb:
    lea -0xa(%r8),%eax
    cmp $0xfffffff8,%eax
    jb read_sbr_grid.L5131
read_sbr_grid.L4d08:
    mov %sil,0x15a9d(%rbx)
    cmp $0x1,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d15:
    lea (%rsi,%rsi,1),%eax
    mov %al,0x15a9e(%rbx)
    cmp $0x2,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d24:
    movzbl %sil,%eax
    lea (%rax,%rax,2),%ecx
    mov %cl,0x15a9f(%rbx)
    cmp $0x3,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d37:
    lea 0x0(,%rsi,4),%ecx
    mov %cl,0x15aa0(%rbx)
    cmp $0x4,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d4a:
    lea (%rax,%rax,4),%ecx
    mov %cl,0x15aa1(%rbx)
    cmp $0x5,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d59:
    lea (%rax,%rax,1),%ecx
    lea (%rcx,%rcx,2),%ecx
    mov %cl,0x15aa2(%rbx)
    cmp $0x6,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d6b:
    lea 0x0(,%rax,8),%ecx
    sub %eax,%ecx
    mov %cl,0x15aa3(%rbx)
    cmp $0x7,%r9d
    je read_sbr_grid.L4d8b
read_sbr_grid.L4d80:
    shl $0x3,%sil
    mov %sil,0x15aa4(%rbx)
read_sbr_grid.L4d8b:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%rax
    mov %ecx,%esi
    shr $0x3,%esi
    xor %r8d,%r8d
    cmp 0x10(%rdx),%ecx
    setl %r8b
    add %ecx,%r8d
    movzbl (%rax,%rsi,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    mov %r8d,0x8(%rdx)
    shr $0x7,%al
    mov %al,0xd(%rbx)
read_sbr_grid.L4db6:
    mov 0x8(%rbx),%edx
    cmp $0x2,%rdx
    jb read_sbr_grid.L4de0
read_sbr_grid.L4dbf:
    lea -0x9(%rdx),%ecx
    cmp $0xfffffff9,%ecx
    jb read_sbr_grid.L5136
read_sbr_grid.L4dcb:
    mov %rdi,%r12
    lea 0xe(%rbx),%rdi
    dec %rdx
    movzbl %al,%esi
    call memset
read_sbr_grid.L4ddd:
    mov %r12,%rdi
read_sbr_grid.L4de0:
    mov %r15d,(%rbx)
    mov 0x8(%rbx),%ecx
    lea 0x1(%rcx),%eax
    xor %r8d,%r8d
    jmp read_sbr_grid.L4ed8
read_sbr_grid.L4df1:
    mov %esi,%r9d
    and $0x7ffffffe,%r9d
    xor %eax,%eax
    nop
read_sbr_grid.L4e00:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%r10
    mov %ecx,%r11d
    shr $0x3,%r11d
    xor %r12d,%r12d
    cmp 0x10(%rdx),%ecx
    setl %r12b
    add %ecx,%r12d
    movzbl (%r10,%r11,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    mov %r12d,0x8(%rdx)
    shr $0x7,%r10b
    mov %r10b,0xd(%rbx,%rax,1)
read_sbr_grid.L4e32:
    mov 0x8(%rdx),%ecx
    mov (%rdx),%r10
    mov %ecx,%r11d
    shr $0x3,%r11d
    xor %r12d,%r12d
    cmp 0x10(%rdx),%ecx
    setl %r12b
    add %ecx,%r12d
    movzbl (%r10,%r11,1),%r10d
    and $0x7,%cl
    shl %cl,%r10d
    mov %r12d,0x8(%rdx)
    shr $0x7,%r10b
    mov %r10b,0xe(%rbx,%rax,1)
read_sbr_grid.L4e64:
    add $0x2,%rax
    cmp %rax,%r9
    jne read_sbr_grid.L4e00
read_sbr_grid.L4e6d:
    test $0x1,%sil
    je read_sbr_grid.L4ea2
read_sbr_grid.L4e73:
    mov 0x8(%rdx),%ecx
    mov %ecx,%esi
    shr $0x3,%esi
    xor %r9d,%r9d
    cmp 0x10(%rdx),%ecx
    mov (%rdx),%r10
    setl %r9b
    add %ecx,%r9d
    movzbl (%r10,%rsi,1),%esi
    and $0x7,%cl
    shl %cl,%esi
    mov %r9d,0x8(%rdx)
    shr $0x7,%sil
    mov %sil,0xd(%rbx,%rax,1)
read_sbr_grid.L4ea2:
    mov %r15d,(%rbx)
    test %r8d,%r8d
    js read_sbr_grid.L50e8
    mov 0x8(%rbx),%ecx
    lea 0x1(%rcx),%eax
    cmp %eax,%r8d
    jbe read_sbr_grid.L4ed8
    mov 0x8(%rdi),%rdi
    lea L_str_28(%rip),%rdx
read_sbr_grid.L4ec4:
    mov $0x10,%esi
    mov %r8d,%ecx
read_sbr_grid.L4ecc:
    xor %eax,%eax
    call av_log
read_sbr_grid.L4ed3:
    jmp read_sbr_grid.L5086
read_sbr_grid.L4ed8:
    test %ecx,%ecx
    je read_sbr_grid.L4f51
    movzbl 0x15a9c(%rbx),%edx
    movzbl 0x15a9d(%rbx),%esi
    cmp %sil,%dl
    jae read_sbr_grid.L506f
    cmp $0x2,%eax
    jne read_sbr_grid.L4fd3
read_sbr_grid.L4efc:
    xor %esi,%esi
    cmp $0x1,%ecx
    setne %sil
    lea 0x1(%rsi),%edi
    mov %edi,0x18(%rbx)
    mov %dl,0x15aa6(%rbx)
read_sbr_grid.L4f11:
    mov %ecx,%edx
    movzbl 0x15a9c(%rbx,%rdx,1),%edx
    mov %dl,0x15aa7(%rsi,%rbx,1)
read_sbr_grid.L4f22:
    cmp $0x1,%ecx
    je read_sbr_grid.L4f75
read_sbr_grid.L4f27:
    test %r15d,%r15d
    je read_sbr_grid.L5094
    test $0x1,%r15b
    jne read_sbr_grid.L509b
    test %r8d,%r8d
    je read_sbr_grid.L50ae
    cmp $0x1,%r8d
    jne read_sbr_grid.L50b8
    dec %ecx
    jmp read_sbr_grid.L4f65
read_sbr_grid.L4f51:
    movzbl 0x15a9c(%rbx),%edx
    movl $0x1,0x18(%rbx)
    mov %dl,0x15aa6(%rbx)
read_sbr_grid.L4f65:
    mov %ecx,%ecx
    movzbl 0x15a9c(%rbx,%rcx,1),%ecx
    mov %cl,0x15aa7(%rbx)
read_sbr_grid.L4f75:
    xor %ecx,%ecx
    cmp %r14d,0x3908(%rbx)
    setne %cl
    neg %ecx
    mov %ecx,0x3904(%rbx)
    movl $0xffffffff,0x3908(%rbx)
read_sbr_grid.L4f93:
    test %r8d,%r8d
    je read_sbr_grid.L4fae
    test $0x1,%r15b
    je read_sbr_grid.L4fae
    sub %r8d,%eax
    mov %eax,0x3908(%rbx)
    xor %eax,%eax
    jmp read_sbr_grid.L508b
read_sbr_grid.L4fae:
    xor %eax,%eax
    cmp $0x2,%r15d
    jne read_sbr_grid.L508b
    cmp $0x2,%r8d
    jb read_sbr_grid.L508b
    dec %r8d
    mov %r8d,0x3908(%rbx)
    jmp read_sbr_grid.L508b
read_sbr_grid.L4fd3:
    movzbl 0x15a9e(%rbx),%r9d
    cmp %r9b,%sil
    jae read_sbr_grid.L506f
    cmp $0x3,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L4fed:
    movzbl 0x15a9f(%rbx),%esi
    cmp %sil,%r9b
    jae read_sbr_grid.L506f
    cmp $0x4,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L5002:
    movzbl 0x15aa0(%rbx),%r9d
    cmp %r9b,%sil
    jae read_sbr_grid.L506f
    cmp $0x5,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L5018:
    movzbl 0x15aa1(%rbx),%esi
    cmp %sil,%r9b
    jae read_sbr_grid.L506f
    cmp $0x6,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L502d:
    movzbl 0x15aa2(%rbx),%r9d
    cmp %r9b,%sil
    jae read_sbr_grid.L506f
    cmp $0x7,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L5043:
    movzbl 0x15aa3(%rbx),%esi
    cmp %sil,%r9b
    jae read_sbr_grid.L506f
    cmp $0x8,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L5058:
    cmp 0x15aa4(%rbx),%sil
    jae read_sbr_grid.L506f
    cmp $0x9,%eax
    je read_sbr_grid.L4efc
read_sbr_grid.L506a:
    ud1 0x12(%eax),%eax
read_sbr_grid.L506f:
    mov 0x8(%rdi),%rdi
    lea L_str_29(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
read_sbr_grid.L5086:
    mov $0xffffffff,%eax
read_sbr_grid.L508b:
    pop %rbx
    pop %r12
    pop %r14
    pop %r15
    pop %rbp
read_sbr_grid.done:
    ret
read_sbr_grid.L5094:
    shr $1,%ecx
    jmp read_sbr_grid.L4f65
read_sbr_grid.L509b:
    cmp $0x3,%r8d
    mov $0x2,%edx
    cmovae %r8d,%edx
    sub %edx,%ecx
    inc %ecx
    jmp read_sbr_grid.L50bc
read_sbr_grid.L50ae:
    mov $0x1,%ecx
    jmp read_sbr_grid.L4f65
read_sbr_grid.L50b8:
    lea -0x1(%r8),%ecx
read_sbr_grid.L50bc:
    cmp $0x9,%ecx
    jb read_sbr_grid.L4f65
    ud1 0x12(%eax),%eax
read_sbr_grid.L50ca:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50cf:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50d4:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50d9:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50de:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50e3:
    ud1 0x12(%eax),%eax
read_sbr_grid.L50e8:
    lea L_str_3(%rip),%rdx
    lea L_str_27(%rip),%rcx
    lea L_str_5(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x2e3,%r9d
    xor %eax,%eax
    call av_log
read_sbr_grid.L510e:
    call abort
read_sbr_grid.L5113:
    ud1 0x12(%eax),%eax
read_sbr_grid.L5118:
    ud1 0x12(%eax),%eax
read_sbr_grid.L511d:
    ud1 0x12(%eax),%eax
read_sbr_grid.L5122:
    ud1 0x12(%eax),%eax
read_sbr_grid.L5127:
    ud1 0x12(%eax),%eax
read_sbr_grid.L512c:
    ud1 0x12(%eax),%eax
read_sbr_grid.L5131:
    ud1 0x12(%eax),%eax
read_sbr_grid.L5136:
    ud1 0x12(%eax),%eax
read_sbr_grid.L513b:
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%ecx
    add $0x2,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rdx)
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
    int3
    int3
    int3
    int3
")

end Kraken.Examples.Sbr.Grid

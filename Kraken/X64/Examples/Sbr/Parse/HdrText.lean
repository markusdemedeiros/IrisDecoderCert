import Kraken.X64.Parser

/-!
# `read_sbr_header`: the program text

`read_sbr_header(sbr, gb, is_usac)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1, `aacsbr.o`, see
`scripts/sbr/README.md`), from `to_program` and `scripts/sbr/parse/hdr/gen.py`.
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Hdr

def body : Program := parse("
read_sbr_header:
    push %rbp
    mov %rsp,%rbp
    push %r14
    push %rbx
    sub $0x10,%rsp
    mov 0x8(%rsi),%ebx
    mov 0x2c(%rdi),%r8d
    movq $0x1,0x4(%rdi)
    mov %edx,0x10(%rdi)
read_sbr_header.Ld1d:
    movzwl 0x20(%rdi),%eax
    mov %ax,-0x14(%rbp)
    mov 0x1c(%rdi),%eax
    mov %eax,-0x18(%rbp)
    mov 0x8(%rsi),%eax
    test %edx,%edx
    je read_sbr_header.Ld91
read_sbr_header.Ld32:
    mov 0x10(%rsi),%edx
    mov (%rsi),%rcx
    mov %eax,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x1c,%r9d
    add $0x4,%eax
    cmp %eax,%edx
    cmovb %edx,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x1c(%rdi)
read_sbr_header.Ld61:
    mov 0x8(%rsi),%eax
    mov (%rsi),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    mov (%rcx,%rdx,1),%edx
    bswap %edx
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%edx
    mov 0x10(%rsi),%ecx
    shr $0x1c,%edx
    add $0x4,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rsi)
    mov %dl,0x1d(%rdi)
    jmp read_sbr_header.Le45
read_sbr_header.Ld91:
    mov (%rsi),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    xor %r9d,%r9d
    cmp 0x10(%rsi),%eax
    setl %r9b
    add %eax,%r9d
    movzbl (%rcx,%rdx,1),%edx
    and $0x7,%al
    mov %eax,%ecx
    shl %cl,%edx
    shr $0x7,%edx
    mov %r9d,0x8(%rsi)
    and $0x1,%edx
    mov %edx,0x24(%rdi)
read_sbr_header.Ldbd:
    mov 0x8(%rsi),%eax
    mov (%rsi),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    mov (%rcx,%rdx,1),%edx
    bswap %edx
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%edx
    mov 0x10(%rsi),%ecx
    shr $0x1c,%edx
    add $0x4,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rsi)
    mov %dl,0x1c(%rdi)
read_sbr_header.Lde8:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%edx
    mov (%rsi),%rcx
    mov %eax,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x1c,%r9d
    add $0x4,%eax
    cmp %eax,%edx
    cmovb %edx,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x1d(%rdi)
read_sbr_header.Le1a:
    mov 0x8(%rsi),%eax
    mov (%rsi),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    mov (%rcx,%rdx,1),%edx
    bswap %edx
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%edx
    mov 0x10(%rsi),%ecx
    shr $0x1d,%edx
    add $0x3,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rsi)
    mov %dl,0x1e(%rdi)
read_sbr_header.Le45:
    mov 0x8(%rsi),%ecx
    mov 0x10(%rsi),%r9d
    add $0x2,%ecx
    cmp %ecx,%r9d
    cmovb %r9d,%ecx
    mov %ecx,0x8(%rsi)
    mov (%rsi),%r10
    mov %ecx,%edx
    shr $0x3,%edx
    xor %eax,%eax
    cmp %r9d,%ecx
    setl %al
    add %ecx,%eax
    movzbl (%r10,%rdx,1),%r14d
    mov %eax,0x8(%rsi)
    mov %eax,%edx
    shr $0x3,%edx
    movzbl (%r10,%rdx,1),%edx
    xor %r11d,%r11d
    cmp %r9d,%eax
    setl %r11b
    add %eax,%r11d
    mov %r11d,0x8(%rsi)
    and $0x7,%cl
    shl %cl,%r14d
    test %r14b,%r14b
    jns read_sbr_header.Lf31
read_sbr_header.Le9d:
    mov %r11d,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %r11d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x1e,%r10d
    add $0x2,%r11d
    cmp %r11d,%r9d
    cmovb %r9d,%r11d
    mov %r11d,0x8(%rsi)
    mov %r10b,0x1f(%rdi)
read_sbr_header.Leca:
    mov 0x8(%rsi),%ecx
    mov %ecx,%r9d
    shr $0x3,%r9d
    xor %r10d,%r10d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r11
    setl %r10b
    add %ecx,%r10d
    movzbl (%r11,%r9,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r10d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x20(%rdi)
read_sbr_header.Lefb:
    mov 0x8(%rsi),%r10d
    mov (%rsi),%rcx
    mov %r10d,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %r10d,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    mov 0x10(%rsi),%ecx
    shr $0x1e,%r9d
    add $0x2,%r10d
    cmp %r10d,%ecx
    cmovb %ecx,%r10d
    mov %r10d,0x8(%rsi)
    jmp read_sbr_header.Lf3a
read_sbr_header.Lf31:
    movw $0x102,0x1f(%rdi)
    mov $0x2,%r9b
read_sbr_header.Lf3a:
    and $0x7,%eax
    mov %r9b,0x21(%rdi)
    mov -0x18(%rbp),%ecx
    xor 0x1c(%rdi),%ecx
    movzwl -0x14(%rbp),%r9d
    xor 0x20(%rdi),%r9w
    movzwl %r9w,%r9d
    or %ecx,%r9d
    je read_sbr_header.Lf61
    movl $0x1,0x18(%rdi)
read_sbr_header.Lf61:
    mov %eax,%ecx
    shl %cl,%edx
    test %dl,%dl
    jns read_sbr_header.L102d
read_sbr_header.Lf6d:
    mov 0x8(%rsi),%eax
    mov (%rsi),%rcx
    mov %eax,%edx
    shr $0x3,%edx
    mov (%rcx,%rdx,1),%edx
    bswap %edx
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%edx
    mov 0x10(%rsi),%ecx
    shr $0x1e,%edx
    add $0x2,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rsi)
    mov %edx,0x2c(%rdi)
read_sbr_header.Lf98:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%edx
    mov (%rsi),%rcx
    mov %eax,%r9d
    shr $0x3,%r9d
    mov (%rcx,%r9,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x1e,%r9d
    add $0x2,%eax
    cmp %eax,%edx
    cmovb %edx,%eax
    mov %eax,0x8(%rsi)
    mov %r9d,0x30(%rdi)
read_sbr_header.Lfca:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%rax
    mov %ecx,%edx
    shr $0x3,%edx
    xor %r9d,%r9d
    cmp 0x10(%rsi),%ecx
    setl %r9b
    add %ecx,%r9d
    movzbl (%rax,%rdx,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    mov %r9d,0x8(%rsi)
    and $0x1,%eax
    mov %eax,0x34(%rdi)
read_sbr_header.Lff8:
    mov 0x8(%rsi),%ecx
    mov %ecx,%eax
    shr $0x3,%eax
    xor %edx,%edx
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %dl
    add %ecx,%edx
    movzbl (%r9,%rax,1),%eax
    and $0x7,%cl
    shl %cl,%eax
    shr $0x7,%eax
    mov %edx,0x8(%rsi)
    and $0x1,%eax
    mov 0x2c(%rdi),%ecx
    mov %eax,0x38(%rdi)
    cmp %r8d,%ecx
    jne read_sbr_header.L1054
    jmp read_sbr_header.L1065
read_sbr_header.L102d:
    movabs $0x200000002,%rax
    mov %rax,0x2c(%rdi)
    movl $0x1,0x34(%rdi)
    mov $0x1,%eax
    mov $0x2,%ecx
    mov %eax,0x38(%rdi)
    cmp %r8d,%ecx
    je read_sbr_header.L1065
read_sbr_header.L1054:
    cmpl $0x0,0x18(%rdi)
    jne read_sbr_header.L1065
read_sbr_header.L105a:
    mov %rsi,%r14
    call sbr_make_f_tablelim
read_sbr_header.L1062:
    mov %r14,%rsi
read_sbr_header.L1065:
    mov 0x8(%rsi),%eax
    sub %ebx,%eax
    add $0x10,%rsp
    pop %rbx
    pop %r14
    pop %rbp
read_sbr_header.done:
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

end Kraken.Examples.Sbr.Hdr

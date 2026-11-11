import Kraken.X64.Parser

/-!
# `read_sbr_invf`: the program text

`read_sbr_invf(sbr, gb, ch_data)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1, `aacsbr.o`, see
`scripts/sbr/README.md`), from `to_program` and `scripts/sbr/parse/hdr/gen.py`.
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Invf

def body : Program := parse("
read_sbr_invf:
    movzbl 0x2b(%rdx),%eax
    mov %al,0x30(%rdx)
    mov 0x27(%rdx),%eax
    mov %eax,0x2c(%rdx)
    cmpl $0x0,0x4c1e8(%rdi)
    je read_sbr_invf.L578f
read_sbr_invf.L564a:
    lea 0x27(%rdx),%rax
    mov 0x8(%rsi),%r8d
    mov 0x10(%rsi),%r9d
    mov (%rsi),%rcx
    mov %r8d,%r10d
    shr $0x3,%r10d
    mov (%rcx,%r10,1),%r10d
    bswap %r10d
    mov %r8d,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x1e,%r10d
    add $0x2,%r8d
    cmp %r8d,%r9d
    cmovb %r9d,%r8d
    mov %r8d,0x8(%rsi)
    mov %r10b,(%rax)
    cmpl $0x1,0x4c1e8(%rdi)
    jbe read_sbr_invf.L578f
read_sbr_invf.L5693:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%r8d
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
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x28(%rdx)
    cmpl $0x3,0x4c1e8(%rdi)
    jb read_sbr_invf.L578f
read_sbr_invf.L56d5:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%r8d
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
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x29(%rdx)
    cmpl $0x4,0x4c1e8(%rdi)
    jb read_sbr_invf.L578f
read_sbr_invf.L5713:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%r8d
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
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x2a(%rdx)
    cmpl $0x5,0x4c1e8(%rdi)
    jb read_sbr_invf.L578f
read_sbr_invf.L5751:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%r8d
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
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,0x8(%rsi)
    mov %r9b,0x2b(%rdx)
    cmpl $0x5,0x4c1e8(%rdi)
    ja read_sbr_invf.L5790
read_sbr_invf.L578f:
read_sbr_invf.done:
    ret
read_sbr_invf.L5790:
    mov 0x8(%rsi),%eax
    mov 0x10(%rsi),%ecx
    add $0x2,%eax
    cmp %eax,%ecx
    cmovb %ecx,%eax
    mov %eax,0x8(%rsi)
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
")

end Kraken.Examples.Sbr.Invf

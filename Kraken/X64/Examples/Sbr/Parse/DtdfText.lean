import Kraken.X64.Parser

/-!
# `read_sbr_dtdf`: the program text

`read_sbr_dtdf(sbr, gb, ch_data, indep_flag)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1,
`aacsbr.o`, see `scripts/sbr/README.md`), output of `scripts/sbr/parse/noise/gen.py` with the
cuts 5202 52d2 5392 5462 54e2 55b2 (the second half of each two-element loop body). In the
object the first argument is `sbr->usac` (the only field of `*sbr` the routine reads).
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Dtdf

def body : Program := parse("
read_sbr_dtdf:
    test %edi,%edi
    je read_sbr_dtdf.L5185
    test %ecx,%ecx
    je read_sbr_dtdf.L51a2
    movb $0x0,0x1c(%rdx)
    mov 0x8(%rdx),%eax
    dec %eax
    test %eax,%eax
    jle read_sbr_dtdf.L5272
    cmp $0x1,%eax
    jne read_sbr_dtdf.L51bf
    xor %eax,%eax
    jmp read_sbr_dtdf.L5243
read_sbr_dtdf.L5185:
    movslq 0x8(%rdx),%rdi
    test %rdi,%rdi
    jle read_sbr_dtdf.L5402
    cmp $0x1,%edi
    jne read_sbr_dtdf.L5347
    xor %eax,%eax
    jmp read_sbr_dtdf.L53d3
read_sbr_dtdf.L51a2:
    movslq 0x8(%rdx),%rdi
    test %rdi,%rdi
    jle read_sbr_dtdf.L5552
    cmp $0x1,%edi
    jne read_sbr_dtdf.L54a2
    xor %eax,%eax
    jmp read_sbr_dtdf.L5523
read_sbr_dtdf.L51bf:
    mov %eax,%edi
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L51d0:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1d(%rdx,%rax,1)
read_sbr_dtdf.L5202:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1e(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L51d0
    test $0x1,%dil
    je read_sbr_dtdf.L5272
read_sbr_dtdf.L5243:
    mov 0x8(%rsi),%ecx
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %r8b
    add %ecx,%r8d
    movzbl (%r9,%rdi,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r8d,0x8(%rsi)
    shr $0x7,%dil
    mov %dil,0x1d(%rdx,%rax,1)
read_sbr_dtdf.L5272:
    movb $0x0,0x25(%rdx)
    mov 0x18(%rdx),%eax
    dec %eax
    test %eax,%eax
    jle read_sbr_dtdf.L5622
    cmp $0x1,%eax
    jne read_sbr_dtdf.L528f
    xor %eax,%eax
    jmp read_sbr_dtdf.L5317
read_sbr_dtdf.L528f:
    mov %eax,%edi
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L52a0:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x26(%rdx,%rax,1)
read_sbr_dtdf.L52d2:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x27(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L52a0
    test $0x1,%dil
    je read_sbr_dtdf.L5622
read_sbr_dtdf.L5317:
    mov 0x8(%rsi),%ecx
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %r8b
    add %ecx,%r8d
    movzbl (%r9,%rdi,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r8d,0x8(%rsi)
    shr $0x7,%dil
    mov %dil,0x26(%rdx,%rax,1)
read_sbr_dtdf.done:
    ret
read_sbr_dtdf.L5347:
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L5360:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1c(%rdx,%rax,1)
read_sbr_dtdf.L5392:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1d(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L5360
    test $0x1,%dil
    je read_sbr_dtdf.L5402
read_sbr_dtdf.L53d3:
    mov 0x8(%rsi),%ecx
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %r8b
    add %ecx,%r8d
    movzbl (%r9,%rdi,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r8d,0x8(%rsi)
    shr $0x7,%dil
    mov %dil,0x1c(%rdx,%rax,1)
read_sbr_dtdf.L5402:
    movslq 0x18(%rdx),%rdi
    test %rdi,%rdi
    jle read_sbr_dtdf.L5622
    cmp $0x1,%edi
    je read_sbr_dtdf.L5564
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L5430:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x25(%rdx,%rax,1)
read_sbr_dtdf.L5462:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x26(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L5430
    jmp read_sbr_dtdf.L55ed
read_sbr_dtdf.L54a2:
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L54b0:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1c(%rdx,%rax,1)
read_sbr_dtdf.L54e2:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x1d(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L54b0
    test $0x1,%dil
    je read_sbr_dtdf.L5552
read_sbr_dtdf.L5523:
    mov 0x8(%rsi),%ecx
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %r8b
    add %ecx,%r8d
    movzbl (%r9,%rdi,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r8d,0x8(%rsi)
    shr $0x7,%dil
    mov %dil,0x1c(%rdx,%rax,1)
read_sbr_dtdf.L5552:
    movslq 0x18(%rdx),%rdi
    test %rdi,%rdi
    jle read_sbr_dtdf.L5622
    cmp $0x1,%edi
    jne read_sbr_dtdf.L556b
read_sbr_dtdf.L5564:
    xor %eax,%eax
    jmp read_sbr_dtdf.L55f3
read_sbr_dtdf.L556b:
    mov %edi,%r8d
    and $0x7ffffffe,%r8d
    xor %eax,%eax
    nop
read_sbr_dtdf.L5580:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x25(%rdx,%rax,1)
read_sbr_dtdf.L55b2:
    mov 0x8(%rsi),%ecx
    mov (%rsi),%r9
    mov %ecx,%r10d
    shr $0x3,%r10d
    xor %r11d,%r11d
    cmp 0x10(%rsi),%ecx
    setl %r11b
    add %ecx,%r11d
    movzbl (%r9,%r10,1),%r9d
    and $0x7,%cl
    shl %cl,%r9d
    mov %r11d,0x8(%rsi)
    shr $0x7,%r9b
    mov %r9b,0x26(%rdx,%rax,1)
    add $0x2,%rax
    cmp %rax,%r8
    jne read_sbr_dtdf.L5580
read_sbr_dtdf.L55ed:
    test $0x1,%dil
    je read_sbr_dtdf.L5622
read_sbr_dtdf.L55f3:
    mov 0x8(%rsi),%ecx
    mov %ecx,%edi
    shr $0x3,%edi
    xor %r8d,%r8d
    cmp 0x10(%rsi),%ecx
    mov (%rsi),%r9
    setl %r8b
    add %ecx,%r8d
    movzbl (%r9,%rdi,1),%edi
    and $0x7,%cl
    shl %cl,%edi
    mov %r8d,0x8(%rsi)
    shr $0x7,%dil
    mov %dil,0x25(%rdx,%rax,1)
read_sbr_dtdf.L5622:
    jmp read_sbr_dtdf.done
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

end Kraken.Examples.Sbr.Dtdf

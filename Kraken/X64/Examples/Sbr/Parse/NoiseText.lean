import Kraken.X64.Parser

/-!
# `read_sbr_noise`: the program text

`read_sbr_noise(ac, sbr, gb, ch_data, ch)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1,
`aacsbr.o`, see `scripts/sbr/README.md`), output of `scripts/sbr/parse/noise/gen.py` with the
cuts 6111 613d 615b 6172 61a9 61d7 61ee 6210 624c 627f 6296 62b8 62f0 6323 633a 635c 6394 63c7
63de 6400 6438 646b 6482 64a4 64dc 651b 6568 657b 659b 65d9 6607 (the prologue in three parts;
each unrolled `delta` element at its `n_q` test, after the first-level window, after the
first-level entry, before the second-level shift; the `f_huff` loop likewise).
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Noise

def body : Program := parse("
read_sbr_noise:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x28,%rsp
read_sbr_noise.L6111:
    mov %rcx,%r9
    test %r8d,%r8d
    setne %cl
    mov 0x3c(%rsi),%eax
    cmp $0x1,%eax
    sete %r11b
    test %eax,%eax
    setne %r10b
    xor %eax,%eax
    cmpl $0x0,0x18(%r9)
    mov $0x0,%r8d
    je read_sbr_noise.L6694
read_sbr_noise.L613d:
    mov %rdi,-0x40(%rbp)
    and %cl,%r11b
    and %cl,%r10b
    lea ff_aac_sbr_vlc(%rip),%rax
    movzbl %r10b,%ecx
    mov 0x40(%rax,%rcx,8),%rdi
    mov %rdi,-0x38(%rbp)
read_sbr_noise.L615b:
    shl $0x4,%ecx
    mov 0x28(%rcx,%rax,1),%r15
    lea 0x15a50(%r9),%rax
    mov %rax,-0x48(%rbp)
    mov %r11b,-0x29(%rbp)
read_sbr_noise.L6172:
    movzbl %r11b,%eax
    mov %eax,-0x30(%rbp)
    lea 0x15a56(%r9),%r13
    xor %r12d,%r12d
    mov %r9,-0x50(%rbp)
    nop
read_sbr_noise.L6190:
    cmpb $0x0,0x25(%r9,%r12,1)
    je read_sbr_noise.L64f0
    cmpl $0x0,0x4c1e8(%rsi)
    je read_sbr_noise.L6640
read_sbr_noise.L61a9:
    lea (%r12,%r12,4),%rbx
    mov -0x48(%rbp),%rax
    movzbl (%rax,%rbx,1),%edi
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r10
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x17,%r9d
read_sbr_noise.L61d7:
    mov %r9d,%ecx
    mov -0x38(%rbp),%r14
    movzwl (%r14,%rcx,4),%r9d
    movswl 0x2(%r14,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L6224
read_sbr_noise.L61ee:
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r9w,%r9d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
read_sbr_noise.L6210:
    mov %r11d,%ecx
    shr %cl,%r10d
    add %r9d,%r10d
    movzwl (%r14,%r10,4),%r9d
    movswl 0x2(%r14,%r10,4),%r11d
read_sbr_noise.L6224:
    add %r11d,%eax
    add -0x48(%rbp),%rbx
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov -0x30(%rbp),%ecx
    shl %cl,%r9d
    mov %eax,0x8(%rdx)
    add %r9b,%dil
    mov %dil,0x5(%rbx)
    cmp $0x1f,%dil
    jae read_sbr_noise.L66c9
read_sbr_noise.L624c:
    cmpl $0x2,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    movzbl 0x1(%rbx),%edi
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r10
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x17,%r9d
read_sbr_noise.L627f:
    mov %r9d,%ecx
    mov -0x38(%rbp),%r14
    movzwl (%r14,%rcx,4),%r9d
    movswl 0x2(%r14,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L62cc
read_sbr_noise.L6296:
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r9w,%r9d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
read_sbr_noise.L62b8:
    mov %r11d,%ecx
    shr %cl,%r10d
    add %r9d,%r10d
    movzwl (%r14,%r10,4),%r9d
    movswl 0x2(%r14,%r10,4),%r11d
read_sbr_noise.L62cc:
    add %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov -0x30(%rbp),%ecx
    shl %cl,%r9d
    mov %eax,0x8(%rdx)
    add %r9b,%dil
    mov %dil,0x6(%rbx)
    cmp $0x1e,%dil
    ja read_sbr_noise.L66c9
read_sbr_noise.L62f0:
    cmpl $0x3,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    movzbl 0x2(%rbx),%edi
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r10
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x17,%r9d
read_sbr_noise.L6323:
    mov %r9d,%ecx
    mov -0x38(%rbp),%r14
    movzwl (%r14,%rcx,4),%r9d
    movswl 0x2(%r14,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L6370
read_sbr_noise.L633a:
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r9w,%r9d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
read_sbr_noise.L635c:
    mov %r11d,%ecx
    shr %cl,%r10d
    add %r9d,%r10d
    movzwl (%r14,%r10,4),%r9d
    movswl 0x2(%r14,%r10,4),%r11d
read_sbr_noise.L6370:
    add %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov -0x30(%rbp),%ecx
    shl %cl,%r9d
    mov %eax,0x8(%rdx)
    add %r9b,%dil
    mov %dil,0x7(%rbx)
    cmp $0x1e,%dil
    ja read_sbr_noise.L66c9
read_sbr_noise.L6394:
    cmpl $0x4,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    movzbl 0x3(%rbx),%edi
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r10
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x17,%r9d
read_sbr_noise.L63c7:
    mov %r9d,%ecx
    mov -0x38(%rbp),%r14
    movzwl (%r14,%rcx,4),%r9d
    movswl 0x2(%r14,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L6414
read_sbr_noise.L63de:
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r9w,%r9d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
read_sbr_noise.L6400:
    mov %r11d,%ecx
    shr %cl,%r10d
    add %r9d,%r10d
    movzwl (%r14,%r10,4),%r9d
    movswl 0x2(%r14,%r10,4),%r11d
read_sbr_noise.L6414:
    add %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov -0x30(%rbp),%ecx
    shl %cl,%r9d
    mov %eax,0x8(%rdx)
    add %r9b,%dil
    mov %dil,0x8(%rbx)
    cmp $0x1e,%dil
    ja read_sbr_noise.L66c9
read_sbr_noise.L6438:
    cmpl $0x5,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    movzbl 0x4(%rbx),%edi
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r10
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r9d
    bswap %r9d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r9d
    shr $0x17,%r9d
read_sbr_noise.L646b:
    mov %r9d,%ecx
    mov -0x38(%rbp),%r14
    movzwl (%r14,%rcx,4),%r9d
    movswl 0x2(%r14,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L64b8
read_sbr_noise.L6482:
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r9w,%r9d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r10,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
read_sbr_noise.L64a4:
    mov %r11d,%ecx
    shr %cl,%r10d
    add %r9d,%r10d
    movzwl (%r14,%r10,4),%r9d
    movswl 0x2(%r14,%r10,4),%r11d
read_sbr_noise.L64b8:
    add %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov -0x30(%rbp),%ecx
    shl %cl,%r9d
    mov %eax,0x8(%rdx)
    add %r9b,%dil
    mov %dil,0x9(%rbx)
    cmp $0x1e,%dil
    ja read_sbr_noise.L66c9
read_sbr_noise.L64dc:
    cmpl $0x6,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    jmp read_sbr_noise.L66d9
    nop
read_sbr_noise.L64f0:
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%edi
    mov (%rdx),%rcx
    mov %eax,%r8d
    shr $0x3,%r8d
    mov (%rcx,%r8,1),%r8d
    bswap %r8d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r8d
    shr $0x1b,%r8d
    add $0x5,%eax
    cmp %eax,%edi
    cmovb %edi,%eax
read_sbr_noise.L651b:
    mov %eax,0x8(%rdx)
    movzbl -0x29(%rbp),%ecx
    shl %cl,%r8d
    lea (%r12,%r12,4),%rax
    mov %r8b,0x15a55(%r9,%rax,1)
    cmpl $0x2,0x4c1e8(%rsi)
    jb read_sbr_noise.L6640
    xor %edi,%edi
read_sbr_noise.L6540:
    movzbl -0x1(%r13,%rdi,1),%r9d
    mov 0x8(%rdx),%eax
    mov 0x10(%rdx),%r8d
    mov (%rdx),%r14
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r14,%rcx,1),%r10d
    bswap %r10d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r10d
    shr $0x17,%r10d
read_sbr_noise.L6568:
    mov %r10d,%ecx
    movzwl (%r15,%rcx,4),%r10d
    movswl 0x2(%r15,%rcx,4),%r11d
    test %r11d,%r11d
    jns read_sbr_noise.L65f0
read_sbr_noise.L657b:
    movswl %r10w,%r10d
    add $0x9,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r14,%rcx,1),%ebx
    bswap %ebx
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%ebx
read_sbr_noise.L659b:
    mov %r11d,%ecx
    shr %cl,%ebx
    add %r10d,%ebx
    movzwl (%r15,%rbx,4),%r10d
    movswl 0x2(%r15,%rbx,4),%ebx
    test %ebx,%ebx
    js read_sbr_noise.L65b7
    mov %ebx,%r11d
    jmp read_sbr_noise.L65f0
read_sbr_noise.L65b7:
    sub %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    movswl %r10w,%r10d
    mov %eax,%ecx
    shr $0x3,%ecx
    mov (%r14,%rcx,1),%r11d
    bswap %r11d
    mov %eax,%ecx
    and $0x7,%cl
    shl %cl,%r11d
read_sbr_noise.L65d9:
    mov %ebx,%ecx
    shr %cl,%r11d
    add %r10d,%r11d
    movzwl (%r15,%r11,4),%r10d
    movswl 0x2(%r15,%r11,4),%r11d
    nop
read_sbr_noise.L65f0:
    add %r11d,%eax
    cmp %eax,%r8d
    cmovb %r8d,%eax
    mov %eax,0x8(%rdx)
    cmp $0x4,%rdi
    je read_sbr_noise.L66cf
read_sbr_noise.L6607:
    mov -0x30(%rbp),%ecx
    shl %cl,%r10d
    add %r10b,%r9b
    mov %r9b,0x0(%r13,%rdi,1)
    cmp $0x1f,%r9b
    jae read_sbr_noise.L6663
    mov 0x4c1e8(%rsi),%eax
    lea 0x1(%rdi),%rcx
    add $0x2,%rdi
    cmp %rax,%rdi
    mov %rcx,%rdi
    jb read_sbr_noise.L6540
    nop
read_sbr_noise.L6640:
    inc %r12
    mov -0x50(%rbp),%r9
    mov 0x18(%r9),%r8d
    cmp %r8,%r12
    jae read_sbr_noise.L6689
    add $0x5,%r13
    cmp $0x2,%r12
    jne read_sbr_noise.L6190
    ud1 0x12(%eax),%eax
read_sbr_noise.L6663:
    movzbl %r9b,%ecx
read_sbr_noise.L6667:
    mov -0x40(%rbp),%rax
    mov 0x8(%rax),%rdi
    lea L_str_31(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
    mov $0xbebbb1b7,%eax
    jmp read_sbr_noise.L66ba
read_sbr_noise.L6689:
    cmp $0x4,%r8d
    mov $0x0,%eax
    jae read_sbr_noise.L66d4
read_sbr_noise.L6694:
    mov %r8d,%ecx
    lea (%rcx,%rcx,4),%rdx
    movzbl 0x15a54(%r9,%rdx,1),%ecx
    mov %cl,0x15a54(%r9)
    mov 0x15a50(%r9,%rdx,1),%ecx
    mov %ecx,0x15a50(%r9)
read_sbr_noise.L66ba:
    add $0x28,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
read_sbr_noise.done:
    ret
read_sbr_noise.L66c9:
    movzbl %dil,%ecx
    jmp read_sbr_noise.L6667
read_sbr_noise.L66cf:
    ud1 0x12(%eax),%eax
read_sbr_noise.L66d4:
    ud1 0x12(%eax),%eax
read_sbr_noise.L66d9:
    ud1 0x12(%eax),%eax
    int3
    int3
")

end Kraken.Examples.Sbr.Noise

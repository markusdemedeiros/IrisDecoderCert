import Kraken.X64.Parser

/-!
# `sbr_make_f_tablelim`: the program text

The compiled `sbr_make_f_tablelim(sbr)` of `libavcodec/aacsbr_template.c` (FFmpeg n8.1,
`aacsbr.o`, see `scripts/sbr/README.md`), from `scripts/sbr/parse/tlim/gen.py`: the objdump labels
plus cut points (each conditional exit of the unrolled patch-border chain, after each call, and
inside the inlined `AV_QSORT` and the compaction loop). `sbr_make_f_tablelim_bw` is
`bands_warped[3]` (`.rodata+0x70` of `aacsbr.o`, no symbol).
-/

open Kraken Kraken.X64.Parser

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

def body : Program := parse("
sbr_make_f_tablelim:
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r12
    push %rbx
    sub $0x420,%rsp
sbr_make_f_tablelim.L3f22:
    mov %rdi,%rbx
    mov 0x2c(%rdi),%eax
    test %rax,%rax
    je sbr_make_f_tablelim.L438a
sbr_make_f_tablelim.L3f31:
    cmp $0x4,%eax
    jae sbr_make_f_tablelim.L43dc
sbr_make_f_tablelim.L3f3a:
    lea sbr_make_f_tablelim_bw(%rip),%rcx
    vmovss -0x4(%rcx,%rax,4),%xmm0
    movzwl 0x58(%rbx),%eax
    mov %ax,-0x2e(%rbp)
    mov 0x4c330(%rbx),%ecx
    test %ecx,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3f59:
    lea -0x7(%rcx),%edx
    cmp $0xfffffffa,%edx
    jb sbr_make_f_tablelim.L43e6
sbr_make_f_tablelim.L3f65:
    movzbl 0x4c334(%rbx),%edx
    add %edx,%eax
    mov %ax,-0x2c(%rbp)
    cmp $0x1,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3f77:
    movzbl 0x4c335(%rbx),%edx
    add %edx,%eax
    mov %ax,-0x2a(%rbp)
    cmp $0x2,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3f89:
    movzbl 0x4c336(%rbx),%edx
    add %edx,%eax
    mov %ax,-0x28(%rbp)
    cmp $0x3,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3f9b:
    movzbl 0x4c337(%rbx),%edx
    add %edx,%eax
    mov %ax,-0x26(%rbp)
    cmp $0x4,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3fad:
    movzbl 0x4c338(%rbx),%edx
    add %edx,%eax
    mov %ax,-0x24(%rbp)
    cmp $0x5,%ecx
    je sbr_make_f_tablelim.L3fcc
sbr_make_f_tablelim.L3fbf:
    movzbl 0x4c339(%rbx),%ecx
    add %ecx,%eax
    mov %ax,-0x22(%rbp)
sbr_make_f_tablelim.L3fcc:
    vmovss %xmm0,-0x34(%rbp)
    lea 0x4c2f2(%rbx),%r14
    lea 0x4c252(%rbx),%rsi
    mov 0x4c1e0(%rbx),%r15d
    lea 0x1(%r15),%edx
    add %rdx,%rdx
    mov %r14,%rdi
    call memcpy
sbr_make_f_tablelim.L3ff5:
    mov 0x4c330(%rbx),%edx
    cmp $0x2,%edx
    jb sbr_make_f_tablelim.L4026
sbr_make_f_tablelim.L4000:
    cmp $0x1f,%r15d
    jae sbr_make_f_tablelim.L43f0
sbr_make_f_tablelim.L400a:
    lea (%r14,%r15,2),%rdi
    add $0x2,%rdi
    lea -0x2c(%rbp),%rsi
    dec %edx
    add %rdx,%rdx
    call memcpy
sbr_make_f_tablelim.L4020:
    mov 0x4c330(%rbx),%edx
sbr_make_f_tablelim.L4026:
    mov %r14,-0x440(%rbp)
    add %edx,%r15d
    cmp $0x1f,%r15d
    vmovss -0x34(%rbp),%xmm2
    jae sbr_make_f_tablelim.L43e1
sbr_make_f_tablelim.L403f:
    lea 0x4c2f4(%rbx),%rax
    mov %r15d,%ecx
    lea (%r14,%rcx,2),%rcx
    add $0xfffffffffffffffe,%rcx
    mov %rcx,-0x438(%rbp)
    mov $0x1,%ecx
    jmp sbr_make_f_tablelim.L4068
    nop
sbr_make_f_tablelim.L4060:
    test %ecx,%ecx
    je sbr_make_f_tablelim.L429d
sbr_make_f_tablelim.L4068:
    cmp $0x41,%ecx
    jae sbr_make_f_tablelim.L43d7
    dec %ecx
    mov %rcx,%rdx
    shl $0x4,%rdx
    mov -0x440(%rbp,%rdx,1),%rsi
    mov -0x438(%rbp,%rdx,1),%rdx
    nop
sbr_make_f_tablelim.L4090:
    cmp %rdx,%rsi
    jae sbr_make_f_tablelim.L4060
    lea -0x2(%rdx),%r8
    cmp %r8,%rsi
    jae sbr_make_f_tablelim.L4280
    mov %rdx,%r9
    sub %rsi,%r9
    sar $0x2,%r9
    lea (%rsi,%r9,2),%rdi
    movzwl (%rsi),%r10d
    movzwl (%rdx),%r11d
    movzwl (%rsi,%r9,2),%r9d
    cmp %r11w,%r10w
    jle sbr_make_f_tablelim.L40e0
sbr_make_f_tablelim.L40c3:
    cmp %r9w,%r11w
    jg sbr_make_f_tablelim.L40ec
sbr_make_f_tablelim.L40c9:
    mov %r10w,(%rdx)
    mov %r11d,%r9d
    jmp sbr_make_f_tablelim.L40f0
    nop
sbr_make_f_tablelim.L40e0:
    mov $0x1,%r11d
    cmp %r9w,%r10w
    jle sbr_make_f_tablelim.L40f7
sbr_make_f_tablelim.L40ec:
    mov %r10w,(%rdi)
sbr_make_f_tablelim.L40f0:
    mov %r9w,(%rsi)
    xor %r11d,%r11d
sbr_make_f_tablelim.L40f7:
    movzwl (%rdi),%r9d
    movzwl (%rdx),%r15d
    cmp %r15w,%r9w
    jle sbr_make_f_tablelim.L4120
sbr_make_f_tablelim.L4105:
    mov %r9w,(%rdx)
    mov %r15w,(%rdi)
    xor %r11d,%r11d
sbr_make_f_tablelim.L4110:
    lea -0x4(%rdx),%r9
    cmp %r9,%rsi
    jne sbr_make_f_tablelim.L4130
    jmp sbr_make_f_tablelim.L4060
    nop
sbr_make_f_tablelim.L4120:
    mov %r9d,%r15d
    lea -0x4(%rdx),%r9
    cmp %r9,%rsi
    je sbr_make_f_tablelim.L4060
sbr_make_f_tablelim.L4130:
    lea 0x2(%rsi),%r10
    movzwl (%r8),%r12d
    mov %r12w,(%rdi)
    mov %r15w,(%r8)
    cmp %r9,%r10
    jbe sbr_make_f_tablelim.L4169
    jmp sbr_make_f_tablelim.L41b4
    nop
sbr_make_f_tablelim.L4150:
    movzwl (%r10),%r15d
    mov %r15w,(%r9)
    mov %r12w,(%r10)
    add $0x2,%r10
    add $0xfffffffffffffffe,%r9
sbr_make_f_tablelim.L4164:
    cmp %r9,%r10
    ja sbr_make_f_tablelim.L41b0
sbr_make_f_tablelim.L4169:
    movzwl (%r8),%r15d
    nop
sbr_make_f_tablelim.L4170:
    cmp %r15w,(%r10)
    jge sbr_make_f_tablelim.L4194
    add $0x2,%r10
    cmp %r9,%r10
    jbe sbr_make_f_tablelim.L4170
    jmp sbr_make_f_tablelim.L4194
    nop
sbr_make_f_tablelim.L4190:
    add $0xfffffffffffffffe,%r9
sbr_make_f_tablelim.L4194:
    cmp %r9,%r10
    ja sbr_make_f_tablelim.L4164
sbr_make_f_tablelim.L4199:
    movzwl (%r9),%r12d
    cmp %r15w,%r12w
    jg sbr_make_f_tablelim.L4190
    jmp sbr_make_f_tablelim.L4150
    nop
sbr_make_f_tablelim.L41b0:
    movzwl (%r8),%r15d
sbr_make_f_tablelim.L41b4:
    movzwl (%r10),%r12d
    mov %r15w,(%r10)
    mov %r12w,(%r8)
    test %r11d,%r11d
    je sbr_make_f_tablelim.L4200
    cmp %r10,%rdi
    je sbr_make_f_tablelim.L41d3
sbr_make_f_tablelim.L41ca:
    lea -0x2(%r10),%r8
    cmp %r8,%rdi
    jne sbr_make_f_tablelim.L4200
sbr_make_f_tablelim.L41d3:
    mov %rsi,%r8
    nop
sbr_make_f_tablelim.L41e0:
    mov %r8,%rdi
    cmp %rdx,%r8
    jae sbr_make_f_tablelim.L41f7
    lea 0x2(%rdi),%r8
    movzwl (%rdi),%r11d
    cmp 0x2(%rdi),%r11w
    jle sbr_make_f_tablelim.L41e0
sbr_make_f_tablelim.L41f7:
    cmp %rdx,%rdi
    je sbr_make_f_tablelim.L4060
sbr_make_f_tablelim.L4200:
    mov %rdx,%rdi
    sub %r10,%rdi
    mov %r10,%r8
    sub %rsi,%r8
    cmp %r8,%rdi
    jge sbr_make_f_tablelim.L4250
sbr_make_f_tablelim.L4211:
    cmp $0x40,%rcx
    jae sbr_make_f_tablelim.L43cd
sbr_make_f_tablelim.L421b:
    mov %rcx,%rdi
    shl $0x4,%rdi
    mov %rsi,-0x440(%rbp,%rdi,1)
    mov %r9,-0x438(%rbp,%rdi,1)
    add $0x2,%r10
    mov %r10,%rsi
    inc %rcx
    jmp sbr_make_f_tablelim.L4090
    nop
sbr_make_f_tablelim.L4250:
    cmp $0x40,%rcx
    jae sbr_make_f_tablelim.L43d2
sbr_make_f_tablelim.L425a:
    add $0x2,%r10
    mov %rcx,%rdi
    shl $0x4,%rdi
    mov %r10,-0x440(%rbp,%rdi,1)
    mov %rdx,-0x438(%rbp,%rdi,1)
    mov %r9,%rdx
    inc %rcx
    jmp sbr_make_f_tablelim.L4090
sbr_make_f_tablelim.L4280:
    movzwl (%rsi),%edi
    movzwl (%rdx),%r8d
    cmp %r8w,%di
    jle sbr_make_f_tablelim.L4060
    mov %di,(%rdx)
    mov %r8w,(%rsi)
    jmp sbr_make_f_tablelim.L4060
sbr_make_f_tablelim.L429d:
    mov 0x4c1e0(%rbx),%ecx
    mov 0x4c330(%rbx),%edx
    add %ecx,%edx
    dec %edx
    mov %edx,0x4c1ec(%rbx)
    cmp $0x1e,%edx
sbr_make_f_tablelim.L42b6:
    ja sbr_make_f_tablelim.L4385
sbr_make_f_tablelim.L42bc:
    mov %r14,%rcx
    jmp sbr_make_f_tablelim.L42eb
    nop
sbr_make_f_tablelim.L42d0:
    mov %si,0x2(%rcx)
    add $0x2,%rcx
    mov 0x4c1ec(%rbx),%edx
    add $0x2,%rax
    cmp $0x1f,%edx
    jae sbr_make_f_tablelim.L4385
sbr_make_f_tablelim.L42eb:
    mov %edx,%esi
    lea (%r14,%rsi,2),%rsi
    cmp %rsi,%rcx
    jae sbr_make_f_tablelim.L43bd
sbr_make_f_tablelim.L42fa:
    movzwl (%rax),%esi
    vcvtsi2ss %esi,%xmm15,%xmm0
    movzwl (%rcx),%edi
    vcvtsi2ss %edi,%xmm15,%xmm1
    vmulss %xmm1,%xmm2,%xmm1
    vucomiss %xmm1,%xmm0
    jae sbr_make_f_tablelim.L42d0
sbr_make_f_tablelim.L4312:
    cmp %di,%si
    je sbr_make_f_tablelim.L4370
sbr_make_f_tablelim.L4317:
    mov 0x4c330(%rbx),%r8d
    test %r8d,%r8d
    js sbr_make_f_tablelim.L4370
sbr_make_f_tablelim.L4323:
    inc %r8
    xor %r9d,%r9d
    nop
sbr_make_f_tablelim.L4330:
    cmp %si,-0x2e(%rbp,%r9,2)
    je sbr_make_f_tablelim.L4342
sbr_make_f_tablelim.L4338:
    inc %r9
    cmp %r9,%r8
    jne sbr_make_f_tablelim.L4330
sbr_make_f_tablelim.L4340:
    jmp sbr_make_f_tablelim.L4370
sbr_make_f_tablelim.L4342:
    xor %edx,%edx
    nop
sbr_make_f_tablelim.L4350:
    cmp %di,-0x2e(%rbp,%rdx,2)
    je sbr_make_f_tablelim.L42d0
sbr_make_f_tablelim.L435b:
    inc %rdx
    cmp %rdx,%r8
    jne sbr_make_f_tablelim.L4350
sbr_make_f_tablelim.L4363:
    mov %si,(%rcx)
    mov 0x4c1ec(%rbx),%edx
    nop
sbr_make_f_tablelim.L4370:
    dec %edx
    mov %edx,0x4c1ec(%rbx)
    add $0x2,%rax
    cmp $0x1f,%edx
    jb sbr_make_f_tablelim.L42eb
sbr_make_f_tablelim.L4385:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L438a:
    movzwl 0x4c252(%rbx),%eax
    mov %ax,0x4c2f2(%rbx)
sbr_make_f_tablelim.L4398:
    mov 0x4c1e0(%rbx),%eax
    cmp $0x19,%rax
    jae sbr_make_f_tablelim.L43eb
sbr_make_f_tablelim.L43a4:
    movzwl 0x4c252(%rbx,%rax,2),%eax
    mov %ax,0x4c2f4(%rbx)
    movl $0x1,0x4c1ec(%rbx)
sbr_make_f_tablelim.L43bd:
    add $0x420,%rsp
    pop %rbx
    pop %r12
    pop %r14
    pop %r15
    pop %rbp
sbr_make_f_tablelim.done:
    ret
sbr_make_f_tablelim.L43cd:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43d2:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43d7:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43dc:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43e1:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43e6:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43eb:
    ud1 0x12(%eax),%eax
sbr_make_f_tablelim.L43f0:
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

end Kraken.Examples.Sbr.Tlim

import Kraken.X64.Parser
import Kraken.Blocks
import Kraken.MachineWP
import Kraken.SysV

/-!
# `ff_aac_sbr_apply`: the program text

`libavcodec/aacsbr_template.c` (FFmpeg n8.1), `ff_aac_sbr_apply(ac, che, id_aac, L, R)`
from the `-c opt` object (`aacsbr.o`). The text is cut into 434 blocks (a label at
every jump target, after every call, and inside long runs); each block's body is a
separate definition `B.<id>` and the text `body` is their concatenation, so the control-flow
rule reads the block list without reducing the text (`Kraken/Rules/CfgTable.lean`).

This module holds the text only and imports only the parser and the machine model; the
translation validation (`scripts/sbr/tv`) compares it with the object. The control-flow
lemmas, the footprint and the table are in `ApplyTable.lean`.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem

namespace Kraken.Examples.Sbr.Apply


namespace B

set_option maxRecDepth 20000 in
/-- asm line 2 (Entry, straight) -/
def start : Program := parse("
    push %rbp
    mov %rsp,%rbp
    push %r15
    push %r14
    push %r13
    push %r12
    push %rbx
    sub $0x198,%rsp
    mov %r8,-0x128(%rbp)
    mov %rcx,-0x130(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 12 (Entry, straight) -/
def start_1 : Program := parse("
    mov 0x57f4(%rdi),%eax
    xor %r14d,%r14d
    cmp 0x28920(%rsi),%eax
    setl -0xf0(%rbp)
    cmp $0x1,%edx
    sete %al
")

set_option maxRecDepth 20000 in
/-- asm line 18 (Entry, straight) -/
def start_2 : Program := parse("
    mov 0x2892c(%rsi),%r8d
    cmp %r8d,%edx
    mov %rsi,-0x38(%rbp)
    mov %rdi,-0x90(%rbp)
    mov %al,-0x39(%rbp)
    mov %edx,-0x9c(%rbp)
    jne ff_aac_sbr_apply.L6797
    mov %rsi,%r9
    mov $0x1,%bl
    cmpl $0x0,0x28924(%rsi)
    je ff_aac_sbr_apply.L6817
    cmpl $0x0,0x28928(%r9)
    je ff_aac_sbr_apply.L6f32
    xor %ebx,%ebx
    cmpl $0x0,0x28984(%r9)
")

set_option maxRecDepth 20000 in
/-- asm line 33 (Entry, straight) -/
def start_3 : Program := parse("
    jne ff_aac_sbr_apply.L6825
")

set_option maxRecDepth 20000 in
/-- asm line 35 (Entry, straight) -/
def L676e : Program := parse("
    mov 0x28978(%r9),%eax
    mov 0x28980(%r9),%ecx
    mov %eax,0x28974(%r9)
    mov %ecx,0x2897c(%r9)
    test %bl,%bl
    jne ff_aac_sbr_apply.L74e9
    jmp ff_aac_sbr_apply.L6838
")

set_option maxRecDepth 20000 in
/-- asm line 43 (Entry, call_avlog) -/
def L6797 : Program := parse("
    mov %edx,%ecx
    mov 0x8(%rdi),%rdi
    xor %esi,%esi
    cmp $0x3,%edx
    sete %sil
    shl $0x4,%esi
    add $0x18,%esi
    lea L_str_1(%rip),%rdx
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 53 (Entry, store_run) -/
def L6797_1 : Program := parse("
    mov -0x38(%rbp),%r9
    movq $0x0,0x28924(%r9)
    movl $0x0,0x28930(%r9)
    movl $0x20,0x28978(%r9)
    movl $0x0,0x28980(%r9)
    movl $0xffffffff,0x41d68(%r9)
    movl $0xffffffff,0x2c2a8(%r9)
    movl $0xffffffff,0x2893c(%r9)
    movw $0xffff,0x28940(%r9)
    mov $0x1,%bl
")

set_option maxRecDepth 20000 in
/-- asm line 64 (Entry, straight) -/
def L6817 : Program := parse("
    cmpl $0x0,0x28984(%r9)
    je ff_aac_sbr_apply.L676e
")

set_option maxRecDepth 20000 in
/-- asm line 67 (Entry, straight) -/
def L6825 : Program := parse("
    movl $0x0,0x28984(%r9)
    test %bl,%bl
    jne ff_aac_sbr_apply.L74e9
")

set_option maxRecDepth 20000 in
/-- asm line 71 (Entry, straight) -/
def L6838 : Program := parse("
    mov $0x1,%eax
    mov %rax,-0xc8(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 73 (Entry, straight) -/
def L6838_1 : Program := parse("
    mov -0x9c(%rbp),%eax
    cmp $0x1,%eax
    jne ff_aac_sbr_apply.L6fca
    cmpl $0x0,0x2895c(%r9)
    je ff_aac_sbr_apply.L6fbe
    cmpl $0x0,0x28a04(%r9)
    mov $0x18,%eax
    mov $0xc,%r15d
    cmove %eax,%r15d
    cmpl $0x0,0x289a8(%r9)
    je ff_aac_sbr_apply.L6abf
    lea 0x53670(%r9),%r12
    lea 0x538b0(%r9),%r13
    mov $0x1,%ebx
    vmovsd LCPI14_4(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 88 (Entry, straight) -/
def L6838_2 : Program := parse("
    vmovss LCPI14_5(%rip),%xmm3
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 91 (DqCplEnv, straight) -/
def L68b0 : Program := parse("
    movzbl 0x289ac(%r9,%rbx,1),%eax
    cmp $0x1,%al
    ja ff_aac_sbr_apply.L6ff7
    xor %r14d,%r14d
    jmp ff_aac_sbr_apply.L68f8
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 98 (DqCplEnv, straight) -/
def L68d0 : Program := parse("
    vaddss %xmm3,%xmm4,%xmm1
    vdivss %xmm1,%xmm0,%xmm0
    vmovss %xmm0,-0x15ac0(%r13,%r14,4)
    vmulss %xmm0,%xmm4,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 102 (DqCplEnv, straight) -/
def L68d0_1 : Program := parse("
    vmovss %xmm0,0x0(%r13,%r14,4)
    inc %r14
    cmp $0x2,%al
    jae ff_aac_sbr_apply.L6ff7
")

set_option maxRecDepth 20000 in
/-- asm line 107 (DqCplEnv, straight) -/
def L68f8 : Program := parse("
    movzbl %al,%ecx
    mov 0x74b00(%r9,%rcx,4),%ecx
    cmp %rcx,%r14
    jae ff_aac_sbr_apply.L6a90
    cmpl $0x0,0x28a04(%r9)
    je ff_aac_sbr_apply.L6940
    cmp $0x30,%r14
    jae ff_aac_sbr_apply.L9b63
    movzbl -0x15ac0(%r12,%r14,1),%ecx
    cmp $0x7a,%ecx
    jb ff_aac_sbr_apply.L69d0
    vmovd LCPI14_0(%rip),%xmm0
    jmp ff_aac_sbr_apply.L69dd
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 122 (DqCplEnv, straight) -/
def L6940 : Program := parse("
    cmp $0x30,%r14
    jae ff_aac_sbr_apply.L9b6d
    movzbl -0x15ac0(%r12,%r14,1),%ecx
    movzbl %cl,%esi
    shr $1,%esi
    add $0x7,%esi
    movzbl (%r12,%r14,1),%edx
    mov %r15d,%edi
    sub %edx,%edi
    vmovd %esi,%xmm0
    vpinsrd $0x1,%edi,%xmm0,%xmm1
    vpslld $0x16,%xmm1,%xmm1
    vpslld $0x17,%xmm0,%xmm0
    vpblendw $0xc,%xmm1,%xmm0,%xmm0
    vpand LCPI14_1(%rip),%xmm0,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 137 (DqCplEnv, straight) -/
def L6940_1 : Program := parse("
    vpaddd LCPI14_2(%rip),%xmm0,%xmm0
    vcvtps2pd %xmm0,%xmm1
    vmovapd %xmm1,%xmm0
    cmp $0xf4,%cl
    jb ff_aac_sbr_apply.L69a4
    vmovsd LCPI14_3(%rip),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 144 (DqCplEnv, straight) -/
def L69a4 : Program := parse("
    and $0x1,%ecx
    lea exp2_tab(%rip),%rsi
    vmulsd (%rsi,%rcx,8),%xmm0,%xmm0
    vcvtsd2ss %xmm0,%xmm0,%xmm0
    and $0x1,%edx
    vshufpd $0x1,%xmm1,%xmm1,%xmm1
    vmulsd (%rsi,%rdx,8),%xmm1,%xmm1
    vcvtsd2ss %xmm1,%xmm1,%xmm4
    jmp ff_aac_sbr_apply.L6a30
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 155 (DqCplEnv, straight) -/
def L69d0 : Program := parse("
    shl $0x17,%ecx
    add $0x43000000,%ecx
    vmovd %ecx,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 159 (DqCplEnv, straight) -/
def L69dd : Program := parse("
    movzbl (%r12,%r14,1),%edx
    mov %r15d,%ecx
    sub %edx,%ecx
    lea 0x7e(%rcx),%edx
    cmp $0xfe,%edx
    ja ff_aac_sbr_apply.L6a10
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm4
    jmp ff_aac_sbr_apply.L6a30
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 171 (DqCplEnv, straight) -/
def L6a10 : Program := parse("
    vpxor %xmm4,%xmm4,%xmm4
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6a30
    add $0x95,%cl
    mov $0x1,%edx
    shl %cl,%edx
    vmovd %edx,%xmm4
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 180 (DqCplEnv, straight) -/
def L6a30 : Program := parse("
    vcvtss2sd %xmm0,%xmm0,%xmm1
    vucomisd %xmm2,%xmm1
    jbe ff_aac_sbr_apply.L68d0
    xor %edi,%edi
    mov $0x10,%esi
    lea L_str_33(%rip),%rdx
    xor %eax,%eax
    vmovd %xmm4,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 188 (DqCplEnv, call_avlog) -/
def L6a30_1 : Program := parse("
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 189 (DqCplEnv, straight) -/
def L6a30_2 : Program := parse("
    vmovd -0x30(%rbp),%xmm4
    vmovss LCPI14_5(%rip),%xmm3
    vmovsd LCPI14_4(%rip),%xmm2
    mov -0x38(%rbp),%r9
    movzbl 0x289ac(%r9,%rbx,1),%eax
    vmovaps %xmm3,%xmm0
    jmp ff_aac_sbr_apply.L68d0
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 198 (DqCplEnv, straight+ud1) -/
def L6a90 : Program := parse("
    mov 0x289a8(%r9),%eax
    cmp %rax,%rbx
    mov $0x0,%r14d
    jae ff_aac_sbr_apply.L6abf
    inc %rbx
    add $0x30,%r12
    add $0xc0,%r13
    cmp $0x9,%rbx
    jne ff_aac_sbr_apply.L68b0
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 209 (DqCplNoise, straight) -/
def L6abf : Program := parse("
    mov 0x289b8(%r9),%eax
    test %eax,%eax
    je ff_aac_sbr_apply.L74de
    mov 0x74b08(%r9),%r8d
    test %r8d,%r8d
    je ff_aac_sbr_apply.L74de
    inc %eax
    mov $0x1,%edx
    mov $0x1,%ecx
    xor %esi,%esi
    vmovsd LCPI14_4(%rip),%xmm0
    vmovss LCPI14_5(%rip),%xmm1
    jmp ff_aac_sbr_apply.L6b12
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 224 (DqCplNoise, straight) -/
def L6b00 : Program := parse("
    xor %ecx,%ecx
")

set_option maxRecDepth 20000 in
/-- asm line 226 (DqCplNoise, straight) -/
def L6b02 : Program := parse("
    inc %rdx
    add $0x5,%rsi
    cmp %rdx,%rax
    je ff_aac_sbr_apply.L74de
")

set_option maxRecDepth 20000 in
/-- asm line 231 (DqCplNoise, straight) -/
def L6b12 : Program := parse("
    test %ecx,%ecx
    je ff_aac_sbr_apply.L6b00
    cmp $0x2,%rdx
    ja ff_aac_sbr_apply.L9c04
    movzbl 0x3e3f5(%r9,%rsi,1),%edi
    mov $0x7,%ecx
    sub %edi,%ecx
    cmp $0x86,%edi
    jae ff_aac_sbr_apply.L6b50
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm2
    jmp ff_aac_sbr_apply.L6b6c
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 246 (DqCplNoise, straight) -/
def L6b50 : Program := parse("
    vxorpd %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6b6c
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 255 (DqCplNoise, straight) -/
def L6b6c : Program := parse("
    movzbl 0x53eb5(%r9,%rsi,1),%edi
    mov $0xc,%ecx
    sub %edi,%ecx
    cmp $0x8a,%edi
    ja ff_aac_sbr_apply.L6ba0
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6bbc
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 266 (DqCplNoise, straight) -/
def L6ba0 : Program := parse("
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6bbc
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 275 (DqCplNoise, straight) -/
def L6bbc : Program := parse("
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e414(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 282 (DqCplNoise, straight) -/
def L6bbc_1 : Program := parse("
    vmovss %xmm2,0x53ed4(%r9,%rsi,4)
    mov %r8d,%ecx
    cmp $0x2,%r8d
    jb ff_aac_sbr_apply.L6b02
    movzbl 0x3e3f6(%r9,%rsi,1),%edi
    mov $0x7,%ecx
    sub %edi,%ecx
    cmp $0x86,%edi
    jae ff_aac_sbr_apply.L6c1e
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm2
    jmp ff_aac_sbr_apply.L6c3a
")

set_option maxRecDepth 20000 in
/-- asm line 296 (DqCplNoise, straight) -/
def L6c1e : Program := parse("
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6c3a
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 305 (DqCplNoise, straight) -/
def L6c3a : Program := parse("
    movzbl 0x53eb6(%r9,%rsi,1),%edi
    mov $0xc,%ecx
    sub %edi,%ecx
    cmp $0x8b,%edi
    jae ff_aac_sbr_apply.L6c61
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6c7d
")

set_option maxRecDepth 20000 in
/-- asm line 315 (DqCplNoise, straight) -/
def L6c61 : Program := parse("
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6c7d
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 324 (DqCplNoise, straight) -/
def L6c7d : Program := parse("
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e418(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 331 (DqCplNoise, straight) -/
def L6c7d_1 : Program := parse("
    vmovss %xmm2,0x53ed8(%r9,%rsi,4)
")

set_option maxRecDepth 20000 in
/-- asm line 332 (DqCplNoise, straight) -/
def L6c7d_2 : Program := parse("
    mov 0x74b08(%r9),%edi
    cmp $0x3,%edi
    jb ff_aac_sbr_apply.L6ce0
    movzbl 0x3e3f7(%r9,%rsi,1),%r8d
    mov $0x7,%ecx
    sub %r8d,%ecx
    cmp $0x86,%r8d
    jae ff_aac_sbr_apply.L6cea
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm2
    jmp ff_aac_sbr_apply.L6d09
")

set_option maxRecDepth 20000 in
/-- asm line 345 (DqCplNoise, straight) -/
def L6ce0 : Program := parse("
    mov %edi,%r8d
    mov %edi,%ecx
    jmp ff_aac_sbr_apply.L6b02
")

set_option maxRecDepth 20000 in
/-- asm line 349 (DqCplNoise, straight) -/
def L6cea : Program := parse("
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6d09
    mov $0x9c,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 358 (DqCplNoise, straight) -/
def L6d09 : Program := parse("
    movzbl 0x53eb7(%r9,%rsi,1),%r8d
    mov $0xc,%ecx
    sub %r8d,%ecx
    cmp $0x8b,%r8d
    jae ff_aac_sbr_apply.L6d32
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6d51
")

set_option maxRecDepth 20000 in
/-- asm line 368 (DqCplNoise, straight) -/
def L6d32 : Program := parse("
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6d51
    mov $0xa1,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 377 (DqCplNoise, straight) -/
def L6d51 : Program := parse("
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e41c(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 384 (DqCplNoise, straight) -/
def L6d51_1 : Program := parse("
    vmovss %xmm2,0x53edc(%r9,%rsi,4)
    mov $0x3,%r8d
    mov $0x3,%ecx
    cmp $0x3,%edi
    je ff_aac_sbr_apply.L6b02
    movzbl 0x3e3f8(%r9,%rsi,1),%r8d
    mov $0x7,%ecx
    sub %r8d,%ecx
    cmp $0x86,%r8d
    jae ff_aac_sbr_apply.L6dbc
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm2
    jmp ff_aac_sbr_apply.L6ddb
")

set_option maxRecDepth 20000 in
/-- asm line 399 (DqCplNoise, straight) -/
def L6dbc : Program := parse("
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6ddb
    mov $0x9c,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 408 (DqCplNoise, straight) -/
def L6ddb : Program := parse("
    movzbl 0x53eb8(%r9,%rsi,1),%r8d
    mov $0xc,%ecx
    sub %r8d,%ecx
    cmp $0x8b,%r8d
    jae ff_aac_sbr_apply.L6e04
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6e23
")

set_option maxRecDepth 20000 in
/-- asm line 418 (DqCplNoise, straight) -/
def L6e04 : Program := parse("
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6e23
    mov $0xa1,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 427 (DqCplNoise, straight) -/
def L6e23 : Program := parse("
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e420(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 434 (DqCplNoise, straight) -/
def L6e23_1 : Program := parse("
    vmovss %xmm2,0x53ee0(%r9,%rsi,4)
    mov $0x4,%r8d
    mov $0x4,%ecx
    cmp $0x5,%edi
    jb ff_aac_sbr_apply.L6b02
    movzbl 0x3e3f9(%r9,%rsi,1),%edi
    mov $0x7,%ecx
    sub %edi,%ecx
    cmp $0x86,%edi
    jae ff_aac_sbr_apply.L6e8c
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm2
    jmp ff_aac_sbr_apply.L6ea8
")

set_option maxRecDepth 20000 in
/-- asm line 449 (DqCplNoise, straight) -/
def L6e8c : Program := parse("
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6ea8
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 458 (DqCplNoise, straight) -/
def L6ea8 : Program := parse("
    movzbl 0x53eb9(%r9,%rsi,1),%edi
    mov $0xc,%ecx
    sub %edi,%ecx
    cmp $0x8b,%edi
    jae ff_aac_sbr_apply.L6ecf
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6eeb
")

set_option maxRecDepth 20000 in
/-- asm line 468 (DqCplNoise, straight) -/
def L6ecf : Program := parse("
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6eeb
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 477 (DqCplNoise, straight) -/
def L6eeb : Program := parse("
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e424(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 484 (DqCplNoise, straight) -/
def L6eeb_1 : Program := parse("
    vmovss %xmm2,0x53ee4(%r9,%rsi,4)
")

set_option maxRecDepth 20000 in
/-- asm line 485 (DqCplNoise, straight+ud1) -/
def L6eeb_2 : Program := parse("
    mov 0x74b08(%r9),%r8d
    mov %r8d,%ecx
    cmp $0x5,%r8d
    jbe ff_aac_sbr_apply.L6b02
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 491 (Entry, call_avlog) -/
def L6f32 : Program := parse("
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    lea L_str_2(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 497 (Entry, store_run) -/
def L6f32_1 : Program := parse("
    mov -0x38(%rbp),%r9
    movq $0x0,0x28924(%r9)
    movl $0x0,0x28930(%r9)
    movl $0x20,0x28978(%r9)
    movl $0x0,0x28980(%r9)
    movl $0xffffffff,0x41d68(%r9)
    movl $0xffffffff,0x2c2a8(%r9)
    movl $0xffffffff,0x2893c(%r9)
    movw $0xffff,0x28940(%r9)
")

set_option maxRecDepth 20000 in
/-- asm line 506 (Entry, straight) -/
def L6f32_2 : Program := parse("
    cmpl $0x0,0x28984(%r9)
    jne ff_aac_sbr_apply.L6825
    jmp ff_aac_sbr_apply.L676e
")

set_option maxRecDepth 20000 in
/-- asm line 510 (DqSce, straight) -/
def L6fbe : Program := parse("
    mov $0x2,%eax
    mov %rax,-0xc8(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 513 (DqSce, straight) -/
def L6fca : Program := parse("
    lea 0x289a0(%r9),%rax
    mov %rax,-0x58(%rbp)
    lea 0x3dbb0(%r9),%rax
    mov %rax,-0x50(%rbp)
    lea 0x3ddf0(%r9),%rax
    mov %rax,-0x48(%rbp)
    vmovsd LCPI14_4(%rip),%xmm1
    xor %eax,%eax
    jmp ff_aac_sbr_apply.L7044
")

set_option maxRecDepth 20000 in
/-- asm line 523 (Trap, trap) -/
def L6ff7 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 525 (DqSce, straight) -/
def L6ffc : Program := parse("
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%esi
")

set_option maxRecDepth 20000 in
/-- asm line 529 (DqSce, straight) -/
def L7007 : Program := parse("
    mov %esi,0x15a98(%r13)
")

set_option maxRecDepth 20000 in
/-- asm line 531 (DqSce, straight) -/
def L700e : Program := parse("
    cmp $0x3,%rax
    jne ff_aac_sbr_apply.L9c13
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 535 (DqSce, straight) -/
def L7020 : Program := parse("
    mov -0x30(%rbp),%rax
    inc %rax
    addq $0x15ac0,-0x50(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 538 (DqSce, straight) -/
def L7020_1 : Program := parse("
    addq $0x15ac0,-0x48(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 539 (DqSce, straight) -/
def L7020_2 : Program := parse("
    cmp -0xc8(%rbp),%rax
    je ff_aac_sbr_apply.L74de
")

set_option maxRecDepth 20000 in
/-- asm line 542 (DqSce, straight) -/
def L7044 : Program := parse("
    mov %rax,-0x30(%rbp)
    imul $0x15ac0,%rax,%rax
")

set_option maxRecDepth 20000 in
/-- asm line 544 (DqSce, straight) -/
def L7044_1 : Program := parse("
    mov -0x58(%rbp),%rcx
    lea (%rcx,%rax,1),%r13
    cmpl $0x0,0x8(%rcx,%rax,1)
    je ff_aac_sbr_apply.L71e0
    mov $0x1,%r15d
    mov -0x48(%rbp),%r12
    mov -0x50(%rbp),%r14
")

set_option maxRecDepth 20000 in
/-- asm line 552 (DqSce, straight) -/
def L7070 : Program := parse("
    movzbl 0xc(%r13,%r15,1),%eax
    cmp $0x1,%al
    ja ff_aac_sbr_apply.L99ee
    xor %ebx,%ebx
    jmp ff_aac_sbr_apply.L70ca
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 559 (DqSce, call_avlog) -/
def L7090 : Program := parse("
    xor %edi,%edi
    mov $0x10,%esi
    lea L_str_33(%rip),%rdx
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 564 (DqSce, straight) -/
def L7090_1 : Program := parse("
    vmovsd LCPI14_4(%rip),%xmm1
    mov -0x38(%rbp),%r9
    movl $0x3f800000,(%r12,%rbx,4)
")

set_option maxRecDepth 20000 in
/-- asm line 567 (DqSce, straight) -/
def L7090_2 : Program := parse("
    movzbl 0xc(%r13,%r15,1),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 569 (DqSce, straight) -/
def L70bf : Program := parse("
    inc %rbx
    cmp $0x2,%al
    jae ff_aac_sbr_apply.L99ee
")

set_option maxRecDepth 20000 in
/-- asm line 573 (DqSce, straight) -/
def L70ca : Program := parse("
    movzbl %al,%ecx
    mov 0x74b00(%r9,%rcx,4),%ecx
    cmp %rcx,%rbx
    jae ff_aac_sbr_apply.L71b0
    cmpl $0x0,0x64(%r13)
    je ff_aac_sbr_apply.L7120
    cmp $0x30,%rbx
    jae ff_aac_sbr_apply.L9b3b
    movzbl (%r14,%rbx,1),%ecx
    cmp $0x7b,%ecx
    jb ff_aac_sbr_apply.L7140
    vmovss LCPI14_0(%rip),%xmm0
    vmovss %xmm0,(%r12,%rbx,4)
    vcvtss2sd %xmm0,%xmm0,%xmm0
    vucomisd %xmm1,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 588 (DqSce, straight) -/
def L70ca_1 : Program := parse("
    jbe ff_aac_sbr_apply.L70bf
    jmp ff_aac_sbr_apply.L7090
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 592 (DqSce, straight) -/
def L7120 : Program := parse("
    cmp $0x30,%rbx
    jae ff_aac_sbr_apply.L9b45
    movzbl (%r14,%rbx,1),%ecx
    cmp $0xf6,%cl
    jb ff_aac_sbr_apply.L7166
    vmovsd LCPI14_3(%rip),%xmm0
    jmp ff_aac_sbr_apply.L717f
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 601 (DqSce, straight) -/
def L7140 : Program := parse("
    shl $0x17,%ecx
    add $0x42800000,%ecx
    vmovd %ecx,%xmm0
    vmovd %xmm0,(%r12,%rbx,4)
    vcvtss2sd %xmm0,%xmm0,%xmm0
    vucomisd %xmm1,%xmm0
    ja ff_aac_sbr_apply.L7090
    jmp ff_aac_sbr_apply.L70bf
")

set_option maxRecDepth 20000 in
/-- asm line 610 (DqSce, straight) -/
def L7166 : Program := parse("
    mov %ecx,%edx
    shl $0x16,%edx
    and $0x3f800000,%edx
    add $0x42800000,%edx
    vmovd %edx,%xmm0
    vcvtss2sd %xmm0,%xmm0,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 617 (DqSce, straight) -/
def L717f : Program := parse("
    and $0x1,%ecx
    lea exp2_tab(%rip),%rdx
    vmulsd (%rdx,%rcx,8),%xmm0,%xmm0
    vcvtsd2ss %xmm0,%xmm0,%xmm0
    vmovss %xmm0,(%r12,%rbx,4)
    vcvtss2sd %xmm0,%xmm0,%xmm0
    vucomisd %xmm1,%xmm0
    jbe ff_aac_sbr_apply.L70bf
    jmp ff_aac_sbr_apply.L7090
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 628 (DqSce, straight) -/
def L71b0 : Program := parse("
    mov 0x8(%r13),%eax
    cmp %rax,%r15
    jae ff_aac_sbr_apply.L71e0
    inc %r15
    add $0x30,%r14
    add $0xc0,%r12
    cmp $0x9,%r15
    jne ff_aac_sbr_apply.L7070
    jmp ff_aac_sbr_apply.L99f3
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 639 (DqSce, straight) -/
def L71e0 : Program := parse("
    mov 0x18(%r13),%eax
    test %rax,%rax
    mov $0x0,%r14d
    je ff_aac_sbr_apply.L7020
    mov 0x74b08(%r9),%edx
    test %edx,%edx
    je ff_aac_sbr_apply.L7020
    movzbl 0x15a55(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7226
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 654 (DqSce, straight) -/
def L71e0_1 : Program := parse("
    jmp ff_aac_sbr_apply.L723c
")

set_option maxRecDepth 20000 in
/-- asm line 656 (DqSce, straight) -/
def L7226 : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L723c
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 664 (DqSce, straight) -/
def L723c : Program := parse("
    mov %edi,0x15a74(%r13)
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L7370
")

set_option maxRecDepth 20000 in
/-- asm line 667 (DqSce, straight) -/
def L723c_1 : Program := parse("
    movzbl 0x15a56(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7270
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7286
")

set_option maxRecDepth 20000 in
/-- asm line 677 (DqSce, straight) -/
def L7270 : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7286
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 685 (DqSce, straight) -/
def L7286 : Program := parse("
    mov %edi,0x15a78(%r13)
    cmp $0x3,%edx
    jb ff_aac_sbr_apply.L7370
")

set_option maxRecDepth 20000 in
/-- asm line 688 (DqSce, straight) -/
def L7286_1 : Program := parse("
    movzbl 0x15a57(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L72ba
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L72d0
")

set_option maxRecDepth 20000 in
/-- asm line 698 (DqSce, straight) -/
def L72ba : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L72d0
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 706 (DqSce, straight) -/
def L72d0 : Program := parse("
    mov %edi,0x15a7c(%r13)
    cmp $0x3,%edx
    je ff_aac_sbr_apply.L7370
")

set_option maxRecDepth 20000 in
/-- asm line 709 (DqSce, straight) -/
def L72d0_1 : Program := parse("
    movzbl 0x15a58(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7304
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L731a
")

set_option maxRecDepth 20000 in
/-- asm line 719 (DqSce, straight) -/
def L7304 : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L731a
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 727 (DqSce, straight) -/
def L731a : Program := parse("
    mov %edi,0x15a80(%r13)
    cmp $0x5,%edx
    jb ff_aac_sbr_apply.L7370
")

set_option maxRecDepth 20000 in
/-- asm line 730 (DqSce, straight) -/
def L731a_1 : Program := parse("
    movzbl 0x15a59(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L734a
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7360
")

set_option maxRecDepth 20000 in
/-- asm line 740 (DqSce, straight) -/
def L734a : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7360
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 748 (DqSce, straight) -/
def L7360 : Program := parse("
    mov %edi,0x15a84(%r13)
    cmp $0x5,%edx
    jne ff_aac_sbr_apply.L9c22
")

set_option maxRecDepth 20000 in
/-- asm line 752 (DqSce, straight) -/
def L7370 : Program := parse("
    inc %rax
    cmp $0x2,%rax
    je ff_aac_sbr_apply.L7020
    movzbl 0x15a5a(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L73a1
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L73b7
")

set_option maxRecDepth 20000 in
/-- asm line 765 (DqSce, straight) -/
def L73a1 : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L73b7
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 773 (DqSce, straight) -/
def L73b7 : Program := parse("
    mov %edi,0x15a88(%r13)
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L700e
")

set_option maxRecDepth 20000 in
/-- asm line 776 (DqSce, straight) -/
def L73b7_1 : Program := parse("
    movzbl 0x15a5b(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L73eb
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7401
")

set_option maxRecDepth 20000 in
/-- asm line 786 (DqSce, straight) -/
def L73eb : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7401
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 794 (DqSce, straight) -/
def L7401 : Program := parse("
    mov %edi,0x15a8c(%r13)
    cmp $0x3,%edx
    jb ff_aac_sbr_apply.L700e
")

set_option maxRecDepth 20000 in
/-- asm line 797 (DqSce, straight) -/
def L7401_1 : Program := parse("
    movzbl 0x15a5c(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7435
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L744b
")

set_option maxRecDepth 20000 in
/-- asm line 807 (DqSce, straight) -/
def L7435 : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L744b
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 815 (DqSce, straight) -/
def L744b : Program := parse("
    mov %edi,0x15a90(%r13)
    cmp $0x3,%edx
    je ff_aac_sbr_apply.L700e
")

set_option maxRecDepth 20000 in
/-- asm line 818 (DqSce, straight) -/
def L744b_1 : Program := parse("
    movzbl 0x15a5d(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L747f
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7495
")

set_option maxRecDepth 20000 in
/-- asm line 828 (DqSce, straight) -/
def L747f : Program := parse("
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7495
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
")

set_option maxRecDepth 20000 in
/-- asm line 836 (DqSce, straight) -/
def L7495 : Program := parse("
    mov %edi,0x15a94(%r13)
    cmp $0x5,%edx
    jb ff_aac_sbr_apply.L700e
")

set_option maxRecDepth 20000 in
/-- asm line 839 (DqSce, straight) -/
def L7495_1 : Program := parse("
    movzbl 0x15a5e(%r13),%edx
    mov $0x6,%ecx
    sub %edx,%ecx
    cmp $0x85,%edx
    jb ff_aac_sbr_apply.L6ffc
    xor %esi,%esi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7007
    mov $0x9b,%cl
    sub %dl,%cl
    mov $0x1,%esi
    shl %cl,%esi
    jmp ff_aac_sbr_apply.L7007
")

set_option maxRecDepth 20000 in
/-- asm line 853 (Setup, straight) -/
def L74de : Program := parse("
    movl $0x0,0x28928(%r9)
")

set_option maxRecDepth 20000 in
/-- asm line 855 (Setup, straight) -/
def L74e9 : Program := parse("
    lea _GLOBAL_OFFSET_TABLE_(%rip),%rax
    lea 0x28920(%r9),%rcx
    mov %rcx,-0xb0(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 858 (Setup, store_run) -/
def L74e9_1 : Program := parse("
    movzbl -0xf0(%rbp),%ecx
    mov %cl,%r14b
    mov %r14,-0x150(%rbp)
    lea 0x88b00(%r9),%rcx
    mov %rcx,-0x120(%rbp)
    lea 0x289a0(%r9),%rcx
    mov %rcx,-0x138(%rbp)
    lea 0x885e0(%r9),%r12
    lea 0x886e0(%r9),%r13
    lea 0x74c60(%r9),%rcx
    mov %rcx,-0xc0(%rbp)
    lea 0x85c60(%r9),%rcx
    mov %rcx,-0x148(%rbp)
    lea 0x85e60(%r9),%rcx
    mov %rcx,-0x140(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 873 (Setup, store_run) -/
def L74e9_2 : Program := parse("
    lea 0x77460(%r9),%rcx
    mov %rcx,-0xb8(%rbp)
    lea 0x74ba4(%r9),%rcx
    mov %rcx,-0x1b8(%rbp)
    lea 0x74b72(%r9),%rcx
    mov %rcx,-0x1b0(%rbp)
    movabs $sbr_qmf_window_ds-_GLOBAL_OFFSET_TABLE_,%r15
    add %rax,%r15
    lea 0x86060(%r9),%rax
    mov %rax,-0xd0(%rbp)
    lea 0x86660(%r9),%rax
    mov %rax,-0x188(%rbp)
    lea 0x86c60(%r9),%rax
    mov %rax,-0x1a8(%rbp)
    lea 0x2893c(%r9),%rax
")

set_option maxRecDepth 20000 in
/-- asm line 888 (Setup, store_run) -/
def L74e9_3 : Program := parse("
    mov %rax,-0x168(%rbp)
    lea 0x86de0(%r9),%rax
    mov %rax,-0x178(%rbp)
    lea 0x873e0(%r9),%rax
    mov %rax,-0x108(%rbp)
    lea 0x879e0(%r9),%rax
    mov %rax,-0x170(%rbp)
    lea 0x87fe0(%r9),%rax
    mov %rax,-0x100(%rbp)
    lea 0x7c460(%r9),%rax
    mov %rax,-0xa8(%rbp)
    lea 0x74ba8(%r9),%rax
    mov %rax,-0x198(%rbp)
    lea 0x289d2(%r9),%rax
    mov %rax,-0x180(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 903 (Setup, store_run) -/
def L74e9_4 : Program := parse("
    lea 0x775b0(%r9),%rax
    mov %rax,-0x70(%rbp)
    lea 0x77470(%r9),%rax
    mov %rax,-0x190(%rbp)
    lea 0x3da00(%r9),%rax
    mov %rax,-0x160(%rbp)
    lea 0x87fe4(%r9),%rax
    mov %rax,-0x158(%rbp)
    mov $0x1,%cl
    xor %edx,%edx
    mov %r13,-0xc8(%rbp)
    mov %r15,-0xf0(%rbp)
    mov %r12,-0x118(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 917 (Ana, straight) -/
def L7682 : Program := parse("
    mov -0x90(%rbp),%rax
    mov 0x2550(%rax),%rax
    mov %rax,-0x30(%rbp)
    mov %r12,%r14
")

set_option maxRecDepth 20000 in
/-- asm line 921 (Ana, straight) -/
def L7682_1 : Program := parse("
    mov 0x88ae0(%r9),%rax
    mov %rax,-0x58(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 923 (Ana, straight) -/
def L7682_2 : Program := parse("
    mov 0x88ae8(%r9),%rax
    mov %rax,-0x50(%rbp)
    mov %ecx,-0xf8(%rbp)
    test $0x1,%cl
")

set_option maxRecDepth 20000 in
/-- asm line 927 (Ana, straight) -/
def L7682_3 : Program := parse("
    mov -0x128(%rbp),%rax
    cmovne -0x130(%rbp),%rax
    mov %rax,-0x68(%rbp)
    mov %rdx,-0x1a0(%rbp)
    imul $0x15ac0,%rdx,%r13
")

set_option maxRecDepth 20000 in
/-- asm line 932 (Ana, straight) -/
def L7682_4 : Program := parse("
    mov -0x138(%rbp),%rcx
    lea (%rcx,%r13,1),%rax
    mov %rax,-0x48(%rbp)
    lea (%rcx,%r13,1),%rdi
    add $0x2480,%rdi
    lea 0x3920(%rcx,%r13,1),%rax
    mov %rax,-0x78(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 939 (Ana, call_mem) -/
def L7682_5 : Program := parse("
    movslq 0x7920(%rcx,%r13,1),%r15
    lea 0x3480(%rcx,%r13,1),%rsi
    mov $0x480,%edx
    mov %rdi,%r12
    mov %r9,%rbx
    call memcpy
")

set_option maxRecDepth 20000 in
/-- asm line 945 (Ana, straight) -/
def L7682_6 : Program := parse("
    mov %r13,-0x98(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 946 (Ana, call_mem) -/
def L7682_7 : Program := parse("
    mov -0x138(%rbp),%rax
    lea (%rax,%r13,1),%rdi
    add $0x2900,%rdi
    mov $0x1000,%edx
    mov -0x68(%rbp),%rsi
    call memcpy
")

set_option maxRecDepth 20000 in
/-- asm line 952 (Ana, straight) -/
def L7682_8 : Program := parse("
    shl $0xd,%r15
    add -0x78(%rbp),%r15
    xor %r13d,%r13d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 957 (Ana, call_ind) -/
def L7750 : Program := parse("
    lea (%r12,%r13,1),%rdx
    mov %r14,%rdi
    mov -0xf0(%rbp),%rsi
    mov $0x140,%ecx
    mov -0x30(%rbp),%rax
    call *0x38(%rax)
")

set_option maxRecDepth 20000 in
/-- asm line 963 (Ana, call_ind) -/
def L7750_1 : Program := parse("
    mov %r14,%rdi
    call *0x88b00(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 965 (Ana, call_ind) -/
def L7750_2 : Program := parse("
    mov %r14,%rdi
    call *0x88b18(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 967 (Ana, call_ind) -/
def L7750_3 : Program := parse("
    mov $0x4,%ecx
    mov -0x58(%rbp),%rdi
    mov %r14,%rsi
    mov -0xc8(%rbp),%rdx
    call *-0x50(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 972 (Ana, call_ind) -/
def L7750_4 : Program := parse("
    mov %r15,%rdi
    mov %r14,%rsi
    call *0x88b20(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 975 (Ana, call_ind) -/
def L7750_5 : Program := parse("
    sub $0xffffffffffffff80,%r13
    add $0x100,%r15
    cmp $0x1000,%r13
    jne ff_aac_sbr_apply.L7750
    mov -0x48(%rbp),%r15
    mov 0x7920(%r15),%ecx
    mov -0xb0(%rbp),%rdi
    mov -0xc0(%rbp),%rsi
    mov -0x78(%rbp),%rdx
    call *0x88b70(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 985 (Ana, straight) -/
def L7750_6 : Program := parse("
    mov 0x7920(%r15),%eax
    xor $0x1,%eax
    mov %eax,0x7920(%r15)
")

set_option maxRecDepth 20000 in
/-- asm line 988 (Ana, call_ind) -/
def L7750_7 : Program := parse("
    cmpl $0x0,0x28924(%rbx)
    mov %r14,%r12
    mov -0x120(%rbp),%rdi
    je ff_aac_sbr_apply.L9934
    mov 0x28960(%rbx),%r8d
    mov -0x148(%rbp),%rsi
    mov -0x140(%rbp),%rdx
    mov -0xc0(%rbp),%rcx
    mov -0x38(%rbp),%rax
    call *0x88b88(%rax)
")

set_option maxRecDepth 20000 in
/-- asm line 998 (Ana, straight) -/
def L7750_8 : Program := parse("
    mov -0x38(%rbp),%r8
    mov 0x74b08(%r8),%eax
    test %eax,%eax
    mov -0x48(%rbp),%rbx
    je ff_aac_sbr_apply.L7b00
    movzbl 0x27(%rbx),%ecx
    movzbl 0x2c(%rbx),%edx
    add %ecx,%edx
    vmovss LCPI14_6(%rip),%xmm0
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L7866
    cmp $0x4,%cl
    jae ff_aac_sbr_apply.L9c09
    lea bw_tab(%rip),%rdx
    vmovss (%rdx,%rcx,4),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 1014 (Chirp, straight) -/
def L7866 : Program := parse("
    vmovss 0x390c(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7884
    vmovss LCPI14_10(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 1020 (Chirp, vector) -/
def L7884 : Program := parse("
    vcmpltss %xmm1,%xmm0,%xmm3
    vbroadcastss LCPI14_17(%rip),%xmm4
    vblendvps %xmm3,LCPI14_8(%rip),%xmm4,%xmm3
    vmulss %xmm3,%xmm0,%xmm0
    vmulss %xmm2,%xmm1,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vcmpltss LCPI14_11(%rip),%xmm0,%xmm1
    vandnps %xmm0,%xmm1,%xmm0
    vmovss %xmm0,0x390c(%rbx)
    cmp $0x1,%eax
    je ff_aac_sbr_apply.L7b00
")

set_option maxRecDepth 20000 in
/-- asm line 1031 (Chirp, straight) -/
def L7884_1 : Program := parse("
    movzbl 0x28(%rbx),%ecx
    movzbl 0x2d(%rbx),%edx
    add %ecx,%edx
    vmovss LCPI14_6(%rip),%xmm0
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L78f2
    cmp $0x3,%cl
    ja ff_aac_sbr_apply.L9c09
    lea bw_tab(%rip),%rdx
    vmovss (%rdx,%rcx,4),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 1042 (Chirp, straight) -/
def L78f2 : Program := parse("
    vmovss 0x3910(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7910
    vmovss LCPI14_10(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 1048 (Chirp, vector) -/
def L7910 : Program := parse("
    vcmpltss %xmm1,%xmm0,%xmm3
    vbroadcastss LCPI14_17(%rip),%xmm4
    vblendvps %xmm3,LCPI14_8(%rip),%xmm4,%xmm3
    vmulss %xmm3,%xmm0,%xmm0
    vmulss %xmm2,%xmm1,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vcmpltss LCPI14_11(%rip),%xmm0,%xmm1
    vandnps %xmm0,%xmm1,%xmm0
    vmovss %xmm0,0x3910(%rbx)
    cmp $0x3,%eax
    jb ff_aac_sbr_apply.L7b00
")

set_option maxRecDepth 20000 in
/-- asm line 1059 (Chirp, straight) -/
def L7910_1 : Program := parse("
    movzbl 0x29(%rbx),%ecx
    movzbl 0x2e(%rbx),%edx
    add %ecx,%edx
    vmovss LCPI14_6(%rip),%xmm0
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L797e
    cmp $0x3,%cl
    ja ff_aac_sbr_apply.L9c09
    lea bw_tab(%rip),%rdx
    vmovss (%rdx,%rcx,4),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 1070 (Chirp, straight) -/
def L797e : Program := parse("
    vmovss 0x3914(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L799c
    vmovss LCPI14_10(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 1076 (Chirp, vector) -/
def L799c : Program := parse("
    vcmpltss %xmm1,%xmm0,%xmm3
    vbroadcastss LCPI14_17(%rip),%xmm4
    vblendvps %xmm3,LCPI14_8(%rip),%xmm4,%xmm3
    vmulss %xmm3,%xmm0,%xmm0
    vmulss %xmm2,%xmm1,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vcmpltss LCPI14_11(%rip),%xmm0,%xmm1
    vandnps %xmm0,%xmm1,%xmm0
    vmovss %xmm0,0x3914(%rbx)
    cmp $0x3,%eax
    je ff_aac_sbr_apply.L7b00
")

set_option maxRecDepth 20000 in
/-- asm line 1087 (Chirp, straight) -/
def L799c_1 : Program := parse("
    movzbl 0x2a(%rbx),%ecx
    movzbl 0x2f(%rbx),%edx
    add %ecx,%edx
    vmovss LCPI14_6(%rip),%xmm0
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L7a0a
    cmp $0x3,%cl
    ja ff_aac_sbr_apply.L9c09
    lea bw_tab(%rip),%rdx
    vmovss (%rdx,%rcx,4),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 1098 (Chirp, straight) -/
def L7a0a : Program := parse("
    vmovss 0x3918(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7a28
    vmovss LCPI14_10(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 1104 (Chirp, vector) -/
def L7a28 : Program := parse("
    vcmpltss %xmm1,%xmm0,%xmm3
    vbroadcastss LCPI14_17(%rip),%xmm4
    vblendvps %xmm3,LCPI14_8(%rip),%xmm4,%xmm3
    vmulss %xmm3,%xmm0,%xmm0
    vmulss %xmm2,%xmm1,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vcmpltss LCPI14_11(%rip),%xmm0,%xmm1
    vandnps %xmm0,%xmm1,%xmm0
    vmovss %xmm0,0x3918(%rbx)
    cmp $0x5,%eax
    jb ff_aac_sbr_apply.L7b00
")

set_option maxRecDepth 20000 in
/-- asm line 1115 (Chirp, straight) -/
def L7a28_1 : Program := parse("
    movzbl 0x2b(%rbx),%ecx
    movzbl 0x30(%rbx),%edx
    add %ecx,%edx
    vmovss LCPI14_6(%rip),%xmm0
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L7a96
    cmp $0x3,%cl
    ja ff_aac_sbr_apply.L9c09
    lea bw_tab(%rip),%rdx
    vmovss (%rdx,%rcx,4),%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 1126 (Chirp, straight) -/
def L7a96 : Program := parse("
    vmovss 0x391c(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7ab4
    vmovss LCPI14_10(%rip),%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 1132 (Chirp, vector) -/
def L7ab4 : Program := parse("
    vcmpltss %xmm1,%xmm0,%xmm3
    vbroadcastss LCPI14_17(%rip),%xmm4
    vblendvps %xmm3,LCPI14_8(%rip),%xmm4,%xmm3
    vmulss %xmm3,%xmm0,%xmm0
    vmulss %xmm2,%xmm1,%xmm1
    vaddss %xmm1,%xmm0,%xmm0
    vcmpltss LCPI14_11(%rip),%xmm0,%xmm1
    vandnps %xmm0,%xmm1,%xmm0
    vmovss %xmm0,0x391c(%rbx)
    cmp $0x5,%eax
    jne ff_aac_sbr_apply.L9c1d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1145 (HfGen, straight) -/
def L7b00 : Program := parse("
    movslq 0x8(%rbx),%rcx
    mov %rcx,-0x30(%rbp)
    test %rcx,%rcx
    je ff_aac_sbr_apply.L9bd4
")

set_option maxRecDepth 20000 in
/-- asm line 1149 (HfGen, straight) -/
def L7b00_1 : Program := parse("
    mov 0x28978(%r8),%r12d
    mov 0x74c50(%r8),%eax
    test %eax,%eax
    je ff_aac_sbr_apply.L7cb0
    xor %r13d,%r13d
    xor %r15d,%r15d
")

set_option maxRecDepth 20000 in
/-- asm line 1156 (HfGen, straight) -/
def L7b2d : Program := parse("
    cmpb $0x0,0x74c54(%r8,%r15,1)
    je ff_aac_sbr_apply.L7c5d
    movslq %r12d,%r12
    xor %r14d,%r14d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1162 (HfGen, straight) -/
def L7b50 : Program := parse("
    movzbl 0x74c5a(%r8,%r15,1),%eax
    mov 0x74b08(%r8),%ecx
    cmp %ecx,%r13d
    ja ff_aac_sbr_apply.L7bb3
    mov %r13d,%edx
    lea 0x1(%rcx),%r13d
    cmp $0x7,%rdx
    mov $0x6,%esi
    cmovae %rdx,%rsi
    inc %rcx
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1174 (HfGen, straight) -/
def L7b80 : Program := parse("
    cmp %rdx,%rsi
    je ff_aac_sbr_apply.L9b4a
    movzwl 0x74c06(%r8,%rdx,2),%edi
    cmp %rdi,%r12
    jl ff_aac_sbr_apply.L7bb0
    inc %rdx
    cmp %rdx,%rcx
    jne ff_aac_sbr_apply.L7b80
    jmp ff_aac_sbr_apply.L7bb3
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1185 (HfGen, straight) -/
def L7bb0 : Program := parse("
    mov %edx,%r13d
")

set_option maxRecDepth 20000 in
/-- asm line 1187 (HfGen, straight) -/
def L7bb3 : Program := parse("
    test %r13d,%r13d
    jle ff_aac_sbr_apply.L7c80
    add %r14d,%eax
    dec %r13d
    lea (%r12,%r12,4),%rcx
    shl $0x6,%rcx
    mov -0xb8(%rbp),%rdx
    lea (%rdx,%rcx,1),%rdi
    add $0x10,%rdi
    mov %eax,%eax
    lea (%rax,%rax,4),%rcx
    shl $0x6,%rcx
    mov -0xc0(%rbp),%rdx
    lea (%rdx,%rcx,1),%rsi
    add $0x10,%rsi
")

set_option maxRecDepth 20000 in
/-- asm line 1202 (HfGen, call_ind) -/
def L7bb3_1 : Program := parse("
    mov -0x148(%rbp),%rcx
    lea (%rcx,%rax,8),%rdx
    mov -0x140(%rbp),%rcx
    lea (%rcx,%rax,8),%rcx
    vmovss 0x390c(%rbx,%r13,4),%xmm0
    movzbl 0x15a9c(%rbx),%r8d
    add %r8d,%r8d
    mov -0x30(%rbp),%rax
    movzbl 0x15a9c(%rbx,%rax,1),%r9d
    add %r9d,%r9d
    mov -0x38(%rbp),%rbx
    call *0x88b40(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 1214 (HfGen, straight) -/
def L7bb3_2 : Program := parse("
    mov %rbx,%r8
    mov -0x48(%rbp),%rbx
    inc %r14d
    inc %r12
    movzbl 0x74c54(%r8,%r15,1),%eax
    cmp %eax,%r14d
    jb ff_aac_sbr_apply.L7b50
    mov 0x74c50(%r8),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 1223 (HfGen, straight) -/
def L7c5d : Program := parse("
    inc %r15
    mov %eax,%ecx
    cmp %rcx,%r15
    jae ff_aac_sbr_apply.L8b4f
    cmp $0x6,%r15
    jne ff_aac_sbr_apply.L7b2d
    jmp ff_aac_sbr_apply.L9a5f
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1232 (HfGen, call_avlog) -/
def L7c80 : Program := parse("
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    mov $0x10,%esi
    lea L_str_35(%rip),%rdx
    mov %r12d,%ecx
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 1239 (HfGen, straight) -/
def L7c80_1 : Program := parse("
    jmp ff_aac_sbr_apply.L7ce0
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1242 (HfGen, straight) -/
def L7cb0 : Program := parse("
    mov %r12d,%eax
    add 0x28980(%r8),%eax
    sub %r12d,%eax
    jbe ff_aac_sbr_apply.L7ce4
")

set_option maxRecDepth 20000 in
/-- asm line 1247 (HfGen, call_mem) -/
def L7cbf : Program := parse("
    movslq %r12d,%rcx
    lea (%rcx,%rcx,4),%rdi
    shl $0x6,%rdi
    add -0xb8(%rbp),%rdi
    shl $0x6,%rax
    lea (%rax,%rax,4),%rdx
    xor %esi,%esi
    call memset
")

set_option maxRecDepth 20000 in
/-- asm line 1256 (HfGen, straight) -/
def L7ce0 : Program := parse("
    mov -0x38(%rbp),%r8
")

set_option maxRecDepth 20000 in
/-- asm line 1258 (Map:A, store_run) -/
def L7ce4 : Program := parse("
    lea 0x15030(%rbx),%r10
    vxorps %xmm0,%xmm0,%xmm0
    vmovups %ymm0,0x15190(%rbx)
    vmovaps %ymm0,0x15180(%rbx)
    vmovaps %ymm0,0x15160(%rbx)
    vmovaps %ymm0,0x15140(%rbx)
    vmovaps %ymm0,0x15120(%rbx)
    vmovaps %ymm0,0x15100(%rbx)
    vmovaps %ymm0,0x150e0(%rbx)
    vmovaps %ymm0,0x150c0(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 1268 (Map:A, straight) -/
def L7ce4_1 : Program := parse("
    vmovaps %ymm0,0x150a0(%rbx)
    vmovaps %ymm0,0x15080(%rbx)
    vmovaps %ymm0,0x15060(%rbx)
")

set_option maxRecDepth 20000 in
/-- asm line 1271 (Map:A, straight) -/
def L7ce4_2 : Program := parse("
    cmpl $0x0,0x8(%rbx)
    vmovss LCPI14_5(%rip),%xmm9
    je ff_aac_sbr_apply.L8790
    lea 0x15390(%rbx),%rax
    mov %rax,-0xe0(%rbp)
    lea 0x15a60(%rbx),%rax
    mov %rax,-0xd8(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 1278 (Map:A, straight) -/
def L7ce4_3 : Program := parse("
    mov -0x180(%rbp),%rax
    mov -0x98(%rbp),%rcx
    lea (%rax,%rcx,1),%r11
    mov $0x1,%ecx
    mov %r8,-0x60(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 1283 (Map:A, straight) -/
def L7ce4_4 : Program := parse("
    mov -0x188(%rbp),%rax
    mov %rax,-0x58(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 1285 (Map:A, straight) -/
def L7ce4_5 : Program := parse("
    mov -0xd0(%rbp),%r12
    xor %eax,%eax
    mov %r10,-0x80(%rbp)
    mov %r11,-0xe8(%rbp)
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1291 (Map:A, straight) -/
def L7db0 : Program := parse("
    mov %rcx,%r14
    movzbl 0xc(%rbx,%rcx,1),%ecx
    cmp $0x2,%rcx
    jae ff_aac_sbr_apply.L9b77
    test %rcx,%rcx
    mov -0x1b8(%rbp),%r15
    cmove -0x1b0(%rbp),%r15
    mov 0x28978(%r8),%edx
    movzwl (%r15),%edi
    mov %edx,-0x30(%rbp)
    cmp %edi,%edx
    jne ff_aac_sbr_apply.L879e
")

set_option maxRecDepth 20000 in
/-- asm line 1303 (Map:A, straight) -/
def L7db0_1 : Program := parse("
    mov 0x74b00(%r8,%rcx,4),%ecx
    mov %rcx,-0x50(%rbp)
    test %rcx,%rcx
    je ff_aac_sbr_apply.L7e90
    lea (%r14,%r14,2),%rcx
    shl $0x6,%rcx
    add -0xe0(%rbp),%rcx
    xor %edx,%edx
    jmp ff_aac_sbr_apply.L7e29
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1314 (Map:A, straight) -/
def L7e20 : Program := parse("
    mov %r9d,%edi
    cmp -0x50(%rbp),%rdx
    je ff_aac_sbr_apply.L7e90
")

set_option maxRecDepth 20000 in
/-- asm line 1318 (Map:A, straight) -/
def L7e29 : Program := parse("
    mov %rdx,%rsi
    inc %rdx
    movzwl 0x2(%r15,%rsi,2),%r9d
    cmp %r9w,%di
    jae ff_aac_sbr_apply.L7e20
    cmp $0x2f,%rsi
    ja ff_aac_sbr_apply.L9b5e
    movzwl %di,%edi
    mov %edi,%r8d
    sub -0x30(%rbp),%r8d
    cmp $0x2f,%r8d
    ja ff_aac_sbr_apply.L99e9
    mov %r8d,%r8d
    inc %rdi
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1334 (Map:A, straight) -/
def L7e60 : Program := parse("
    vmovss (%rcx,%rsi,4),%xmm0
    vmovss %xmm0,(%r12,%r8,4)
")

set_option maxRecDepth 20000 in
/-- asm line 1336 (Map:A, straight) -/
def L7e60_1 : Program := parse("
    movzwl (%r15,%rdx,2),%r9d
    cmp %r9,%rdi
    jae ff_aac_sbr_apply.L7e20
    inc %r8
    inc %rdi
    cmp $0x30,%r8d
    jb ff_aac_sbr_apply.L7e60
    jmp ff_aac_sbr_apply.L99e9
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1346 (Map:A, straight) -/
def L7e90 : Program := parse("
    mov %r14,-0x68(%rbp)
    mov $0x1,%edx
")

set_option maxRecDepth 20000 in
/-- asm line 1348 (Map:A, straight) -/
def L7e90_1 : Program := parse("
    cmpl $0x2,0x18(%rbx)
    jb ff_aac_sbr_apply.L7eb6
    movzbl 0x15a9c(%rbx,%rax,1),%ecx
    cmp 0x15aa7(%rbx),%cl
    mov $0x2,%edx
    sbb $0x0,%rdx
")

set_option maxRecDepth 20000 in
/-- asm line 1355 (Map:A, straight) -/
def L7eb6 : Program := parse("
    mov -0x38(%rbp),%r8
    mov 0x74b08(%r8),%ecx
    test %ecx,%ecx
    je ff_aac_sbr_apply.L8520
    lea (%rdx,%rdx,4),%rdx
    mov -0xd8(%rbp),%rsi
    lea (%rsi,%rdx,4),%rdx
    movzwl 0x74c06(%r8),%edi
    movzwl 0x74c08(%r8),%esi
    cmp %si,%di
    jae ff_aac_sbr_apply.L8009
    mov %rsi,%r8
    sub %rdi,%r8
    mov %r8,%r9
    and $0x3,%r9
")

set_option maxRecDepth 20000 in
/-- asm line 1370 (Map:A, straight) -/
def L7eb6_1 : Program := parse("
    je ff_aac_sbr_apply.L7f36
    mov %edi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1377 (Map:A, straight) -/
def L7f10 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b40
    vmovss (%rdx),%xmm0
    mov -0x58(%rbp),%rbx
    vmovss %xmm0,(%rbx,%r10,4)
    dec %r11
    inc %r10
    cmp %r11,%r9
    jne ff_aac_sbr_apply.L7f10
    sub %r11,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 1388 (Map:A, straight) -/
def L7f36 : Program := parse("
    dec %r8
    cmp $0x3,%r8
    jb ff_aac_sbr_apply.L8009
    mov %edi,%r8d
    sub -0x30(%rbp),%r8d
    lea 0x3(%r8),%r9d
    mov -0x60(%rbp),%rbx
    lea (%rbx,%r9,4),%r9
    lea 0x2(%r8),%r10d
    lea (%rbx,%r10,4),%r10
    mov %r8d,%r11d
    inc %r11d
    lea (%rbx,%r11,4),%r11
    sub %rsi,%rdi
    lea (%rbx,%r8,4),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 1403 (Map:A, straight) -/
def L7f36_1 : Program := parse("
    mov $0x21998,%r14d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1406 (Map:A, straight) -/
def L7f80 : Program := parse("
    lea (%r8,%r14,1),%r13d
    add $0xfffde668,%r13d
    cmp $0x30,%r13d
    jae ff_aac_sbr_apply.L9b40
    vmovss (%rdx),%xmm0
    vmovss %xmm0,(%rbx,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde669,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r11,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66a,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
")

set_option maxRecDepth 20000 in
/-- asm line 1421 (Map:A, straight) -/
def L7f80_1 : Program := parse("
    vmovss %xmm0,(%r10,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66b,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r9,%r14,4)
    lea (%rdi,%r14,1),%r13
    add $0x4,%r13
    add $0x4,%r14
    cmp $0x21998,%r13
    jne ff_aac_sbr_apply.L7f80
")

set_option maxRecDepth 20000 in
/-- asm line 1433 (Map:B, straight) -/
def L8009 : Program := parse("
    cmp $0x1,%ecx
    mov -0x38(%rbp),%r8
    je ff_aac_sbr_apply.L8520
    movzwl 0x74c0a(%r8),%edi
    cmp %di,%si
    jae ff_aac_sbr_apply.L814a
    mov %rdi,%r8
    sub %rsi,%r8
    mov %r8,%r9
    and $0x3,%r9
    je ff_aac_sbr_apply.L8077
    mov %esi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1450 (Map:B, straight) -/
def L8050 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x4(%rdx),%xmm0
    mov -0x58(%rbp),%rbx
    vmovss %xmm0,(%rbx,%r10,4)
    dec %r11
    inc %r10
    cmp %r11,%r9
    jne ff_aac_sbr_apply.L8050
    sub %r11,%rsi
")

set_option maxRecDepth 20000 in
/-- asm line 1461 (Map:B, straight) -/
def L8077 : Program := parse("
    dec %r8
    cmp $0x3,%r8
    jb ff_aac_sbr_apply.L814a
    mov %esi,%r8d
    sub -0x30(%rbp),%r8d
    lea 0x3(%r8),%r9d
    mov -0x60(%rbp),%rbx
    lea (%rbx,%r9,4),%r9
    lea 0x2(%r8),%r10d
    lea (%rbx,%r10,4),%r10
    mov %r8d,%r11d
    inc %r11d
    lea (%rbx,%r11,4),%r11
    sub %rdi,%rsi
    lea (%rbx,%r8,4),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 1476 (Map:B, straight) -/
def L8077_1 : Program := parse("
    mov $0x21998,%r14d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1479 (Map:B, straight) -/
def L80c0 : Program := parse("
    lea (%r8,%r14,1),%r13d
    add $0xfffde668,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x4(%rdx),%xmm0
    vmovss %xmm0,(%rbx,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde669,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r11,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66a,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
")

set_option maxRecDepth 20000 in
/-- asm line 1494 (Map:B, straight) -/
def L80c0_1 : Program := parse("
    vmovss %xmm0,(%r10,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66b,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r9,%r14,4)
    lea (%rsi,%r14,1),%r13
    add $0x4,%r13
    add $0x4,%r14
    cmp $0x21998,%r13
    jne ff_aac_sbr_apply.L80c0
")

set_option maxRecDepth 20000 in
/-- asm line 1506 (Map:B, straight) -/
def L814a : Program := parse("
    cmp $0x2,%ecx
    mov -0x38(%rbp),%r8
    je ff_aac_sbr_apply.L8520
    movzwl 0x74c0c(%r8),%esi
    cmp %si,%di
    jae ff_aac_sbr_apply.L828a
    mov %rsi,%r8
    sub %rdi,%r8
    mov %r8,%r9
    and $0x3,%r9
    je ff_aac_sbr_apply.L81b7
    mov %edi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1523 (Map:B, straight) -/
def L8190 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x8(%rdx),%xmm0
    mov -0x58(%rbp),%rbx
    vmovss %xmm0,(%rbx,%r10,4)
    dec %r11
    inc %r10
    cmp %r11,%r9
    jne ff_aac_sbr_apply.L8190
    sub %r11,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 1534 (Map:B, straight) -/
def L81b7 : Program := parse("
    dec %r8
    cmp $0x3,%r8
    jb ff_aac_sbr_apply.L828a
    mov %edi,%r8d
    sub -0x30(%rbp),%r8d
    lea 0x3(%r8),%r9d
    mov -0x60(%rbp),%rbx
    lea (%rbx,%r9,4),%r9
    lea 0x2(%r8),%r10d
    lea (%rbx,%r10,4),%r10
    mov %r8d,%r11d
    inc %r11d
    lea (%rbx,%r11,4),%r11
    sub %rsi,%rdi
    lea (%rbx,%r8,4),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 1549 (Map:B, straight) -/
def L81b7_1 : Program := parse("
    mov $0x21998,%r14d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1552 (Map:B, straight) -/
def L8200 : Program := parse("
    lea (%r8,%r14,1),%r13d
    add $0xfffde668,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x8(%rdx),%xmm0
    vmovss %xmm0,(%rbx,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde669,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r11,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66a,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
")

set_option maxRecDepth 20000 in
/-- asm line 1567 (Map:B, straight) -/
def L8200_1 : Program := parse("
    vmovss %xmm0,(%r10,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66b,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r9,%r14,4)
    lea (%rdi,%r14,1),%r13
    add $0x4,%r13
    add $0x4,%r14
    cmp $0x21998,%r13
    jne ff_aac_sbr_apply.L8200
")

set_option maxRecDepth 20000 in
/-- asm line 1579 (Map:B, straight) -/
def L828a : Program := parse("
    cmp $0x3,%ecx
    mov -0x38(%rbp),%r8
    je ff_aac_sbr_apply.L8520
    movzwl 0x74c0e(%r8),%edi
    cmp %di,%si
    jae ff_aac_sbr_apply.L83ca
    mov %rdi,%r8
    sub %rsi,%r8
    mov %r8,%r9
    and $0x3,%r9
    je ff_aac_sbr_apply.L82f7
    mov %esi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1596 (Map:B, straight) -/
def L82d0 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0xc(%rdx),%xmm0
    mov -0x58(%rbp),%rbx
    vmovss %xmm0,(%rbx,%r10,4)
    dec %r11
    inc %r10
    cmp %r11,%r9
    jne ff_aac_sbr_apply.L82d0
    sub %r11,%rsi
")

set_option maxRecDepth 20000 in
/-- asm line 1607 (Map:B, straight) -/
def L82f7 : Program := parse("
    dec %r8
    cmp $0x3,%r8
    jb ff_aac_sbr_apply.L83ca
    mov %esi,%r8d
    sub -0x30(%rbp),%r8d
    lea 0x3(%r8),%r9d
    mov -0x60(%rbp),%rbx
    lea (%rbx,%r9,4),%r9
    lea 0x2(%r8),%r10d
    lea (%rbx,%r10,4),%r10
    mov %r8d,%r11d
    inc %r11d
    lea (%rbx,%r11,4),%r11
    sub %rdi,%rsi
    lea (%rbx,%r8,4),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 1622 (Map:B, straight) -/
def L82f7_1 : Program := parse("
    mov $0x21998,%r14d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1625 (Map:B, straight) -/
def L8340 : Program := parse("
    lea (%r8,%r14,1),%r13d
    add $0xfffde668,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0xc(%rdx),%xmm0
    vmovss %xmm0,(%rbx,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde669,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r11,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66a,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
")

set_option maxRecDepth 20000 in
/-- asm line 1640 (Map:B, straight) -/
def L8340_1 : Program := parse("
    vmovss %xmm0,(%r10,%r14,4)
    lea (%r8,%r14,1),%r13d
    add $0xfffde66b,%r13d
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r9,%r14,4)
    lea (%rsi,%r14,1),%r13
    add $0x4,%r13
    add $0x4,%r14
    cmp $0x21998,%r13
    jne ff_aac_sbr_apply.L8340
")

set_option maxRecDepth 20000 in
/-- asm line 1652 (Map:B, straight) -/
def L83ca : Program := parse("
    cmp $0x4,%ecx
    mov -0x38(%rbp),%r8
    je ff_aac_sbr_apply.L8520
    movzwl 0x74c10(%r8),%esi
    cmp %si,%di
    jae ff_aac_sbr_apply.L8509
    mov %rsi,%r8
    sub %rdi,%r8
    mov %r8,%r9
    and $0x3,%r9
    je ff_aac_sbr_apply.L8437
    mov %edi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1669 (Map:B, straight) -/
def L8410 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x10(%rdx),%xmm0
    mov -0x58(%rbp),%rbx
    vmovss %xmm0,(%rbx,%r10,4)
    dec %r11
    inc %r10
    cmp %r11,%r9
    jne ff_aac_sbr_apply.L8410
    sub %r11,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 1680 (Map:B, straight) -/
def L8437 : Program := parse("
    dec %r8
    cmp $0x3,%r8
    jb ff_aac_sbr_apply.L8509
    mov %edi,%r8d
    sub -0x30(%rbp),%r8d
    lea 0x3(%r8),%r9d
    mov -0x60(%rbp),%rbx
    lea (%rbx,%r9,4),%r9
    lea 0x2(%r8),%r10d
    lea (%rbx,%r10,4),%r10
    mov %r8d,%r11d
    inc %r11d
    lea (%rbx,%r11,4),%r11
    sub %rsi,%rdi
    lea (%rbx,%r8,4),%rsi
")

set_option maxRecDepth 20000 in
/-- asm line 1695 (Map:B, straight) -/
def L8437_1 : Program := parse("
    mov $0x21998,%ebx
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1698 (Map:B, straight) -/
def L8480 : Program := parse("
    lea (%r8,%rbx,1),%r14d
    add $0xfffde668,%r14d
    cmp $0x2f,%r14d
    ja ff_aac_sbr_apply.L9b40
    vmovss 0x10(%rdx),%xmm0
    vmovss %xmm0,(%rsi,%rbx,4)
    lea (%r8,%rbx,1),%r14d
    add $0xfffde669,%r14d
    cmp $0x2f,%r14d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r11,%rbx,4)
    lea (%r8,%rbx,1),%r14d
    add $0xfffde66a,%r14d
    cmp $0x2f,%r14d
    ja ff_aac_sbr_apply.L9b40
")

set_option maxRecDepth 20000 in
/-- asm line 1713 (Map:B, straight) -/
def L8480_1 : Program := parse("
    vmovss %xmm0,(%r10,%rbx,4)
    lea (%r8,%rbx,1),%r14d
    add $0xfffde66b,%r14d
    cmp $0x2f,%r14d
    ja ff_aac_sbr_apply.L9b40
    vmovss %xmm0,(%r9,%rbx,4)
    lea (%rdi,%rbx,1),%r14
    add $0x4,%r14
    add $0x4,%rbx
    cmp $0x21998,%r14
    jne ff_aac_sbr_apply.L8480
")

set_option maxRecDepth 20000 in
/-- asm line 1725 (Map:B, straight) -/
def L8509 : Program := parse("
    cmp $0x5,%ecx
    mov -0x38(%rbp),%r8
    jne ff_aac_sbr_apply.L9c18
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1730 (Map:B, straight) -/
def L8520 : Program := parse("
    cmpl $0x0,0x74b04(%r8)
    mov $0x0,%r11d
    mov -0x48(%rbp),%rbx
    mov -0x80(%rbp),%r14
    mov -0xe8(%rbp),%r13
    je ff_aac_sbr_apply.L8660
    cmpl $0x0,0x4(%rbx)
    je ff_aac_sbr_apply.L8660
    mov -0x68(%rbp),%rcx
    lea (%rcx,%rcx,2),%rcx
    shl $0x4,%rcx
    add %r14,%rcx
    mov $0x1,%edx
    mov -0x198(%rbp),%rsi
    xor %edi,%edi
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1747 (Map:B, straight) -/
def L8570 : Program := parse("
    movzwl -0x4(%rsi),%r8d
    movzwl -0x2(%rsi),%r10d
    add %r8d,%r10d
    shr $1,%r10d
    movzbl -0x1(%r13,%rdi,1),%r9d
    movslq 0x3908(%rbx),%r8
    sub -0x30(%rbp),%r10d
    cmp %r8,%rax
    jge ff_aac_sbr_apply.L85c0
    cmp $0x30,%r10d
    jae ff_aac_sbr_apply.L9b68
    mov %r10d,%r10d
    cmpb $0x1,(%r14,%r10,1)
    movzbl %r9b,%r9d
    cmovne %r11d,%r9d
")

set_option maxRecDepth 20000 in
/-- asm line 1762 (Map:B, straight) -/
def L8570_1 : Program := parse("
    jmp ff_aac_sbr_apply.L85cd
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1765 (Map:B, straight) -/
def L85c0 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b54
    mov %r10d,%r10d
")

set_option maxRecDepth 20000 in
/-- asm line 1769 (Map:B, straight) -/
def L85cd : Program := parse("
    mov %r9b,(%rcx,%r10,1)
")

set_option maxRecDepth 20000 in
/-- asm line 1770 (Map:B, straight) -/
def L85cd_1 : Program := parse("
    mov -0x38(%rbp),%r9
    mov 0x74b04(%r9),%r9d
    cmp %r9,%rdx
    jae ff_aac_sbr_apply.L8660
    movzwl -0x2(%rsi),%r9d
    movzwl (%rsi),%r10d
    add %r9d,%r10d
    shr $1,%r10d
    movzbl 0x0(%r13,%rdi,1),%r9d
    sub -0x30(%rbp),%r10d
    cmp %r8,%rax
    jge ff_aac_sbr_apply.L8620
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b68
    mov %r10d,%r8d
")

set_option maxRecDepth 20000 in
/-- asm line 1785 (Map:B, straight) -/
def L85cd_2 : Program := parse("
    cmpb $0x1,(%r14,%r8,1)
    movzbl %r9b,%r9d
    cmovne %r11d,%r9d
    jmp ff_aac_sbr_apply.L862d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1791 (Map:B, straight) -/
def L8620 : Program := parse("
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b54
    mov %r10d,%r8d
")

set_option maxRecDepth 20000 in
/-- asm line 1795 (Map:B, straight) -/
def L862d : Program := parse("
    mov %r9b,(%rcx,%r8,1)
    add $0x2,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 1797 (Map:B, straight) -/
def L862d_1 : Program := parse("
    mov -0x38(%rbp),%r8
    mov 0x74b04(%r8),%r8d
    cmp %r8,%rdi
    jae ff_aac_sbr_apply.L8660
    add $0x2,%rdx
    add $0x4,%rsi
    cmp $0x30,%rdi
    jne ff_aac_sbr_apply.L8570
    jmp ff_aac_sbr_apply.L9b59
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1808 (Map:B, straight) -/
def L8660 : Program := parse("
    cmpq $0x0,-0x50(%rbp)
    je ff_aac_sbr_apply.L8740
    mov -0x68(%rbp),%rcx
    lea (%rcx,%rcx,2),%rbx
    shl $0x4,%rbx
    add -0x80(%rbp),%rbx
    lea (%rax,%rax,2),%r14
    shl $0x4,%r14
    add -0x1a8(%rbp),%r14
    mov -0x30(%rbp),%eax
    neg %eax
    mov %rax,-0x78(%rbp)
    xor %r13d,%r13d
    jmp ff_aac_sbr_apply.L86d7
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1824 (Map:B, straight) -/
def L86a0 : Program := parse("
    xor %esi,%esi
    mov %eax,%edx
    sub -0x30(%rbp),%edx
    cmp $0x31,%edx
    jae ff_aac_sbr_apply.L9b4f
")

set_option maxRecDepth 20000 in
/-- asm line 1830 (Map:B, call_mem) -/
def L86b0 : Program := parse("
    inc %r13
    mov %edx,%edi
    add %r14,%rdi
    sub %eax,%ecx
    movslq %ecx,%rdx
    movzbl %sil,%esi
    vzeroupper
    call memset
")

set_option maxRecDepth 20000 in
/-- asm line 1838 (Map:B, straight) -/
def L86b0_1 : Program := parse("
    cmp -0x50(%rbp),%r13
    vmovss LCPI14_5(%rip),%xmm9
    je ff_aac_sbr_apply.L8740
")

set_option maxRecDepth 20000 in
/-- asm line 1842 (Map:B, straight) -/
def L86d7 : Program := parse("
    movzwl (%r15,%r13,2),%eax
    movzwl 0x2(%r15,%r13,2),%ecx
    cmp %cx,%ax
    jae ff_aac_sbr_apply.L86a0
    mov %ecx,%edx
    sub %rax,%rdx
    mov -0x78(%rbp),%rsi
    add %eax,%esi
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1852 (Map:B, straight) -/
def L8700 : Program := parse("
    cmp $0x30,%esi
    jae ff_aac_sbr_apply.L9b36
    mov %esi,%edi
    cmpb $0x0,(%rbx,%rdi,1)
    jne ff_aac_sbr_apply.L8720
    inc %esi
    dec %rdx
    jne ff_aac_sbr_apply.L8700
    jmp ff_aac_sbr_apply.L86a0
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1863 (Map:B, straight) -/
def L8720 : Program := parse("
    mov $0x1,%sil
    mov %eax,%edx
    sub -0x30(%rbp),%edx
    cmp $0x31,%edx
    jb ff_aac_sbr_apply.L86b0
    jmp ff_aac_sbr_apply.L9b4f
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1871 (Map:B, straight) -/
def L8740 : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%eax
    mov -0x68(%rbp),%rdx
    cmp %rax,%rdx
    mov -0x38(%rbp),%r8
    jae ff_aac_sbr_apply.L8818
    lea 0x1(%rdx),%rcx
    add $0xc0,%r12
    addq $0xc0,-0x58(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 1880 (Map:B, straight) -/
def L8740_1 : Program := parse("
    addq $0xc0,-0x60(%rbp)
    mov %rdx,%rax
    cmp $0x8,%rdx
    jne ff_aac_sbr_apply.L7db0
    jmp ff_aac_sbr_apply.L9b7c
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1887 (Map:B, straight) -/
def L8790 : Program := parse("
    mov 0x28978(%r8),%eax
    mov %eax,-0x30(%rbp)
    xor %eax,%eax
    jmp ff_aac_sbr_apply.L881c
")

set_option maxRecDepth 20000 in
/-- asm line 1892 (Map:B, call_avlog) -/
def L879e : Program := parse("
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    mov $0x10,%esi
    lea L_str_36(%rip),%rdx
    xor %eax,%eax
    vzeroupper
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 1899 (Map:B, store_run) -/
def L879e_1 : Program := parse("
    mov -0x38(%rbp),%rax
    movq $0x0,0x28924(%rax)
    movl $0x0,0x28930(%rax)
    movl $0x20,0x28978(%rax)
    movl $0x0,0x28980(%rax)
    movl $0xffffffff,0x41d68(%rax)
    movl $0xffffffff,0x2c2a8(%rax)
")

set_option maxRecDepth 20000 in
/-- asm line 1906 (Map:B, straight) -/
def L879e_2 : Program := parse("
    mov -0x168(%rbp),%rax
    movw $0xffff,0x4(%rax)
    movl $0xffffffff,(%rax)
    jmp ff_aac_sbr_apply.L9927
")

set_option maxRecDepth 20000 in
/-- asm line 1911 (Env:A, straight) -/
def L8818 : Program := parse("
    mov -0x80(%rbp),%r10
")

set_option maxRecDepth 20000 in
/-- asm line 1913 (Env:A, straight) -/
def L881c : Program := parse("
    lea 0x3904(%rbx),%rcx
    mov %rcx,-0x110(%rbp)
    mov %eax,%ecx
    lea (%rcx,%rcx,2),%rdx
    shl $0x4,%rdx
    vmovups (%r10,%rdx,1),%ymm0
    vmovups 0x10(%r10,%rdx,1),%ymm1
    vmovups %ymm1,0x10(%r10)
    vmovups %ymm0,(%r10)
")

set_option maxRecDepth 20000 in
/-- asm line 1922 (Env:A, straight) -/
def L881c_1 : Program := parse("
    cmpl $0x0,0x28954(%r8)
    je ff_aac_sbr_apply.L8947
    test %eax,%eax
    je ff_aac_sbr_apply.L98e0
    movzbl 0x15a9c(%rbx),%r12d
    cmp $0x13,%r12d
    jae ff_aac_sbr_apply.L914e
    movslq -0x30(%rbp),%rdx
    lea (%rdx,%rdx,4),%r14
    shl $0x6,%r14
    mov -0xb8(%rbp),%rdx
    lea (%rdx,%r14,1),%rdi
    mov -0x38(%rbp),%r8
    cmpl $0x0,0x28980(%r8)
    je ff_aac_sbr_apply.L8b6b
")

set_option maxRecDepth 20000 in
/-- asm line 1937 (Env:A, straight) -/
def L881c_2 : Program := parse("
    movzbl 0x15a9d(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
    add %r15d,%r15d
    mov %rdi,-0x50(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 1946 (Env:A, call_ind) -/
def L881c_3 : Program := parse("
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 1952 (Env:A, straight) -/
def L881c_4 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    add %r14,%rax
    add %rax,%r12
    xor %ebx,%ebx
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1959 (Env:A, straight) -/
def L8900 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86de0(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 1962 (Env:A, call_ind) -/
def L8900_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8b2a
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 1970 (Env:A, straight) -/
def L8900_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8900
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 1975 (Env:A, straight) -/
def L8947 : Program := parse("
    test %eax,%eax
    je ff_aac_sbr_apply.L98e0
    movslq -0x30(%rbp),%rcx
    mov %rcx,-0x60(%rbp)
    mov $0x1,%ecx
")

set_option maxRecDepth 20000 in
/-- asm line 1980 (Env:A, straight) -/
def L8947_1 : Program := parse("
    mov -0x38(%rbp),%rsi
    mov %rsi,%rdi
    xor %r8d,%r8d
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 1985 (Env:A, straight) -/
def L8970 : Program := parse("
    movzbl 0x15a9c(%rbx,%r8,1),%r9d
    mov %rcx,%r8
    movzbl 0xc(%rbx,%rcx,1),%ecx
    mov -0xb0(%rbp),%rdx
    lea 0x4c284(%rdx),%r14
    add $0x4c252,%rdx
    test %cl,%cl
    cmove %rdx,%r14
    cmp $0x12,%r9d
    ja ff_aac_sbr_apply.L9146
    cmp $0x1,%cl
    ja ff_aac_sbr_apply.L9a64
    mov %r9,%rdx
    mov -0x48(%rbp),%rax
    movzbl 0x15a9c(%rax,%r8,1),%r12d
")

set_option maxRecDepth 20000 in
/-- asm line 2000 (Env:A, straight) -/
def L8970_1 : Program := parse("
    sub %edx,%r12d
    add %r12d,%r12d
    shl $0x4,%edx
    add -0x190(%rbp),%rdx
    mov %rdx,-0x80(%rbp)
    xor %ebx,%ebx
    mov %rdi,-0x78(%rbp)
    mov %r8,-0x68(%rbp)
    jmp ff_aac_sbr_apply.L89f3
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2011 (Env:A, straight) -/
def L89e0 : Program := parse("
    mov -0x48(%rbp),%rax
    movzbl 0xc(%rax,%r8,1),%ecx
    cmp $0x2,%cl
    jae ff_aac_sbr_apply.L9a64
")

set_option maxRecDepth 20000 in
/-- asm line 2016 (Env:A, straight) -/
def L89f3 : Program := parse("
    movzbl %cl,%eax
    mov 0x74b00(%rsi,%rax,4),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L8b00
    mov %rbx,%rdx
    inc %rbx
    movzwl 0x2(%r14,%rdx,2),%eax
    movzwl (%r14,%rdx,2),%r13d
    cmp %ax,%r13w
    jae ff_aac_sbr_apply.L89e0
    mov %rdx,-0x58(%rbp)
    sub %r13d,%eax
    imul %r12d,%eax
    mov %eax,-0x50(%rbp)
    lea 0x0(,%r13,4),%r15
")

set_option maxRecDepth 20000 in
/-- asm line 2031 (Env:A, straight) -/
def L89f3_1 : Program := parse("
    add %r13,%r15
    shl $0x6,%r15d
    add -0x80(%rbp),%r15
    vxorps %xmm1,%xmm1,%xmm1
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2037 (Env:A, straight) -/
def L8a50 : Program := parse("
    vmovss %xmm1,-0x30(%rbp)
    mov %r15,%rdi
    mov %r12d,%esi
")

set_option maxRecDepth 20000 in
/-- asm line 2040 (Env:A, call_ind) -/
def L8a50_1 : Program := parse("
    mov -0x38(%rbp),%rax
    vzeroupper
    call *0x88b08(%rax)
")

set_option maxRecDepth 20000 in
/-- asm line 2043 (Env:A, straight) -/
def L8a50_2 : Program := parse("
    vmovss -0x30(%rbp),%xmm1
    mov -0x38(%rbp),%rsi
    vaddss %xmm0,%xmm1,%xmm1
    inc %r13
    movzwl (%r14,%rbx,2),%ecx
    add $0x140,%r15
    cmp %rcx,%r13
    jb ff_aac_sbr_apply.L8a50
    mov -0x58(%rbp),%rax
    movzwl (%r14,%rax,2),%eax
    cmp %cx,%ax
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x78(%rbp),%rdi
    mov -0x68(%rbp),%r8
    mov -0x50(%rbp),%edx
")

set_option maxRecDepth 20000 in
/-- asm line 2058 (Env:A, straight) -/
def L8a50_3 : Program := parse("
    jae ff_aac_sbr_apply.L89e0
    mov %rax,%rcx
    sub -0x60(%rbp),%rcx
    cmp $0x2f,%rcx
    ja ff_aac_sbr_apply.L99f8
    vcvtsi2ss %edx,%xmm15,%xmm0
    vdivss %xmm0,%xmm1,%xmm0
    inc %rax
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2068 (Env:A, straight) -/
def L8ad0 : Program := parse("
    vmovss %xmm0,0x86de0(%rdi,%rcx,4)
")

set_option maxRecDepth 20000 in
/-- asm line 2069 (Env:A, straight) -/
def L8ad0_1 : Program := parse("
    movzwl (%r14,%rbx,2),%edx
    cmp %rdx,%rax
    jae ff_aac_sbr_apply.L89e0
    inc %rcx
    inc %rax
    cmp $0x30,%rcx
    jb ff_aac_sbr_apply.L8ad0
    jmp ff_aac_sbr_apply.L99f8
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2079 (Env:A, straight) -/
def L8b00 : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%eax
    cmp %rax,%r8
    jae ff_aac_sbr_apply.L9146
    lea 0x1(%r8),%rcx
    add $0xc0,%rdi
    cmp $0x8,%r8
    jne ff_aac_sbr_apply.L8970
    jmp ff_aac_sbr_apply.L9bff
")

set_option maxRecDepth 20000 in
/-- asm line 2089 (Env:A, straight) -/
def L8b2a : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x50(%rbp),%rdi
    cmp $0x2,%ecx
    jae ff_aac_sbr_apply.L8b77
    jmp ff_aac_sbr_apply.L9146
")

set_option maxRecDepth 20000 in
/-- asm line 2100 (HfGen, straight) -/
def L8b4f : Program := parse("
    mov 0x28978(%r8),%eax
    add 0x28980(%r8),%eax
    sub %r12d,%eax
    ja ff_aac_sbr_apply.L7cbf
    jmp ff_aac_sbr_apply.L7ce4
")

set_option maxRecDepth 20000 in
/-- asm line 2106 (Env:A, straight) -/
def L8b6b : Program := parse("
    mov $0x1,%sil
    cmp $0x2,%ecx
    jb ff_aac_sbr_apply.L9146
")

set_option maxRecDepth 20000 in
/-- asm line 2110 (Env:A, straight) -/
def L8b77 : Program := parse("
    movzbl 0x15a9d(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L9146
    mov %r14,-0x50(%rbp)
    mov $0x1,%dl
    test %sil,%sil
    jne ff_aac_sbr_apply.L8c4c
    movzbl 0x15a9e(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
    add %r15d,%r15d
")

set_option maxRecDepth 20000 in
/-- asm line 2125 (Env:A, call_ind) -/
def L8b77_1 : Program := parse("
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2132 (Env:A, straight) -/
def L8b77_2 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2140 (Env:A, straight) -/
def L8bf0 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86ea0(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2143 (Env:A, call_ind) -/
def L8bf0_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8c33
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2151 (Env:A, straight) -/
def L8bf0_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8bf0
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2156 (Env:A, straight) -/
def L8c33 : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 2164 (Env:A, straight) -/
def L8c4c : Program := parse("
    cmp $0x3,%ecx
    jb ff_aac_sbr_apply.L9146
    movzbl 0x15a9e(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L9146
    mov $0x1,%sil
    test %dl,%dl
    jne ff_aac_sbr_apply.L8d26
    movzbl 0x15a9f(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2179 (Env:A, call_ind) -/
def L8c4c_1 : Program := parse("
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2187 (Env:A, straight) -/
def L8c4c_2 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2194 (Env:A, straight) -/
def L8cc9 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86f60(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2197 (Env:A, call_ind) -/
def L8cc9_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8d0c
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2205 (Env:A, straight) -/
def L8cc9_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8cc9
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2210 (Env:A, straight) -/
def L8d0c : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 2218 (Env:A, straight) -/
def L8d26 : Program := parse("
    cmp $0x4,%ecx
    jb ff_aac_sbr_apply.L9146
    movzbl 0x15a9f(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L9146
    mov $0x1,%dl
    test %sil,%sil
    jne ff_aac_sbr_apply.L8dff
    movzbl 0x15aa0(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2233 (Env:B, call_ind) -/
def L8d26_1 : Program := parse("
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2241 (Env:B, straight) -/
def L8d26_2 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2248 (Env:B, straight) -/
def L8da3 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87020(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2251 (Env:B, call_ind) -/
def L8da3_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8de6
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2259 (Env:B, straight) -/
def L8da3_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8da3
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2264 (Env:B, straight) -/
def L8de6 : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 2272 (Env:B, straight) -/
def L8dff : Program := parse("
    cmp $0x5,%ecx
    jb ff_aac_sbr_apply.L9146
    movzbl 0x15aa0(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L9146
    mov $0x1,%sil
    test %dl,%dl
    jne ff_aac_sbr_apply.L8ed9
    movzbl 0x15aa1(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2287 (Env:B, call_ind) -/
def L8dff_1 : Program := parse("
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2295 (Env:B, straight) -/
def L8dff_2 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2302 (Env:B, straight) -/
def L8e7c : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x870e0(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2305 (Env:B, call_ind) -/
def L8e7c_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8ebf
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2313 (Env:B, straight) -/
def L8e7c_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8e7c
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2318 (Env:B, straight) -/
def L8ebf : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 2326 (Env:B, straight) -/
def L8ed9 : Program := parse("
    cmp $0x6,%ecx
    jb ff_aac_sbr_apply.L9146
    movzbl 0x15aa1(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L9146
    mov $0x1,%dl
    test %sil,%sil
    jne ff_aac_sbr_apply.L8fa4
    movzbl 0x15aa2(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2341 (Env:B, call_ind) -/
def L8ed9_1 : Program := parse("
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
")

set_option maxRecDepth 20000 in
/-- asm line 2349 (Env:B, straight) -/
def L8ed9_2 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2356 (Env:B, straight) -/
def L8f56 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x871a0(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2359 (Env:B, call_ind) -/
def L8f56_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L8f93
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r13)
")

set_option maxRecDepth 20000 in
/-- asm line 2365 (Env:B, straight) -/
def L8f56_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8f56
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2370 (Env:B, straight) -/
def L8f93 : Program := parse("
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    mov %r14,%rdi
")

set_option maxRecDepth 20000 in
/-- asm line 2377 (Env:B, straight) -/
def L8fa4 : Program := parse("
    cmp $0x7,%ecx
    jb ff_aac_sbr_apply.L9063
    movzbl 0x15aa2(%rbx),%r12d
    cmp $0x12,%r12d
    ja ff_aac_sbr_apply.L913a
    mov %rdi,%r14
    mov $0x1,%sil
    test %dl,%dl
    jne ff_aac_sbr_apply.L907f
    mov -0x48(%rbp),%rax
    movzbl 0x15aa3(%rax),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
")

set_option maxRecDepth 20000 in
/-- asm line 2392 (Env:B, straight) -/
def L8fa4_1 : Program := parse("
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2394 (Env:B, call_ind) -/
def L8fa4_2 : Program := parse("
    add %r15d,%r15d
    lea (%r14,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov -0x38(%rbp),%r13
    vzeroupper
    call *0x88b08(%r13)
")

set_option maxRecDepth 20000 in
/-- asm line 2401 (Env:B, straight) -/
def L8fa4_3 : Program := parse("
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2408 (Env:B, straight) -/
def L9026 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87260(%r13,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2411 (Env:B, call_ind) -/
def L9026_1 : Program := parse("
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L9070
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r13)
")

set_option maxRecDepth 20000 in
/-- asm line 2417 (Env:B, straight) -/
def L9026_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L9026
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2422 (Env:B, straight) -/
def L9063 : Program := parse("
    vmovss LCPI14_5(%rip),%xmm9
    jmp ff_aac_sbr_apply.L9146
")

set_option maxRecDepth 20000 in
/-- asm line 2425 (Env:B, straight) -/
def L9070 : Program := parse("
    mov -0x48(%rbp),%rcx
    mov 0x8(%rcx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2431 (Env:B, straight) -/
def L907f : Program := parse("
    cmp $0x8,%ecx
    jb ff_aac_sbr_apply.L913a
    mov -0x48(%rbp),%rdx
    movzbl 0x15aa3(%rdx),%ebx
    cmp $0x12,%ebx
    ja ff_aac_sbr_apply.L913a
    test %sil,%sil
    jne ff_aac_sbr_apply.L99cf
    mov -0x48(%rbp),%rax
    movzbl 0x15aa4(%rax),%r15d
    sub %ebx,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%rbx,%rbx,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 2446 (Env:B, straight) -/
def L907f_1 : Program := parse("
    vmovss %xmm0,-0x30(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2447 (Env:B, call_ind) -/
def L907f_2 : Program := parse("
    add %r15d,%r15d
    lea (%r14,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov -0x38(%rbp),%r14
    vzeroupper
    call *0x88b08(%r14)
")

set_option maxRecDepth 20000 in
/-- asm line 2454 (Env:B, straight) -/
def L907f_3 : Program := parse("
    shl $0x4,%ebx
    mov -0x50(%rbp),%r12
    add -0x70(%rbp),%r12
    add %rbx,%r12
    xor %ebx,%ebx
")

set_option maxRecDepth 20000 in
/-- asm line 2460 (Env:B, straight) -/
def L90f9 : Program := parse("
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87320(%r14,%rbx,4)
    inc %rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2463 (Env:B, call_ind) -/
def L90f9_1 : Program := parse("
    mov 0x28980(%r14),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L99c6
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r14)
")

set_option maxRecDepth 20000 in
/-- asm line 2469 (Env:B, straight) -/
def L90f9_2 : Program := parse("
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L90f9
    jmp ff_aac_sbr_apply.L9b95
")

set_option maxRecDepth 20000 in
/-- asm line 2474 (Env:B, straight) -/
def L913a : Program := parse("
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x48(%rbp),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2477 (Gain, straight) -/
def L9146 : Program := parse("
    test %eax,%eax
    je ff_aac_sbr_apply.L98e0
")

set_option maxRecDepth 20000 in
/-- asm line 2480 (Gain, straight) -/
def L914e : Program := parse("
    mov -0x38(%rbp),%rax
    mov 0x74b0c(%rax),%eax
    mov %rax,-0x78(%rbp)
    test %rax,%rax
    je ff_aac_sbr_apply.L98e0
")

set_option maxRecDepth 20000 in
/-- asm line 2485 (Gain, straight) -/
def L914e_1 : Program := parse("
    mov -0x38(%rbp),%r10
    mov 0x28978(%r10),%ecx
    movzwl 0x74c12(%r10),%eax
    mov %ax,-0x82(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2489 (Gain, straight) -/
def L914e_2 : Program := parse("
    mov -0x98(%rbp),%rax
    add -0x160(%rbp),%rax
    mov %rax,-0x98(%rbp)
    mov %ecx,%eax
    neg %eax
    mov %eax,-0xf4(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2495 (Gain, straight) -/
def L914e_3 : Program := parse("
    mov -0x158(%rbp),%rdi
    mov -0x108(%rbp),%r8
    mov -0xd0(%rbp),%r9
    mov -0x100(%rbp),%r11
    xor %r12d,%r12d
    jmp ff_aac_sbr_apply.L91f7
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2503 (Gain, straight) -/
def L91c0 : Program := parse("
    inc %r12
    mov 0x8(%rbx),%eax
    addq $0x30,-0x98(%rbp)
    add $0xc0,%r11
    add $0x30,%r10
    add $0xc0,%r9
    add $0xc0,%r8
    add $0xc0,%rdi
    cmp %rax,%r12
    jae ff_aac_sbr_apply.L98e0
")

set_option maxRecDepth 20000 in
/-- asm line 2514 (Gain, straight) -/
def L91f7 : Program := parse("
    mov 0x3908(%rbx),%eax
    cmp %rax,%r12
    jne ff_aac_sbr_apply.L9206
    xor %edx,%edx
    jmp ff_aac_sbr_apply.L9215
")

set_option maxRecDepth 20000 in
/-- asm line 2520 (Gain, straight) -/
def L9206 : Program := parse("
    mov -0x110(%rbp),%rax
    mov (%rax),%eax
    cmp %rax,%r12
    setne %dl
")

set_option maxRecDepth 20000 in
/-- asm line 2525 (Gain, straight) -/
def L9215 : Program := parse("
    mov %r12,%rax
    shl $0x6,%rax
    lea (%rax,%rax,2),%rsi
    mov -0xd0(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0x60(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2531 (Gain, straight) -/
def L9215_1 : Program := parse("
    mov -0x108(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xe8(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2534 (Gain, straight) -/
def L9215_2 : Program := parse("
    mov -0x170(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xe0(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2537 (Gain, straight) -/
def L9215_3 : Program := parse("
    mov -0x178(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xd8(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2540 (Gain, straight) -/
def L9215_4 : Program := parse("
    add -0x100(%rbp),%rsi
    mov %rsi,-0x80(%rbp)
    mov %edx,-0x30(%rbp)
    movzbl %dl,%eax
    vcvtsi2ss %eax,%xmm15,%xmm0
")

set_option maxRecDepth 20000 in
/-- asm line 2545 (Gain, straight) -/
def L9215_5 : Program := parse("
    movzwl -0x82(%rbp),%eax
    mov %eax,%esi
    xor %edx,%edx
    mov %r12,-0x58(%rbp)
    jmp ff_aac_sbr_apply.L929e
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2552 (Gain, straight) -/
def L9290 : Program := parse("
    cmp -0x78(%rbp),%rdx
    mov -0x48(%rbp),%rbx
    je ff_aac_sbr_apply.L91c0
")

set_option maxRecDepth 20000 in
/-- asm line 2556 (Gain, straight) -/
def L929e : Program := parse("
    cmp $0x1d,%rdx
    je ff_aac_sbr_apply.L99fd
    movzwl %si,%eax
    mov %eax,%r13d
    sub %ecx,%r13d
    mov %rdx,-0x50(%rbp)
    inc %rdx
")

set_option maxRecDepth 20000 in
/-- asm line 2563 (Gain, straight) -/
def L929e_1 : Program := parse("
    mov -0x38(%rbp),%rsi
    movzwl 0x74c12(%rsi,%rdx,2),%esi
    mov %esi,%ebx
    sub %ecx,%ebx
    cmp $0x8,%r12
    jae ff_aac_sbr_apply.L98bc
    cmp %ebx,%r13d
    jae ff_aac_sbr_apply.L93d0
    movslq %r13d,%rax
    cmp $0x31,%rax
    mov $0x30,%ebx
    cmovae %rax,%rbx
    cmp $0x2f,%r13d
    mov -0x98(%rbp),%r12
    ja ff_aac_sbr_apply.L9a50
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2580 (Gain, straight) -/
def L9300 : Program := parse("
    vmovss -0x1f80(%r11,%rax,4),%xmm1
    vmovss -0x1980(%r11,%rax,4),%xmm2
    vaddss %xmm2,%xmm9,%xmm3
    vdivss %xmm3,%xmm1,%xmm4
    vmulss %xmm4,%xmm2,%xmm5
    vsqrtss %xmm5,%xmm5,%xmm5
    vmovss %xmm5,-0xc00(%r11,%rax,4)
")

set_option maxRecDepth 20000 in
/-- asm line 2587 (Gain, straight) -/
def L9300_1 : Program := parse("
    movzbl (%r12,%rax,1),%esi
    vcvtsi2ss %esi,%xmm15,%xmm5
    vmulss %xmm5,%xmm4,%xmm4
    vsqrtss %xmm4,%xmm4,%xmm4
    vmovss %xmm4,-0x600(%r11,%rax,4)
")

set_option maxRecDepth 20000 in
/-- asm line 2592 (Gain, straight) -/
def L9300_2 : Program := parse("
    cmpb $0x0,0x86c60(%r10,%rax,1)
    je ff_aac_sbr_apply.L9370
    vmulss %xmm2,%xmm1,%xmm1
    vaddss -0x1200(%r11,%rax,4),%xmm9,%xmm2
    vmulss %xmm2,%xmm3,%xmm2
    jmp ff_aac_sbr_apply.L9386
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2600 (Gain, straight) -/
def L9370 : Program := parse("
    vaddss -0x1200(%r11,%rax,4),%xmm9,%xmm3
    vmulss %xmm0,%xmm2,%xmm2
    vaddss %xmm2,%xmm9,%xmm2
    vmulss %xmm3,%xmm2,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 2605 (Gain, straight) -/
def L9386 : Program := parse("
    vdivss %xmm2,%xmm1,%xmm1
    vsqrtss %xmm1,%xmm1,%xmm1
    vaddss LCPI14_14(%rip),%xmm1,%xmm1
    vmovss %xmm1,(%r11,%rax,4)
    inc %rax
")

set_option maxRecDepth 20000 in
/-- asm line 2610 (Gain, straight) -/
def L9386_1 : Program := parse("
    mov -0x38(%rbp),%rsi
    movzwl 0x74c12(%rsi,%rdx,2),%esi
    movzwl %si,%r15d
    mov %r15d,%r14d
    sub %ecx,%r14d
    cmp %r14,%rax
    jae ff_aac_sbr_apply.L93f0
    cmp %rax,%rbx
    jne ff_aac_sbr_apply.L9300
    jmp ff_aac_sbr_apply.L9a50
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2622 (Gain, straight) -/
def L93d0 : Program := parse("
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
    jmp ff_aac_sbr_apply.L9530
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2627 (Gain, straight) -/
def L93f0 : Program := parse("
    mov -0x38(%rbp),%rax
    mov -0x50(%rbp),%rbx
    movzwl 0x74c12(%rax,%rbx,2),%eax
    mov %eax,%r13d
    sub %ecx,%r13d
    cmp %r14d,%r13d
    jae ff_aac_sbr_apply.L9520
    lea -0x31(%r13),%ebx
    mov %eax,%r12d
    sub %r15d,%r12d
    cmp %r12d,%ebx
    jae ff_aac_sbr_apply.L9bc5
    mov %r13d,%ebx
    mov %r14d,%r12d
    sub %r13d,%r12d
")

set_option maxRecDepth 20000 in
/-- asm line 2642 (Gain, straight) -/
def L93f0_1 : Program := parse("
    and $0x7,%r12d
    mov %rbx,-0x68(%rbp)
    vxorps %xmm1,%xmm1,%xmm1
    vxorps %xmm2,%xmm2,%xmm2
    je ff_aac_sbr_apply.L9458
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2649 (Gain, straight) -/
def L9440 : Program := parse("
    vaddss (%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd80(%r9,%rbx,4),%xmm1,%xmm1
    inc %rbx
    dec %r12
    jne ff_aac_sbr_apply.L9440
")

set_option maxRecDepth 20000 in
/-- asm line 2655 (Gain, straight) -/
def L9458 : Program := parse("
    mov -0x68(%rbp),%r12
    sub %r14,%r12
    cmp $0xfffffffffffffff8,%r12
    ja ff_aac_sbr_apply.L9504
    add -0xf4(%rbp),%r15d
")

set_option maxRecDepth 20000 in
/-- asm line 2661 (Gain, vector) -/
def L9470 : Program := parse("
    vaddss (%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd80(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x4(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd84(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x8(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd88(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0xc(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd8c(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x10(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd90(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x14(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd94(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x18(%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd98(%r9,%rbx,4),%xmm1,%xmm1
    vaddss 0x1c(%r9,%rbx,4),%xmm2,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 2676 (Gain, straight) -/
def L9470_1 : Program := parse("
    vaddss 0xd9c(%r9,%rbx,4),%xmm1,%xmm1
    add $0x8,%rbx
    cmp %rbx,%r15
    jne ff_aac_sbr_apply.L9470
")

set_option maxRecDepth 20000 in
/-- asm line 2681 (Gain, straight) -/
def L9504 : Program := parse("
    vmovss LCPI14_13(%rip),%xmm3
    vaddss %xmm3,%xmm2,%xmm2
    vaddss %xmm3,%xmm1,%xmm1
    jmp ff_aac_sbr_apply.L952c
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2687 (Gain, straight) -/
def L9520 : Program := parse("
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 2690 (Gain, straight) -/
def L952c : Program := parse("
    mov -0x58(%rbp),%r12
")

set_option maxRecDepth 20000 in
/-- asm line 2692 (Gain, straight) -/
def L9530 : Program := parse("
    mov -0x38(%rbp),%rbx
    mov 0x28950(%rbx),%ebx
    cmp $0x3,%rbx
    ja ff_aac_sbr_apply.L9b72
    vdivss %xmm1,%xmm2,%xmm1
    vsqrtss %xmm1,%xmm1,%xmm1
    lea limgain(%rip),%r14
    vmulss (%r14,%rbx,4),%xmm1,%xmm1
    vminss LCPI14_15(%rip),%xmm1,%xmm1
    movzwl %si,%ebx
    sub %ecx,%ebx
    cmp %ebx,%r13d
    jae ff_aac_sbr_apply.L9617
    cmp $0x7,%r12
    ja ff_aac_sbr_apply.L9b81
")

set_option maxRecDepth 20000 in
/-- asm line 2707 (Gain, straight) -/
def L9530_1 : Program := parse("
    mov %r13d,%eax
    cmp $0x31,%rax
    mov $0x30,%r14d
    cmovae %rax,%r14
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9a55
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2715 (Gain, straight) -/
def L95a0 : Program := parse("
    vmovss (%r8,%rax,4),%xmm2
    vmulss %xmm2,%xmm1,%xmm3
    vmovss 0xc00(%r8,%rax,4),%xmm4
    vdivss %xmm4,%xmm3,%xmm3
    vminss %xmm2,%xmm3,%xmm2
    vmovss %xmm2,(%r8,%rax,4)
    vminss %xmm4,%xmm1,%xmm2
")

set_option maxRecDepth 20000 in
/-- asm line 2722 (Gain, straight) -/
def L95a0_1 : Program := parse("
    vmovss %xmm2,0xc00(%r8,%rax,4)
    inc %rax
")

set_option maxRecDepth 20000 in
/-- asm line 2724 (Gain, straight) -/
def L95a0_2 : Program := parse("
    mov -0x38(%rbp),%rsi
    movzwl 0x74c12(%rsi,%rdx,2),%esi
    mov %esi,%ebx
    sub %ecx,%ebx
    cmp %rbx,%rax
    jae ff_aac_sbr_apply.L9600
    cmp %rax,%r14
    jne ff_aac_sbr_apply.L95a0
    jmp ff_aac_sbr_apply.L9a55
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2735 (Gain, straight) -/
def L9600 : Program := parse("
    mov -0x38(%rbp),%rax
    mov -0x50(%rbp),%r14
    movzwl 0x74c12(%rax,%r14,2),%eax
    mov %eax,%r13d
    sub %ecx,%r13d
")

set_option maxRecDepth 20000 in
/-- asm line 2741 (Gain, straight) -/
def L9617 : Program := parse("
    cmp %ebx,%r13d
    jae ff_aac_sbr_apply.L9820
    cmp $0x7,%r12
    ja ff_aac_sbr_apply.L9b8b
    cmp $0x31,%r13d
    mov $0x30,%r14d
    cmovae %r13d,%r14d
    add %ecx,%r14d
    sub %eax,%r14d
    not %eax
    add %ecx,%eax
    add %ebx,%eax
    cmp %eax,%r14d
    jbe ff_aac_sbr_apply.L9b90
    mov %ebx,%r12d
")

set_option maxRecDepth 20000 in
/-- asm line 2756 (Gain, straight) -/
def L9617_1 : Program := parse("
    mov %r13d,%eax
    mov %r12d,%r14d
    sub %r13d,%r14d
    vxorps %xmm1,%xmm1,%xmm1
    mov %rax,%rbx
    vxorps %xmm2,%xmm2,%xmm2
    test $0x1,%r14b
    je ff_aac_sbr_apply.L96d3
    mov -0xe0(%rbp),%rbx
    vmovss (%rbx,%rax,4),%xmm3
    cmpb $0x0,-0x30(%rbp)
    je ff_aac_sbr_apply.L968d
    vcmpeqss %xmm1,%xmm3,%xmm1
    vmovss LCPI14_5(%rip),%xmm2
    vandps %xmm2,%xmm1,%xmm1
")

set_option maxRecDepth 20000 in
/-- asm line 2772 (Gain, vector) -/
def L968d : Program := parse("
    mov -0x60(%rbp),%rbx
    vmovss (%rbx,%rax,4),%xmm2
    mov -0x80(%rbp),%rbx
    vmovss (%rbx,%rax,4),%xmm4
    mov -0xd8(%rbp),%rbx
    vmulss (%rbx,%rax,4),%xmm4,%xmm5
    vmulss %xmm5,%xmm4,%xmm4
    vmulss %xmm3,%xmm3,%xmm3
    vaddss %xmm3,%xmm4,%xmm3
    mov -0xe8(%rbp),%rbx
    vmovss (%rbx,%rax,4),%xmm4
    vmulss %xmm1,%xmm4,%xmm1
    vmulss %xmm1,%xmm4,%xmm1
    vaddss %xmm1,%xmm3,%xmm1
    lea 0x1(%rax),%rbx
")

set_option maxRecDepth 20000 in
/-- asm line 2788 (Gain, straight) -/
def L96d3 : Program := parse("
    lea -0x1(%r12),%r14
    cmp %rax,%r14
    jne ff_aac_sbr_apply.L97b7
")

set_option maxRecDepth 20000 in
/-- asm line 2792 (Gain, straight) -/
def L96e1 : Program := parse("
    vmovss LCPI14_13(%rip),%xmm3
    vaddss %xmm3,%xmm2,%xmm2
    vaddss %xmm3,%xmm1,%xmm1
    vdivss %xmm1,%xmm2,%xmm1
    vsqrtss %xmm1,%xmm1,%xmm1
    vminss LCPI14_16(%rip),%xmm1,%xmm1
    movzwl %si,%ebx
    sub %ecx,%ebx
    cmp %ebx,%r13d
    mov -0x58(%rbp),%r12
    jae ff_aac_sbr_apply.L9290
    jmp ff_aac_sbr_apply.L983f
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2806 (Gain, straight) -/
def L9720 : Program := parse("
    vcmpeqss %xmm3,%xmm5,%xmm3
    vmovss LCPI14_5(%rip),%xmm7
    vandps %xmm7,%xmm3,%xmm3
")

set_option maxRecDepth 20000 in
/-- asm line 2810 (Gain, vector) -/
def L9731 : Program := parse("
    vaddss -0x1f84(%rdi,%rbx,4),%xmm2,%xmm2
    vmovss -0x4(%rdi,%rbx,4),%xmm7
    vmulss -0x1204(%rdi,%rbx,4),%xmm7,%xmm8
    vmulss %xmm7,%xmm8,%xmm7
    vmulss %xmm4,%xmm4,%xmm4
    vaddss %xmm4,%xmm7,%xmm4
    vmovss -0xc04(%rdi,%rbx,4),%xmm7
    vmovss -0xc00(%rdi,%rbx,4),%xmm8
    vmulss %xmm6,%xmm7,%xmm6
    vmulss %xmm6,%xmm7,%xmm6
    vaddss %xmm6,%xmm4,%xmm4
    vaddss %xmm4,%xmm1,%xmm1
    vaddss -0x1f80(%rdi,%rbx,4),%xmm2,%xmm2
    vmovss (%rdi,%rbx,4),%xmm4
    vmulss -0x1200(%rdi,%rbx,4),%xmm4,%xmm6
")

set_option maxRecDepth 20000 in
/-- asm line 2825 (Gain, straight) -/
def L9731_1 : Program := parse("
    vmulss %xmm6,%xmm4,%xmm4
    vmulss %xmm5,%xmm5,%xmm5
    vaddss %xmm5,%xmm4,%xmm4
    vmulss %xmm3,%xmm8,%xmm3
    vmulss %xmm3,%xmm8,%xmm3
    vaddss %xmm3,%xmm4,%xmm3
    vaddss %xmm3,%xmm1,%xmm1
    add $0x2,%rbx
    cmp %rbx,%r12
    je ff_aac_sbr_apply.L96e1
")

set_option maxRecDepth 20000 in
/-- asm line 2836 (Gain, straight) -/
def L97b7 : Program := parse("
    vmovss -0x604(%rdi,%rbx,4),%xmm4
    vxorps %xmm3,%xmm3,%xmm3
    cmpb $0x0,-0x30(%rbp)
    jne ff_aac_sbr_apply.L97f0
    vxorps %xmm6,%xmm6,%xmm6
    vmovss -0x600(%rdi,%rbx,4),%xmm5
    je ff_aac_sbr_apply.L9731
    jmp ff_aac_sbr_apply.L9720
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2846 (Gain, straight) -/
def L97f0 : Program := parse("
    vcmpeqss %xmm3,%xmm4,%xmm5
    vmovss LCPI14_5(%rip),%xmm6
    vandps %xmm6,%xmm5,%xmm6
    vmovss -0x600(%rdi,%rbx,4),%xmm5
    je ff_aac_sbr_apply.L9731
    jmp ff_aac_sbr_apply.L9720
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2854 (Gain, straight) -/
def L9820 : Program := parse("
    movzwl %si,%eax
    sub %ecx,%eax
    cmp %eax,%r13d
    jae ff_aac_sbr_apply.L9290
    cmp $0x7,%r12
    ja ff_aac_sbr_apply.L9b86
    mov %r13d,%eax
    vmovaps %xmm9,%xmm1
")

set_option maxRecDepth 20000 in
/-- asm line 2863 (Gain, straight) -/
def L983f : Program := parse("
    cmp $0x31,%rax
    mov $0x30,%ebx
    cmovae %rax,%rbx
    cmp $0x2f,%rax
    ja ff_aac_sbr_apply.L9a5a
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2870 (Gain, straight) -/
def L9860 : Program := parse("
    vmulss 0xc00(%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,0xc00(%r8,%rax,4)
")

set_option maxRecDepth 20000 in
/-- asm line 2872 (Gain, straight) -/
def L9860_1 : Program := parse("
    vmulss (%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,(%r8,%rax,4)
")

set_option maxRecDepth 20000 in
/-- asm line 2874 (Gain, straight) -/
def L9860_2 : Program := parse("
    vmulss 0x600(%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,0x600(%r8,%rax,4)
    inc %rax
")

set_option maxRecDepth 20000 in
/-- asm line 2877 (Gain, straight) -/
def L9860_3 : Program := parse("
    mov -0x38(%rbp),%rsi
    movzwl 0x74c12(%rsi,%rdx,2),%esi
    mov %esi,%r14d
    sub %ecx,%r14d
    cmp %r14,%rax
    jae ff_aac_sbr_apply.L9290
    cmp %rax,%rbx
    jne ff_aac_sbr_apply.L9860
    jmp ff_aac_sbr_apply.L9a5a
")

set_option maxRecDepth 20000 in
/-- asm line 2887 (Gain, straight) -/
def L98bc : Program := parse("
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
    cmp %ebx,%r13d
    jae ff_aac_sbr_apply.L9530
    jmp ff_aac_sbr_apply.L9c27
    nop
")

set_option maxRecDepth 20000 in
/-- asm line 2894 (Asm, call_ind) -/
def L98e0 : Program := parse("
    mov 0x7920(%rbx),%eax
    cmp $0x3,%rax
    jae ff_aac_sbr_apply.L9c0e
    imul $0x4c00,%rax,%rax
    lea (%rbx,%rax,1),%rdi
    add $0x7930,%rdi
    mov -0xb8(%rbp),%rsi
    mov -0xb0(%rbp),%rdx
    mov %rbx,%rcx
    mov -0x110(%rbp),%r8
    mov -0x38(%rbp),%rax
    vzeroupper
    call *0x88b78(%rax)
")

set_option maxRecDepth 20000 in
/-- asm line 2908 (Asm, straight) -/
def L9927 : Program := parse("
    mov -0x118(%rbp),%r12
    mov 0x7920(%rbx),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2911 (Asm, straight) -/
def L9934 : Program := parse("
    mov $0x1,%ecx
    sub %eax,%ecx
    cmp $0x3,%ecx
    jae ff_aac_sbr_apply.L9bca
    cmp $0x3,%eax
    mov -0x1a0(%rbp),%r9
    mov -0x48(%rbp),%rdx
    jae ff_aac_sbr_apply.L9bcf
    imul $0x4c00,%r9,%rsi
    add -0xa8(%rbp),%rsi
    add $0x7930,%rdx
    cmpl $0x1,-0x9c(%rbp)
    mov %rdx,%rdi
    sete %bl
    mov %ecx,%ecx
")

set_option maxRecDepth 20000 in
/-- asm line 2926 (Asm, call_ind) -/
def L9934_1 : Program := parse("
    imul $0x4c00,%rcx,%rdx
    add %rdi,%rdx
    mov %eax,%eax
    imul $0x4c00,%rax,%rcx
    add %rdi,%rcx
    mov -0xb0(%rbp),%rdi
    mov -0xc0(%rbp),%r8
    mov -0x38(%rbp),%r14
    call *0x88b80(%r14)
")

set_option maxRecDepth 20000 in
/-- asm line 2935 (Asm, straight) -/
def L9934_2 : Program := parse("
    mov %r14,%r9
    mov $0x1,%edx
    test %bl,-0xf8(%rbp)
    mov $0x0,%ecx
    jne ff_aac_sbr_apply.L7682
    jmp ff_aac_sbr_apply.L9a02
")

set_option maxRecDepth 20000 in
/-- asm line 2942 (Env:B, straight) -/
def L99c6 : Program := parse("
    mov -0x48(%rbp),%rax
    mov 0x8(%rax),%ecx
    mov %ecx,%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2946 (Env:B, straight+ud1) -/
def L99cf : Program := parse("
    cmp $0x9,%ecx
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x48(%rbp),%rbx
    jb ff_aac_sbr_apply.L9146
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2952 (Trap, trap) -/
def L99e9 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2954 (Trap, trap) -/
def L99ee : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2956 (Trap, trap) -/
def L99f3 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2958 (Trap, trap) -/
def L99f8 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2960 (Trap, trap) -/
def L99fd : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2962 (Syn, call_ps) -/
def L9a02 : Program := parse("
    mov -0x90(%rbp),%rbx
    cmpl $0x1,0x5800(%rbx)
    mov -0x150(%rbp),%r14
    jne ff_aac_sbr_apply.L9a85
    lea 0x81060(%r9),%rax
    cmpl $0x0,0x53f20(%r9)
    je ff_aac_sbr_apply.L9a69
    lea 0x53f20(%r9),%rdi
    mov 0x28980(%r9),%ecx
    add 0x28978(%r9),%ecx
    mov -0xa8(%rbp),%rsi
    mov %rax,%rdx
    call ff_ps_apply
")

set_option maxRecDepth 20000 in
/-- asm line 2975 (Syn, straight) -/
def L9a02_1 : Program := parse("
    jmp ff_aac_sbr_apply.L9a7d
")

set_option maxRecDepth 20000 in
/-- asm line 2977 (Trap, trap) -/
def L9a50 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2979 (Trap, trap) -/
def L9a55 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2981 (Trap, trap) -/
def L9a5a : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2983 (Trap, trap) -/
def L9a5f : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2985 (Trap, trap) -/
def L9a64 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 2987 (Syn, call_mem) -/
def L9a69 : Program := parse("
    mov $0x4c00,%edx
    mov %rax,%rdi
    mov -0xa8(%rbp),%rsi
    call memcpy
")

set_option maxRecDepth 20000 in
/-- asm line 2992 (Syn, straight) -/
def L9a7d : Program := parse("
    mov -0x38(%rbp),%r9
    movb $0x1,-0x39(%rbp)
")

set_option maxRecDepth 20000 in
/-- asm line 2995 (Syn, straight) -/
def L9a85 : Program := parse("
    mov 0x88af0(%r9),%rdi
    mov 0x88af8(%r9),%rsi
    mov 0x2550(%rbx),%rcx
    mov %rbx,%r15
    lea 0x28a20(%r9),%rax
    lea 0x2c2a0(%r9),%r10
    mov -0x120(%rbp),%r13
    mov %r13,%rdx
    mov -0x130(%rbp),%r8
    mov %r9,%rbx
    mov -0xa8(%rbp),%r9
    push %r14
    push %r10
    push %rax
    push %r12
")

set_option maxRecDepth 20000 in
/-- asm line 3010 (Syn, call_qmf) -/
def L9a85_1 : Program := parse("
    call sbr_qmf_synthesis
")

set_option maxRecDepth 20000 in
/-- asm line 3011 (Syn, straight) -/
def L9a85_2 : Program := parse("
    add $0x20,%rsp
    cmpb $0x0,-0x39(%rbp)
    je ff_aac_sbr_apply.L9b24
    mov 0x88af0(%rbx),%rdi
    mov 0x88af8(%rbx),%rsi
    mov 0x2550(%r15),%rcx
    lea 0x81060(%rbx),%r9
    lea 0x3e4e0(%rbx),%rax
    add $0x41d60,%rbx
    mov %r13,%rdx
    mov -0x128(%rbp),%r8
    push %r14
    push %rbx
    push %rax
    push %r12
")

set_option maxRecDepth 20000 in
/-- asm line 3026 (Syn, call_qmf) -/
def L9a85_3 : Program := parse("
    call sbr_qmf_synthesis
")

set_option maxRecDepth 20000 in
/-- asm line 3027 (Syn, straight) -/
def L9a85_4 : Program := parse("
    add $0x1b8,%rsp
    jmp ff_aac_sbr_apply.L9b2b
")

set_option maxRecDepth 20000 in
/-- asm line 3030 (Syn, straight) -/
def L9b24 : Program := parse("
    add $0x198,%rsp
")

set_option maxRecDepth 20000 in
/-- asm line 3032 (Syn, straight) -/
def L9b2b : Program := parse("
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
")

set_option maxRecDepth 20000 in
/-- asm line 3038 (Syn, ret) -/
def done : Program := parse("
    ret
")

set_option maxRecDepth 20000 in
/-- asm line 3040 (Trap, trap) -/
def L9b36 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3042 (Trap, trap) -/
def L9b3b : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3044 (Trap, trap) -/
def L9b40 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3046 (Trap, trap) -/
def L9b45 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3048 (Trap, trap) -/
def L9b4a : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3050 (Trap, trap) -/
def L9b4f : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3052 (Trap, trap) -/
def L9b54 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3054 (Trap, trap) -/
def L9b59 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3056 (Trap, trap) -/
def L9b5e : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3058 (Trap, trap) -/
def L9b63 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3060 (Trap, trap) -/
def L9b68 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3062 (Trap, trap) -/
def L9b6d : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3064 (Trap, trap) -/
def L9b72 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3066 (Trap, trap) -/
def L9b77 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3068 (Trap, trap) -/
def L9b7c : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3070 (Trap, trap) -/
def L9b81 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3072 (Trap, trap) -/
def L9b86 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3074 (Trap, trap) -/
def L9b8b : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3076 (Trap, trap) -/
def L9b90 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3078 (Trap, trap) -/
def L9b95 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3080 (Abort, call_avlog) -/
def L9b9a : Program := parse("
    lea L_str_3(%rip),%rdx
    lea L_str_34(%rip),%rcx
    lea L_src_32(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x78,%r9d
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 3088 (Abort, abort) -/
def L9b9a_1 : Program := parse("
    call abort
")

set_option maxRecDepth 20000 in
/-- asm line 3090 (Trap, trap) -/
def L9bc5 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3092 (Trap, trap) -/
def L9bca : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3094 (Trap, trap) -/
def L9bcf : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3096 (Abort, call_avlog) -/
def L9bd4 : Program := parse("
    lea L_str_3(%rip),%rdx
    lea L_str_4(%rip),%rcx
    lea L_str_5(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x6c2,%r9d
    xor %eax,%eax
    call av_log
")

set_option maxRecDepth 20000 in
/-- asm line 3104 (Abort, abort) -/
def L9bd4_1 : Program := parse("
    call abort
")

set_option maxRecDepth 20000 in
/-- asm line 3106 (Trap, trap) -/
def L9bff : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3108 (Trap, trap) -/
def L9c04 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3110 (Trap, trap) -/
def L9c09 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3112 (Trap, trap) -/
def L9c0e : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3114 (Trap, trap) -/
def L9c13 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3116 (Trap, trap) -/
def L9c18 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3118 (Trap, trap) -/
def L9c1d : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3120 (Trap, trap) -/
def L9c22 : Program := parse("
    ud1 0x12(%eax),%eax
")

set_option maxRecDepth 20000 in
/-- asm line 3122 (Trap, trap) -/
def L9c27 : Program := parse("
    ud1 0x12(%eax),%eax
    int3
    int3
    int3
    int3
")

end B

/-- The labels, in order. -/
def labelList : List Label := [
  "ff_aac_sbr_apply",
  "ff_aac_sbr_apply.start_1",
  "ff_aac_sbr_apply.start_2",
  "ff_aac_sbr_apply.start_3",
  "ff_aac_sbr_apply.L676e",
  "ff_aac_sbr_apply.L6797",
  "ff_aac_sbr_apply.L6797_1",
  "ff_aac_sbr_apply.L6817",
  "ff_aac_sbr_apply.L6825",
  "ff_aac_sbr_apply.L6838",
  "ff_aac_sbr_apply.L6838_1",
  "ff_aac_sbr_apply.L6838_2",
  "ff_aac_sbr_apply.L68b0",
  "ff_aac_sbr_apply.L68d0",
  "ff_aac_sbr_apply.L68d0_1",
  "ff_aac_sbr_apply.L68f8",
  "ff_aac_sbr_apply.L6940",
  "ff_aac_sbr_apply.L6940_1",
  "ff_aac_sbr_apply.L69a4",
  "ff_aac_sbr_apply.L69d0",
  "ff_aac_sbr_apply.L69dd",
  "ff_aac_sbr_apply.L6a10",
  "ff_aac_sbr_apply.L6a30",
  "ff_aac_sbr_apply.L6a30_1",
  "ff_aac_sbr_apply.L6a30_2",
  "ff_aac_sbr_apply.L6a90",
  "ff_aac_sbr_apply.L6abf",
  "ff_aac_sbr_apply.L6b00",
  "ff_aac_sbr_apply.L6b02",
  "ff_aac_sbr_apply.L6b12",
  "ff_aac_sbr_apply.L6b50",
  "ff_aac_sbr_apply.L6b6c",
  "ff_aac_sbr_apply.L6ba0",
  "ff_aac_sbr_apply.L6bbc",
  "ff_aac_sbr_apply.L6bbc_1",
  "ff_aac_sbr_apply.L6c1e",
  "ff_aac_sbr_apply.L6c3a",
  "ff_aac_sbr_apply.L6c61",
  "ff_aac_sbr_apply.L6c7d",
  "ff_aac_sbr_apply.L6c7d_1",
  "ff_aac_sbr_apply.L6c7d_2",
  "ff_aac_sbr_apply.L6ce0",
  "ff_aac_sbr_apply.L6cea",
  "ff_aac_sbr_apply.L6d09",
  "ff_aac_sbr_apply.L6d32",
  "ff_aac_sbr_apply.L6d51",
  "ff_aac_sbr_apply.L6d51_1",
  "ff_aac_sbr_apply.L6dbc",
  "ff_aac_sbr_apply.L6ddb",
  "ff_aac_sbr_apply.L6e04",
  "ff_aac_sbr_apply.L6e23",
  "ff_aac_sbr_apply.L6e23_1",
  "ff_aac_sbr_apply.L6e8c",
  "ff_aac_sbr_apply.L6ea8",
  "ff_aac_sbr_apply.L6ecf",
  "ff_aac_sbr_apply.L6eeb",
  "ff_aac_sbr_apply.L6eeb_1",
  "ff_aac_sbr_apply.L6eeb_2",
  "ff_aac_sbr_apply.L6f32",
  "ff_aac_sbr_apply.L6f32_1",
  "ff_aac_sbr_apply.L6f32_2",
  "ff_aac_sbr_apply.L6fbe",
  "ff_aac_sbr_apply.L6fca",
  "ff_aac_sbr_apply.L6ff7",
  "ff_aac_sbr_apply.L6ffc",
  "ff_aac_sbr_apply.L7007",
  "ff_aac_sbr_apply.L700e",
  "ff_aac_sbr_apply.L7020",
  "ff_aac_sbr_apply.L7020_1",
  "ff_aac_sbr_apply.L7020_2",
  "ff_aac_sbr_apply.L7044",
  "ff_aac_sbr_apply.L7044_1",
  "ff_aac_sbr_apply.L7070",
  "ff_aac_sbr_apply.L7090",
  "ff_aac_sbr_apply.L7090_1",
  "ff_aac_sbr_apply.L7090_2",
  "ff_aac_sbr_apply.L70bf",
  "ff_aac_sbr_apply.L70ca",
  "ff_aac_sbr_apply.L70ca_1",
  "ff_aac_sbr_apply.L7120",
  "ff_aac_sbr_apply.L7140",
  "ff_aac_sbr_apply.L7166",
  "ff_aac_sbr_apply.L717f",
  "ff_aac_sbr_apply.L71b0",
  "ff_aac_sbr_apply.L71e0",
  "ff_aac_sbr_apply.L71e0_1",
  "ff_aac_sbr_apply.L7226",
  "ff_aac_sbr_apply.L723c",
  "ff_aac_sbr_apply.L723c_1",
  "ff_aac_sbr_apply.L7270",
  "ff_aac_sbr_apply.L7286",
  "ff_aac_sbr_apply.L7286_1",
  "ff_aac_sbr_apply.L72ba",
  "ff_aac_sbr_apply.L72d0",
  "ff_aac_sbr_apply.L72d0_1",
  "ff_aac_sbr_apply.L7304",
  "ff_aac_sbr_apply.L731a",
  "ff_aac_sbr_apply.L731a_1",
  "ff_aac_sbr_apply.L734a",
  "ff_aac_sbr_apply.L7360",
  "ff_aac_sbr_apply.L7370",
  "ff_aac_sbr_apply.L73a1",
  "ff_aac_sbr_apply.L73b7",
  "ff_aac_sbr_apply.L73b7_1",
  "ff_aac_sbr_apply.L73eb",
  "ff_aac_sbr_apply.L7401",
  "ff_aac_sbr_apply.L7401_1",
  "ff_aac_sbr_apply.L7435",
  "ff_aac_sbr_apply.L744b",
  "ff_aac_sbr_apply.L744b_1",
  "ff_aac_sbr_apply.L747f",
  "ff_aac_sbr_apply.L7495",
  "ff_aac_sbr_apply.L7495_1",
  "ff_aac_sbr_apply.L74de",
  "ff_aac_sbr_apply.L74e9",
  "ff_aac_sbr_apply.L74e9_1",
  "ff_aac_sbr_apply.L74e9_2",
  "ff_aac_sbr_apply.L74e9_3",
  "ff_aac_sbr_apply.L74e9_4",
  "ff_aac_sbr_apply.L7682",
  "ff_aac_sbr_apply.L7682_1",
  "ff_aac_sbr_apply.L7682_2",
  "ff_aac_sbr_apply.L7682_3",
  "ff_aac_sbr_apply.L7682_4",
  "ff_aac_sbr_apply.L7682_5",
  "ff_aac_sbr_apply.L7682_6",
  "ff_aac_sbr_apply.L7682_7",
  "ff_aac_sbr_apply.L7682_8",
  "ff_aac_sbr_apply.L7750",
  "ff_aac_sbr_apply.L7750_1",
  "ff_aac_sbr_apply.L7750_2",
  "ff_aac_sbr_apply.L7750_3",
  "ff_aac_sbr_apply.L7750_4",
  "ff_aac_sbr_apply.L7750_5",
  "ff_aac_sbr_apply.L7750_6",
  "ff_aac_sbr_apply.L7750_7",
  "ff_aac_sbr_apply.L7750_8",
  "ff_aac_sbr_apply.L7866",
  "ff_aac_sbr_apply.L7884",
  "ff_aac_sbr_apply.L7884_1",
  "ff_aac_sbr_apply.L78f2",
  "ff_aac_sbr_apply.L7910",
  "ff_aac_sbr_apply.L7910_1",
  "ff_aac_sbr_apply.L797e",
  "ff_aac_sbr_apply.L799c",
  "ff_aac_sbr_apply.L799c_1",
  "ff_aac_sbr_apply.L7a0a",
  "ff_aac_sbr_apply.L7a28",
  "ff_aac_sbr_apply.L7a28_1",
  "ff_aac_sbr_apply.L7a96",
  "ff_aac_sbr_apply.L7ab4",
  "ff_aac_sbr_apply.L7b00",
  "ff_aac_sbr_apply.L7b00_1",
  "ff_aac_sbr_apply.L7b2d",
  "ff_aac_sbr_apply.L7b50",
  "ff_aac_sbr_apply.L7b80",
  "ff_aac_sbr_apply.L7bb0",
  "ff_aac_sbr_apply.L7bb3",
  "ff_aac_sbr_apply.L7bb3_1",
  "ff_aac_sbr_apply.L7bb3_2",
  "ff_aac_sbr_apply.L7c5d",
  "ff_aac_sbr_apply.L7c80",
  "ff_aac_sbr_apply.L7c80_1",
  "ff_aac_sbr_apply.L7cb0",
  "ff_aac_sbr_apply.L7cbf",
  "ff_aac_sbr_apply.L7ce0",
  "ff_aac_sbr_apply.L7ce4",
  "ff_aac_sbr_apply.L7ce4_1",
  "ff_aac_sbr_apply.L7ce4_2",
  "ff_aac_sbr_apply.L7ce4_3",
  "ff_aac_sbr_apply.L7ce4_4",
  "ff_aac_sbr_apply.L7ce4_5",
  "ff_aac_sbr_apply.L7db0",
  "ff_aac_sbr_apply.L7db0_1",
  "ff_aac_sbr_apply.L7e20",
  "ff_aac_sbr_apply.L7e29",
  "ff_aac_sbr_apply.L7e60",
  "ff_aac_sbr_apply.L7e60_1",
  "ff_aac_sbr_apply.L7e90",
  "ff_aac_sbr_apply.L7e90_1",
  "ff_aac_sbr_apply.L7eb6",
  "ff_aac_sbr_apply.L7eb6_1",
  "ff_aac_sbr_apply.L7f10",
  "ff_aac_sbr_apply.L7f36",
  "ff_aac_sbr_apply.L7f36_1",
  "ff_aac_sbr_apply.L7f80",
  "ff_aac_sbr_apply.L7f80_1",
  "ff_aac_sbr_apply.L8009",
  "ff_aac_sbr_apply.L8050",
  "ff_aac_sbr_apply.L8077",
  "ff_aac_sbr_apply.L8077_1",
  "ff_aac_sbr_apply.L80c0",
  "ff_aac_sbr_apply.L80c0_1",
  "ff_aac_sbr_apply.L814a",
  "ff_aac_sbr_apply.L8190",
  "ff_aac_sbr_apply.L81b7",
  "ff_aac_sbr_apply.L81b7_1",
  "ff_aac_sbr_apply.L8200",
  "ff_aac_sbr_apply.L8200_1",
  "ff_aac_sbr_apply.L828a",
  "ff_aac_sbr_apply.L82d0",
  "ff_aac_sbr_apply.L82f7",
  "ff_aac_sbr_apply.L82f7_1",
  "ff_aac_sbr_apply.L8340",
  "ff_aac_sbr_apply.L8340_1",
  "ff_aac_sbr_apply.L83ca",
  "ff_aac_sbr_apply.L8410",
  "ff_aac_sbr_apply.L8437",
  "ff_aac_sbr_apply.L8437_1",
  "ff_aac_sbr_apply.L8480",
  "ff_aac_sbr_apply.L8480_1",
  "ff_aac_sbr_apply.L8509",
  "ff_aac_sbr_apply.L8520",
  "ff_aac_sbr_apply.L8570",
  "ff_aac_sbr_apply.L8570_1",
  "ff_aac_sbr_apply.L85c0",
  "ff_aac_sbr_apply.L85cd",
  "ff_aac_sbr_apply.L85cd_1",
  "ff_aac_sbr_apply.L85cd_2",
  "ff_aac_sbr_apply.L8620",
  "ff_aac_sbr_apply.L862d",
  "ff_aac_sbr_apply.L862d_1",
  "ff_aac_sbr_apply.L8660",
  "ff_aac_sbr_apply.L86a0",
  "ff_aac_sbr_apply.L86b0",
  "ff_aac_sbr_apply.L86b0_1",
  "ff_aac_sbr_apply.L86d7",
  "ff_aac_sbr_apply.L8700",
  "ff_aac_sbr_apply.L8720",
  "ff_aac_sbr_apply.L8740",
  "ff_aac_sbr_apply.L8740_1",
  "ff_aac_sbr_apply.L8790",
  "ff_aac_sbr_apply.L879e",
  "ff_aac_sbr_apply.L879e_1",
  "ff_aac_sbr_apply.L879e_2",
  "ff_aac_sbr_apply.L8818",
  "ff_aac_sbr_apply.L881c",
  "ff_aac_sbr_apply.L881c_1",
  "ff_aac_sbr_apply.L881c_2",
  "ff_aac_sbr_apply.L881c_3",
  "ff_aac_sbr_apply.L881c_4",
  "ff_aac_sbr_apply.L8900",
  "ff_aac_sbr_apply.L8900_1",
  "ff_aac_sbr_apply.L8900_2",
  "ff_aac_sbr_apply.L8947",
  "ff_aac_sbr_apply.L8947_1",
  "ff_aac_sbr_apply.L8970",
  "ff_aac_sbr_apply.L8970_1",
  "ff_aac_sbr_apply.L89e0",
  "ff_aac_sbr_apply.L89f3",
  "ff_aac_sbr_apply.L89f3_1",
  "ff_aac_sbr_apply.L8a50",
  "ff_aac_sbr_apply.L8a50_1",
  "ff_aac_sbr_apply.L8a50_2",
  "ff_aac_sbr_apply.L8a50_3",
  "ff_aac_sbr_apply.L8ad0",
  "ff_aac_sbr_apply.L8ad0_1",
  "ff_aac_sbr_apply.L8b00",
  "ff_aac_sbr_apply.L8b2a",
  "ff_aac_sbr_apply.L8b4f",
  "ff_aac_sbr_apply.L8b6b",
  "ff_aac_sbr_apply.L8b77",
  "ff_aac_sbr_apply.L8b77_1",
  "ff_aac_sbr_apply.L8b77_2",
  "ff_aac_sbr_apply.L8bf0",
  "ff_aac_sbr_apply.L8bf0_1",
  "ff_aac_sbr_apply.L8bf0_2",
  "ff_aac_sbr_apply.L8c33",
  "ff_aac_sbr_apply.L8c4c",
  "ff_aac_sbr_apply.L8c4c_1",
  "ff_aac_sbr_apply.L8c4c_2",
  "ff_aac_sbr_apply.L8cc9",
  "ff_aac_sbr_apply.L8cc9_1",
  "ff_aac_sbr_apply.L8cc9_2",
  "ff_aac_sbr_apply.L8d0c",
  "ff_aac_sbr_apply.L8d26",
  "ff_aac_sbr_apply.L8d26_1",
  "ff_aac_sbr_apply.L8d26_2",
  "ff_aac_sbr_apply.L8da3",
  "ff_aac_sbr_apply.L8da3_1",
  "ff_aac_sbr_apply.L8da3_2",
  "ff_aac_sbr_apply.L8de6",
  "ff_aac_sbr_apply.L8dff",
  "ff_aac_sbr_apply.L8dff_1",
  "ff_aac_sbr_apply.L8dff_2",
  "ff_aac_sbr_apply.L8e7c",
  "ff_aac_sbr_apply.L8e7c_1",
  "ff_aac_sbr_apply.L8e7c_2",
  "ff_aac_sbr_apply.L8ebf",
  "ff_aac_sbr_apply.L8ed9",
  "ff_aac_sbr_apply.L8ed9_1",
  "ff_aac_sbr_apply.L8ed9_2",
  "ff_aac_sbr_apply.L8f56",
  "ff_aac_sbr_apply.L8f56_1",
  "ff_aac_sbr_apply.L8f56_2",
  "ff_aac_sbr_apply.L8f93",
  "ff_aac_sbr_apply.L8fa4",
  "ff_aac_sbr_apply.L8fa4_1",
  "ff_aac_sbr_apply.L8fa4_2",
  "ff_aac_sbr_apply.L8fa4_3",
  "ff_aac_sbr_apply.L9026",
  "ff_aac_sbr_apply.L9026_1",
  "ff_aac_sbr_apply.L9026_2",
  "ff_aac_sbr_apply.L9063",
  "ff_aac_sbr_apply.L9070",
  "ff_aac_sbr_apply.L907f",
  "ff_aac_sbr_apply.L907f_1",
  "ff_aac_sbr_apply.L907f_2",
  "ff_aac_sbr_apply.L907f_3",
  "ff_aac_sbr_apply.L90f9",
  "ff_aac_sbr_apply.L90f9_1",
  "ff_aac_sbr_apply.L90f9_2",
  "ff_aac_sbr_apply.L913a",
  "ff_aac_sbr_apply.L9146",
  "ff_aac_sbr_apply.L914e",
  "ff_aac_sbr_apply.L914e_1",
  "ff_aac_sbr_apply.L914e_2",
  "ff_aac_sbr_apply.L914e_3",
  "ff_aac_sbr_apply.L91c0",
  "ff_aac_sbr_apply.L91f7",
  "ff_aac_sbr_apply.L9206",
  "ff_aac_sbr_apply.L9215",
  "ff_aac_sbr_apply.L9215_1",
  "ff_aac_sbr_apply.L9215_2",
  "ff_aac_sbr_apply.L9215_3",
  "ff_aac_sbr_apply.L9215_4",
  "ff_aac_sbr_apply.L9215_5",
  "ff_aac_sbr_apply.L9290",
  "ff_aac_sbr_apply.L929e",
  "ff_aac_sbr_apply.L929e_1",
  "ff_aac_sbr_apply.L9300",
  "ff_aac_sbr_apply.L9300_1",
  "ff_aac_sbr_apply.L9300_2",
  "ff_aac_sbr_apply.L9370",
  "ff_aac_sbr_apply.L9386",
  "ff_aac_sbr_apply.L9386_1",
  "ff_aac_sbr_apply.L93d0",
  "ff_aac_sbr_apply.L93f0",
  "ff_aac_sbr_apply.L93f0_1",
  "ff_aac_sbr_apply.L9440",
  "ff_aac_sbr_apply.L9458",
  "ff_aac_sbr_apply.L9470",
  "ff_aac_sbr_apply.L9470_1",
  "ff_aac_sbr_apply.L9504",
  "ff_aac_sbr_apply.L9520",
  "ff_aac_sbr_apply.L952c",
  "ff_aac_sbr_apply.L9530",
  "ff_aac_sbr_apply.L9530_1",
  "ff_aac_sbr_apply.L95a0",
  "ff_aac_sbr_apply.L95a0_1",
  "ff_aac_sbr_apply.L95a0_2",
  "ff_aac_sbr_apply.L9600",
  "ff_aac_sbr_apply.L9617",
  "ff_aac_sbr_apply.L9617_1",
  "ff_aac_sbr_apply.L968d",
  "ff_aac_sbr_apply.L96d3",
  "ff_aac_sbr_apply.L96e1",
  "ff_aac_sbr_apply.L9720",
  "ff_aac_sbr_apply.L9731",
  "ff_aac_sbr_apply.L9731_1",
  "ff_aac_sbr_apply.L97b7",
  "ff_aac_sbr_apply.L97f0",
  "ff_aac_sbr_apply.L9820",
  "ff_aac_sbr_apply.L983f",
  "ff_aac_sbr_apply.L9860",
  "ff_aac_sbr_apply.L9860_1",
  "ff_aac_sbr_apply.L9860_2",
  "ff_aac_sbr_apply.L9860_3",
  "ff_aac_sbr_apply.L98bc",
  "ff_aac_sbr_apply.L98e0",
  "ff_aac_sbr_apply.L9927",
  "ff_aac_sbr_apply.L9934",
  "ff_aac_sbr_apply.L9934_1",
  "ff_aac_sbr_apply.L9934_2",
  "ff_aac_sbr_apply.L99c6",
  "ff_aac_sbr_apply.L99cf",
  "ff_aac_sbr_apply.L99e9",
  "ff_aac_sbr_apply.L99ee",
  "ff_aac_sbr_apply.L99f3",
  "ff_aac_sbr_apply.L99f8",
  "ff_aac_sbr_apply.L99fd",
  "ff_aac_sbr_apply.L9a02",
  "ff_aac_sbr_apply.L9a02_1",
  "ff_aac_sbr_apply.L9a50",
  "ff_aac_sbr_apply.L9a55",
  "ff_aac_sbr_apply.L9a5a",
  "ff_aac_sbr_apply.L9a5f",
  "ff_aac_sbr_apply.L9a64",
  "ff_aac_sbr_apply.L9a69",
  "ff_aac_sbr_apply.L9a7d",
  "ff_aac_sbr_apply.L9a85",
  "ff_aac_sbr_apply.L9a85_1",
  "ff_aac_sbr_apply.L9a85_2",
  "ff_aac_sbr_apply.L9a85_3",
  "ff_aac_sbr_apply.L9a85_4",
  "ff_aac_sbr_apply.L9b24",
  "ff_aac_sbr_apply.L9b2b",
  "ff_aac_sbr_apply.done",
  "ff_aac_sbr_apply.L9b36",
  "ff_aac_sbr_apply.L9b3b",
  "ff_aac_sbr_apply.L9b40",
  "ff_aac_sbr_apply.L9b45",
  "ff_aac_sbr_apply.L9b4a",
  "ff_aac_sbr_apply.L9b4f",
  "ff_aac_sbr_apply.L9b54",
  "ff_aac_sbr_apply.L9b59",
  "ff_aac_sbr_apply.L9b5e",
  "ff_aac_sbr_apply.L9b63",
  "ff_aac_sbr_apply.L9b68",
  "ff_aac_sbr_apply.L9b6d",
  "ff_aac_sbr_apply.L9b72",
  "ff_aac_sbr_apply.L9b77",
  "ff_aac_sbr_apply.L9b7c",
  "ff_aac_sbr_apply.L9b81",
  "ff_aac_sbr_apply.L9b86",
  "ff_aac_sbr_apply.L9b8b",
  "ff_aac_sbr_apply.L9b90",
  "ff_aac_sbr_apply.L9b95",
  "ff_aac_sbr_apply.L9b9a",
  "ff_aac_sbr_apply.L9b9a_1",
  "ff_aac_sbr_apply.L9bc5",
  "ff_aac_sbr_apply.L9bca",
  "ff_aac_sbr_apply.L9bcf",
  "ff_aac_sbr_apply.L9bd4",
  "ff_aac_sbr_apply.L9bd4_1",
  "ff_aac_sbr_apply.L9bff",
  "ff_aac_sbr_apply.L9c04",
  "ff_aac_sbr_apply.L9c09",
  "ff_aac_sbr_apply.L9c0e",
  "ff_aac_sbr_apply.L9c13",
  "ff_aac_sbr_apply.L9c18",
  "ff_aac_sbr_apply.L9c1d",
  "ff_aac_sbr_apply.L9c22",
  "ff_aac_sbr_apply.L9c27"]

/-- The blocks, in order. -/
def blocks : List (Label × Program) := [
  ("ff_aac_sbr_apply", B.start),
  ("ff_aac_sbr_apply.start_1", B.start_1),
  ("ff_aac_sbr_apply.start_2", B.start_2),
  ("ff_aac_sbr_apply.start_3", B.start_3),
  ("ff_aac_sbr_apply.L676e", B.L676e),
  ("ff_aac_sbr_apply.L6797", B.L6797),
  ("ff_aac_sbr_apply.L6797_1", B.L6797_1),
  ("ff_aac_sbr_apply.L6817", B.L6817),
  ("ff_aac_sbr_apply.L6825", B.L6825),
  ("ff_aac_sbr_apply.L6838", B.L6838),
  ("ff_aac_sbr_apply.L6838_1", B.L6838_1),
  ("ff_aac_sbr_apply.L6838_2", B.L6838_2),
  ("ff_aac_sbr_apply.L68b0", B.L68b0),
  ("ff_aac_sbr_apply.L68d0", B.L68d0),
  ("ff_aac_sbr_apply.L68d0_1", B.L68d0_1),
  ("ff_aac_sbr_apply.L68f8", B.L68f8),
  ("ff_aac_sbr_apply.L6940", B.L6940),
  ("ff_aac_sbr_apply.L6940_1", B.L6940_1),
  ("ff_aac_sbr_apply.L69a4", B.L69a4),
  ("ff_aac_sbr_apply.L69d0", B.L69d0),
  ("ff_aac_sbr_apply.L69dd", B.L69dd),
  ("ff_aac_sbr_apply.L6a10", B.L6a10),
  ("ff_aac_sbr_apply.L6a30", B.L6a30),
  ("ff_aac_sbr_apply.L6a30_1", B.L6a30_1),
  ("ff_aac_sbr_apply.L6a30_2", B.L6a30_2),
  ("ff_aac_sbr_apply.L6a90", B.L6a90),
  ("ff_aac_sbr_apply.L6abf", B.L6abf),
  ("ff_aac_sbr_apply.L6b00", B.L6b00),
  ("ff_aac_sbr_apply.L6b02", B.L6b02),
  ("ff_aac_sbr_apply.L6b12", B.L6b12),
  ("ff_aac_sbr_apply.L6b50", B.L6b50),
  ("ff_aac_sbr_apply.L6b6c", B.L6b6c),
  ("ff_aac_sbr_apply.L6ba0", B.L6ba0),
  ("ff_aac_sbr_apply.L6bbc", B.L6bbc),
  ("ff_aac_sbr_apply.L6bbc_1", B.L6bbc_1),
  ("ff_aac_sbr_apply.L6c1e", B.L6c1e),
  ("ff_aac_sbr_apply.L6c3a", B.L6c3a),
  ("ff_aac_sbr_apply.L6c61", B.L6c61),
  ("ff_aac_sbr_apply.L6c7d", B.L6c7d),
  ("ff_aac_sbr_apply.L6c7d_1", B.L6c7d_1),
  ("ff_aac_sbr_apply.L6c7d_2", B.L6c7d_2),
  ("ff_aac_sbr_apply.L6ce0", B.L6ce0),
  ("ff_aac_sbr_apply.L6cea", B.L6cea),
  ("ff_aac_sbr_apply.L6d09", B.L6d09),
  ("ff_aac_sbr_apply.L6d32", B.L6d32),
  ("ff_aac_sbr_apply.L6d51", B.L6d51),
  ("ff_aac_sbr_apply.L6d51_1", B.L6d51_1),
  ("ff_aac_sbr_apply.L6dbc", B.L6dbc),
  ("ff_aac_sbr_apply.L6ddb", B.L6ddb),
  ("ff_aac_sbr_apply.L6e04", B.L6e04),
  ("ff_aac_sbr_apply.L6e23", B.L6e23),
  ("ff_aac_sbr_apply.L6e23_1", B.L6e23_1),
  ("ff_aac_sbr_apply.L6e8c", B.L6e8c),
  ("ff_aac_sbr_apply.L6ea8", B.L6ea8),
  ("ff_aac_sbr_apply.L6ecf", B.L6ecf),
  ("ff_aac_sbr_apply.L6eeb", B.L6eeb),
  ("ff_aac_sbr_apply.L6eeb_1", B.L6eeb_1),
  ("ff_aac_sbr_apply.L6eeb_2", B.L6eeb_2),
  ("ff_aac_sbr_apply.L6f32", B.L6f32),
  ("ff_aac_sbr_apply.L6f32_1", B.L6f32_1),
  ("ff_aac_sbr_apply.L6f32_2", B.L6f32_2),
  ("ff_aac_sbr_apply.L6fbe", B.L6fbe),
  ("ff_aac_sbr_apply.L6fca", B.L6fca),
  ("ff_aac_sbr_apply.L6ff7", B.L6ff7),
  ("ff_aac_sbr_apply.L6ffc", B.L6ffc),
  ("ff_aac_sbr_apply.L7007", B.L7007),
  ("ff_aac_sbr_apply.L700e", B.L700e),
  ("ff_aac_sbr_apply.L7020", B.L7020),
  ("ff_aac_sbr_apply.L7020_1", B.L7020_1),
  ("ff_aac_sbr_apply.L7020_2", B.L7020_2),
  ("ff_aac_sbr_apply.L7044", B.L7044),
  ("ff_aac_sbr_apply.L7044_1", B.L7044_1),
  ("ff_aac_sbr_apply.L7070", B.L7070),
  ("ff_aac_sbr_apply.L7090", B.L7090),
  ("ff_aac_sbr_apply.L7090_1", B.L7090_1),
  ("ff_aac_sbr_apply.L7090_2", B.L7090_2),
  ("ff_aac_sbr_apply.L70bf", B.L70bf),
  ("ff_aac_sbr_apply.L70ca", B.L70ca),
  ("ff_aac_sbr_apply.L70ca_1", B.L70ca_1),
  ("ff_aac_sbr_apply.L7120", B.L7120),
  ("ff_aac_sbr_apply.L7140", B.L7140),
  ("ff_aac_sbr_apply.L7166", B.L7166),
  ("ff_aac_sbr_apply.L717f", B.L717f),
  ("ff_aac_sbr_apply.L71b0", B.L71b0),
  ("ff_aac_sbr_apply.L71e0", B.L71e0),
  ("ff_aac_sbr_apply.L71e0_1", B.L71e0_1),
  ("ff_aac_sbr_apply.L7226", B.L7226),
  ("ff_aac_sbr_apply.L723c", B.L723c),
  ("ff_aac_sbr_apply.L723c_1", B.L723c_1),
  ("ff_aac_sbr_apply.L7270", B.L7270),
  ("ff_aac_sbr_apply.L7286", B.L7286),
  ("ff_aac_sbr_apply.L7286_1", B.L7286_1),
  ("ff_aac_sbr_apply.L72ba", B.L72ba),
  ("ff_aac_sbr_apply.L72d0", B.L72d0),
  ("ff_aac_sbr_apply.L72d0_1", B.L72d0_1),
  ("ff_aac_sbr_apply.L7304", B.L7304),
  ("ff_aac_sbr_apply.L731a", B.L731a),
  ("ff_aac_sbr_apply.L731a_1", B.L731a_1),
  ("ff_aac_sbr_apply.L734a", B.L734a),
  ("ff_aac_sbr_apply.L7360", B.L7360),
  ("ff_aac_sbr_apply.L7370", B.L7370),
  ("ff_aac_sbr_apply.L73a1", B.L73a1),
  ("ff_aac_sbr_apply.L73b7", B.L73b7),
  ("ff_aac_sbr_apply.L73b7_1", B.L73b7_1),
  ("ff_aac_sbr_apply.L73eb", B.L73eb),
  ("ff_aac_sbr_apply.L7401", B.L7401),
  ("ff_aac_sbr_apply.L7401_1", B.L7401_1),
  ("ff_aac_sbr_apply.L7435", B.L7435),
  ("ff_aac_sbr_apply.L744b", B.L744b),
  ("ff_aac_sbr_apply.L744b_1", B.L744b_1),
  ("ff_aac_sbr_apply.L747f", B.L747f),
  ("ff_aac_sbr_apply.L7495", B.L7495),
  ("ff_aac_sbr_apply.L7495_1", B.L7495_1),
  ("ff_aac_sbr_apply.L74de", B.L74de),
  ("ff_aac_sbr_apply.L74e9", B.L74e9),
  ("ff_aac_sbr_apply.L74e9_1", B.L74e9_1),
  ("ff_aac_sbr_apply.L74e9_2", B.L74e9_2),
  ("ff_aac_sbr_apply.L74e9_3", B.L74e9_3),
  ("ff_aac_sbr_apply.L74e9_4", B.L74e9_4),
  ("ff_aac_sbr_apply.L7682", B.L7682),
  ("ff_aac_sbr_apply.L7682_1", B.L7682_1),
  ("ff_aac_sbr_apply.L7682_2", B.L7682_2),
  ("ff_aac_sbr_apply.L7682_3", B.L7682_3),
  ("ff_aac_sbr_apply.L7682_4", B.L7682_4),
  ("ff_aac_sbr_apply.L7682_5", B.L7682_5),
  ("ff_aac_sbr_apply.L7682_6", B.L7682_6),
  ("ff_aac_sbr_apply.L7682_7", B.L7682_7),
  ("ff_aac_sbr_apply.L7682_8", B.L7682_8),
  ("ff_aac_sbr_apply.L7750", B.L7750),
  ("ff_aac_sbr_apply.L7750_1", B.L7750_1),
  ("ff_aac_sbr_apply.L7750_2", B.L7750_2),
  ("ff_aac_sbr_apply.L7750_3", B.L7750_3),
  ("ff_aac_sbr_apply.L7750_4", B.L7750_4),
  ("ff_aac_sbr_apply.L7750_5", B.L7750_5),
  ("ff_aac_sbr_apply.L7750_6", B.L7750_6),
  ("ff_aac_sbr_apply.L7750_7", B.L7750_7),
  ("ff_aac_sbr_apply.L7750_8", B.L7750_8),
  ("ff_aac_sbr_apply.L7866", B.L7866),
  ("ff_aac_sbr_apply.L7884", B.L7884),
  ("ff_aac_sbr_apply.L7884_1", B.L7884_1),
  ("ff_aac_sbr_apply.L78f2", B.L78f2),
  ("ff_aac_sbr_apply.L7910", B.L7910),
  ("ff_aac_sbr_apply.L7910_1", B.L7910_1),
  ("ff_aac_sbr_apply.L797e", B.L797e),
  ("ff_aac_sbr_apply.L799c", B.L799c),
  ("ff_aac_sbr_apply.L799c_1", B.L799c_1),
  ("ff_aac_sbr_apply.L7a0a", B.L7a0a),
  ("ff_aac_sbr_apply.L7a28", B.L7a28),
  ("ff_aac_sbr_apply.L7a28_1", B.L7a28_1),
  ("ff_aac_sbr_apply.L7a96", B.L7a96),
  ("ff_aac_sbr_apply.L7ab4", B.L7ab4),
  ("ff_aac_sbr_apply.L7b00", B.L7b00),
  ("ff_aac_sbr_apply.L7b00_1", B.L7b00_1),
  ("ff_aac_sbr_apply.L7b2d", B.L7b2d),
  ("ff_aac_sbr_apply.L7b50", B.L7b50),
  ("ff_aac_sbr_apply.L7b80", B.L7b80),
  ("ff_aac_sbr_apply.L7bb0", B.L7bb0),
  ("ff_aac_sbr_apply.L7bb3", B.L7bb3),
  ("ff_aac_sbr_apply.L7bb3_1", B.L7bb3_1),
  ("ff_aac_sbr_apply.L7bb3_2", B.L7bb3_2),
  ("ff_aac_sbr_apply.L7c5d", B.L7c5d),
  ("ff_aac_sbr_apply.L7c80", B.L7c80),
  ("ff_aac_sbr_apply.L7c80_1", B.L7c80_1),
  ("ff_aac_sbr_apply.L7cb0", B.L7cb0),
  ("ff_aac_sbr_apply.L7cbf", B.L7cbf),
  ("ff_aac_sbr_apply.L7ce0", B.L7ce0),
  ("ff_aac_sbr_apply.L7ce4", B.L7ce4),
  ("ff_aac_sbr_apply.L7ce4_1", B.L7ce4_1),
  ("ff_aac_sbr_apply.L7ce4_2", B.L7ce4_2),
  ("ff_aac_sbr_apply.L7ce4_3", B.L7ce4_3),
  ("ff_aac_sbr_apply.L7ce4_4", B.L7ce4_4),
  ("ff_aac_sbr_apply.L7ce4_5", B.L7ce4_5),
  ("ff_aac_sbr_apply.L7db0", B.L7db0),
  ("ff_aac_sbr_apply.L7db0_1", B.L7db0_1),
  ("ff_aac_sbr_apply.L7e20", B.L7e20),
  ("ff_aac_sbr_apply.L7e29", B.L7e29),
  ("ff_aac_sbr_apply.L7e60", B.L7e60),
  ("ff_aac_sbr_apply.L7e60_1", B.L7e60_1),
  ("ff_aac_sbr_apply.L7e90", B.L7e90),
  ("ff_aac_sbr_apply.L7e90_1", B.L7e90_1),
  ("ff_aac_sbr_apply.L7eb6", B.L7eb6),
  ("ff_aac_sbr_apply.L7eb6_1", B.L7eb6_1),
  ("ff_aac_sbr_apply.L7f10", B.L7f10),
  ("ff_aac_sbr_apply.L7f36", B.L7f36),
  ("ff_aac_sbr_apply.L7f36_1", B.L7f36_1),
  ("ff_aac_sbr_apply.L7f80", B.L7f80),
  ("ff_aac_sbr_apply.L7f80_1", B.L7f80_1),
  ("ff_aac_sbr_apply.L8009", B.L8009),
  ("ff_aac_sbr_apply.L8050", B.L8050),
  ("ff_aac_sbr_apply.L8077", B.L8077),
  ("ff_aac_sbr_apply.L8077_1", B.L8077_1),
  ("ff_aac_sbr_apply.L80c0", B.L80c0),
  ("ff_aac_sbr_apply.L80c0_1", B.L80c0_1),
  ("ff_aac_sbr_apply.L814a", B.L814a),
  ("ff_aac_sbr_apply.L8190", B.L8190),
  ("ff_aac_sbr_apply.L81b7", B.L81b7),
  ("ff_aac_sbr_apply.L81b7_1", B.L81b7_1),
  ("ff_aac_sbr_apply.L8200", B.L8200),
  ("ff_aac_sbr_apply.L8200_1", B.L8200_1),
  ("ff_aac_sbr_apply.L828a", B.L828a),
  ("ff_aac_sbr_apply.L82d0", B.L82d0),
  ("ff_aac_sbr_apply.L82f7", B.L82f7),
  ("ff_aac_sbr_apply.L82f7_1", B.L82f7_1),
  ("ff_aac_sbr_apply.L8340", B.L8340),
  ("ff_aac_sbr_apply.L8340_1", B.L8340_1),
  ("ff_aac_sbr_apply.L83ca", B.L83ca),
  ("ff_aac_sbr_apply.L8410", B.L8410),
  ("ff_aac_sbr_apply.L8437", B.L8437),
  ("ff_aac_sbr_apply.L8437_1", B.L8437_1),
  ("ff_aac_sbr_apply.L8480", B.L8480),
  ("ff_aac_sbr_apply.L8480_1", B.L8480_1),
  ("ff_aac_sbr_apply.L8509", B.L8509),
  ("ff_aac_sbr_apply.L8520", B.L8520),
  ("ff_aac_sbr_apply.L8570", B.L8570),
  ("ff_aac_sbr_apply.L8570_1", B.L8570_1),
  ("ff_aac_sbr_apply.L85c0", B.L85c0),
  ("ff_aac_sbr_apply.L85cd", B.L85cd),
  ("ff_aac_sbr_apply.L85cd_1", B.L85cd_1),
  ("ff_aac_sbr_apply.L85cd_2", B.L85cd_2),
  ("ff_aac_sbr_apply.L8620", B.L8620),
  ("ff_aac_sbr_apply.L862d", B.L862d),
  ("ff_aac_sbr_apply.L862d_1", B.L862d_1),
  ("ff_aac_sbr_apply.L8660", B.L8660),
  ("ff_aac_sbr_apply.L86a0", B.L86a0),
  ("ff_aac_sbr_apply.L86b0", B.L86b0),
  ("ff_aac_sbr_apply.L86b0_1", B.L86b0_1),
  ("ff_aac_sbr_apply.L86d7", B.L86d7),
  ("ff_aac_sbr_apply.L8700", B.L8700),
  ("ff_aac_sbr_apply.L8720", B.L8720),
  ("ff_aac_sbr_apply.L8740", B.L8740),
  ("ff_aac_sbr_apply.L8740_1", B.L8740_1),
  ("ff_aac_sbr_apply.L8790", B.L8790),
  ("ff_aac_sbr_apply.L879e", B.L879e),
  ("ff_aac_sbr_apply.L879e_1", B.L879e_1),
  ("ff_aac_sbr_apply.L879e_2", B.L879e_2),
  ("ff_aac_sbr_apply.L8818", B.L8818),
  ("ff_aac_sbr_apply.L881c", B.L881c),
  ("ff_aac_sbr_apply.L881c_1", B.L881c_1),
  ("ff_aac_sbr_apply.L881c_2", B.L881c_2),
  ("ff_aac_sbr_apply.L881c_3", B.L881c_3),
  ("ff_aac_sbr_apply.L881c_4", B.L881c_4),
  ("ff_aac_sbr_apply.L8900", B.L8900),
  ("ff_aac_sbr_apply.L8900_1", B.L8900_1),
  ("ff_aac_sbr_apply.L8900_2", B.L8900_2),
  ("ff_aac_sbr_apply.L8947", B.L8947),
  ("ff_aac_sbr_apply.L8947_1", B.L8947_1),
  ("ff_aac_sbr_apply.L8970", B.L8970),
  ("ff_aac_sbr_apply.L8970_1", B.L8970_1),
  ("ff_aac_sbr_apply.L89e0", B.L89e0),
  ("ff_aac_sbr_apply.L89f3", B.L89f3),
  ("ff_aac_sbr_apply.L89f3_1", B.L89f3_1),
  ("ff_aac_sbr_apply.L8a50", B.L8a50),
  ("ff_aac_sbr_apply.L8a50_1", B.L8a50_1),
  ("ff_aac_sbr_apply.L8a50_2", B.L8a50_2),
  ("ff_aac_sbr_apply.L8a50_3", B.L8a50_3),
  ("ff_aac_sbr_apply.L8ad0", B.L8ad0),
  ("ff_aac_sbr_apply.L8ad0_1", B.L8ad0_1),
  ("ff_aac_sbr_apply.L8b00", B.L8b00),
  ("ff_aac_sbr_apply.L8b2a", B.L8b2a),
  ("ff_aac_sbr_apply.L8b4f", B.L8b4f),
  ("ff_aac_sbr_apply.L8b6b", B.L8b6b),
  ("ff_aac_sbr_apply.L8b77", B.L8b77),
  ("ff_aac_sbr_apply.L8b77_1", B.L8b77_1),
  ("ff_aac_sbr_apply.L8b77_2", B.L8b77_2),
  ("ff_aac_sbr_apply.L8bf0", B.L8bf0),
  ("ff_aac_sbr_apply.L8bf0_1", B.L8bf0_1),
  ("ff_aac_sbr_apply.L8bf0_2", B.L8bf0_2),
  ("ff_aac_sbr_apply.L8c33", B.L8c33),
  ("ff_aac_sbr_apply.L8c4c", B.L8c4c),
  ("ff_aac_sbr_apply.L8c4c_1", B.L8c4c_1),
  ("ff_aac_sbr_apply.L8c4c_2", B.L8c4c_2),
  ("ff_aac_sbr_apply.L8cc9", B.L8cc9),
  ("ff_aac_sbr_apply.L8cc9_1", B.L8cc9_1),
  ("ff_aac_sbr_apply.L8cc9_2", B.L8cc9_2),
  ("ff_aac_sbr_apply.L8d0c", B.L8d0c),
  ("ff_aac_sbr_apply.L8d26", B.L8d26),
  ("ff_aac_sbr_apply.L8d26_1", B.L8d26_1),
  ("ff_aac_sbr_apply.L8d26_2", B.L8d26_2),
  ("ff_aac_sbr_apply.L8da3", B.L8da3),
  ("ff_aac_sbr_apply.L8da3_1", B.L8da3_1),
  ("ff_aac_sbr_apply.L8da3_2", B.L8da3_2),
  ("ff_aac_sbr_apply.L8de6", B.L8de6),
  ("ff_aac_sbr_apply.L8dff", B.L8dff),
  ("ff_aac_sbr_apply.L8dff_1", B.L8dff_1),
  ("ff_aac_sbr_apply.L8dff_2", B.L8dff_2),
  ("ff_aac_sbr_apply.L8e7c", B.L8e7c),
  ("ff_aac_sbr_apply.L8e7c_1", B.L8e7c_1),
  ("ff_aac_sbr_apply.L8e7c_2", B.L8e7c_2),
  ("ff_aac_sbr_apply.L8ebf", B.L8ebf),
  ("ff_aac_sbr_apply.L8ed9", B.L8ed9),
  ("ff_aac_sbr_apply.L8ed9_1", B.L8ed9_1),
  ("ff_aac_sbr_apply.L8ed9_2", B.L8ed9_2),
  ("ff_aac_sbr_apply.L8f56", B.L8f56),
  ("ff_aac_sbr_apply.L8f56_1", B.L8f56_1),
  ("ff_aac_sbr_apply.L8f56_2", B.L8f56_2),
  ("ff_aac_sbr_apply.L8f93", B.L8f93),
  ("ff_aac_sbr_apply.L8fa4", B.L8fa4),
  ("ff_aac_sbr_apply.L8fa4_1", B.L8fa4_1),
  ("ff_aac_sbr_apply.L8fa4_2", B.L8fa4_2),
  ("ff_aac_sbr_apply.L8fa4_3", B.L8fa4_3),
  ("ff_aac_sbr_apply.L9026", B.L9026),
  ("ff_aac_sbr_apply.L9026_1", B.L9026_1),
  ("ff_aac_sbr_apply.L9026_2", B.L9026_2),
  ("ff_aac_sbr_apply.L9063", B.L9063),
  ("ff_aac_sbr_apply.L9070", B.L9070),
  ("ff_aac_sbr_apply.L907f", B.L907f),
  ("ff_aac_sbr_apply.L907f_1", B.L907f_1),
  ("ff_aac_sbr_apply.L907f_2", B.L907f_2),
  ("ff_aac_sbr_apply.L907f_3", B.L907f_3),
  ("ff_aac_sbr_apply.L90f9", B.L90f9),
  ("ff_aac_sbr_apply.L90f9_1", B.L90f9_1),
  ("ff_aac_sbr_apply.L90f9_2", B.L90f9_2),
  ("ff_aac_sbr_apply.L913a", B.L913a),
  ("ff_aac_sbr_apply.L9146", B.L9146),
  ("ff_aac_sbr_apply.L914e", B.L914e),
  ("ff_aac_sbr_apply.L914e_1", B.L914e_1),
  ("ff_aac_sbr_apply.L914e_2", B.L914e_2),
  ("ff_aac_sbr_apply.L914e_3", B.L914e_3),
  ("ff_aac_sbr_apply.L91c0", B.L91c0),
  ("ff_aac_sbr_apply.L91f7", B.L91f7),
  ("ff_aac_sbr_apply.L9206", B.L9206),
  ("ff_aac_sbr_apply.L9215", B.L9215),
  ("ff_aac_sbr_apply.L9215_1", B.L9215_1),
  ("ff_aac_sbr_apply.L9215_2", B.L9215_2),
  ("ff_aac_sbr_apply.L9215_3", B.L9215_3),
  ("ff_aac_sbr_apply.L9215_4", B.L9215_4),
  ("ff_aac_sbr_apply.L9215_5", B.L9215_5),
  ("ff_aac_sbr_apply.L9290", B.L9290),
  ("ff_aac_sbr_apply.L929e", B.L929e),
  ("ff_aac_sbr_apply.L929e_1", B.L929e_1),
  ("ff_aac_sbr_apply.L9300", B.L9300),
  ("ff_aac_sbr_apply.L9300_1", B.L9300_1),
  ("ff_aac_sbr_apply.L9300_2", B.L9300_2),
  ("ff_aac_sbr_apply.L9370", B.L9370),
  ("ff_aac_sbr_apply.L9386", B.L9386),
  ("ff_aac_sbr_apply.L9386_1", B.L9386_1),
  ("ff_aac_sbr_apply.L93d0", B.L93d0),
  ("ff_aac_sbr_apply.L93f0", B.L93f0),
  ("ff_aac_sbr_apply.L93f0_1", B.L93f0_1),
  ("ff_aac_sbr_apply.L9440", B.L9440),
  ("ff_aac_sbr_apply.L9458", B.L9458),
  ("ff_aac_sbr_apply.L9470", B.L9470),
  ("ff_aac_sbr_apply.L9470_1", B.L9470_1),
  ("ff_aac_sbr_apply.L9504", B.L9504),
  ("ff_aac_sbr_apply.L9520", B.L9520),
  ("ff_aac_sbr_apply.L952c", B.L952c),
  ("ff_aac_sbr_apply.L9530", B.L9530),
  ("ff_aac_sbr_apply.L9530_1", B.L9530_1),
  ("ff_aac_sbr_apply.L95a0", B.L95a0),
  ("ff_aac_sbr_apply.L95a0_1", B.L95a0_1),
  ("ff_aac_sbr_apply.L95a0_2", B.L95a0_2),
  ("ff_aac_sbr_apply.L9600", B.L9600),
  ("ff_aac_sbr_apply.L9617", B.L9617),
  ("ff_aac_sbr_apply.L9617_1", B.L9617_1),
  ("ff_aac_sbr_apply.L968d", B.L968d),
  ("ff_aac_sbr_apply.L96d3", B.L96d3),
  ("ff_aac_sbr_apply.L96e1", B.L96e1),
  ("ff_aac_sbr_apply.L9720", B.L9720),
  ("ff_aac_sbr_apply.L9731", B.L9731),
  ("ff_aac_sbr_apply.L9731_1", B.L9731_1),
  ("ff_aac_sbr_apply.L97b7", B.L97b7),
  ("ff_aac_sbr_apply.L97f0", B.L97f0),
  ("ff_aac_sbr_apply.L9820", B.L9820),
  ("ff_aac_sbr_apply.L983f", B.L983f),
  ("ff_aac_sbr_apply.L9860", B.L9860),
  ("ff_aac_sbr_apply.L9860_1", B.L9860_1),
  ("ff_aac_sbr_apply.L9860_2", B.L9860_2),
  ("ff_aac_sbr_apply.L9860_3", B.L9860_3),
  ("ff_aac_sbr_apply.L98bc", B.L98bc),
  ("ff_aac_sbr_apply.L98e0", B.L98e0),
  ("ff_aac_sbr_apply.L9927", B.L9927),
  ("ff_aac_sbr_apply.L9934", B.L9934),
  ("ff_aac_sbr_apply.L9934_1", B.L9934_1),
  ("ff_aac_sbr_apply.L9934_2", B.L9934_2),
  ("ff_aac_sbr_apply.L99c6", B.L99c6),
  ("ff_aac_sbr_apply.L99cf", B.L99cf),
  ("ff_aac_sbr_apply.L99e9", B.L99e9),
  ("ff_aac_sbr_apply.L99ee", B.L99ee),
  ("ff_aac_sbr_apply.L99f3", B.L99f3),
  ("ff_aac_sbr_apply.L99f8", B.L99f8),
  ("ff_aac_sbr_apply.L99fd", B.L99fd),
  ("ff_aac_sbr_apply.L9a02", B.L9a02),
  ("ff_aac_sbr_apply.L9a02_1", B.L9a02_1),
  ("ff_aac_sbr_apply.L9a50", B.L9a50),
  ("ff_aac_sbr_apply.L9a55", B.L9a55),
  ("ff_aac_sbr_apply.L9a5a", B.L9a5a),
  ("ff_aac_sbr_apply.L9a5f", B.L9a5f),
  ("ff_aac_sbr_apply.L9a64", B.L9a64),
  ("ff_aac_sbr_apply.L9a69", B.L9a69),
  ("ff_aac_sbr_apply.L9a7d", B.L9a7d),
  ("ff_aac_sbr_apply.L9a85", B.L9a85),
  ("ff_aac_sbr_apply.L9a85_1", B.L9a85_1),
  ("ff_aac_sbr_apply.L9a85_2", B.L9a85_2),
  ("ff_aac_sbr_apply.L9a85_3", B.L9a85_3),
  ("ff_aac_sbr_apply.L9a85_4", B.L9a85_4),
  ("ff_aac_sbr_apply.L9b24", B.L9b24),
  ("ff_aac_sbr_apply.L9b2b", B.L9b2b),
  ("ff_aac_sbr_apply.done", B.done),
  ("ff_aac_sbr_apply.L9b36", B.L9b36),
  ("ff_aac_sbr_apply.L9b3b", B.L9b3b),
  ("ff_aac_sbr_apply.L9b40", B.L9b40),
  ("ff_aac_sbr_apply.L9b45", B.L9b45),
  ("ff_aac_sbr_apply.L9b4a", B.L9b4a),
  ("ff_aac_sbr_apply.L9b4f", B.L9b4f),
  ("ff_aac_sbr_apply.L9b54", B.L9b54),
  ("ff_aac_sbr_apply.L9b59", B.L9b59),
  ("ff_aac_sbr_apply.L9b5e", B.L9b5e),
  ("ff_aac_sbr_apply.L9b63", B.L9b63),
  ("ff_aac_sbr_apply.L9b68", B.L9b68),
  ("ff_aac_sbr_apply.L9b6d", B.L9b6d),
  ("ff_aac_sbr_apply.L9b72", B.L9b72),
  ("ff_aac_sbr_apply.L9b77", B.L9b77),
  ("ff_aac_sbr_apply.L9b7c", B.L9b7c),
  ("ff_aac_sbr_apply.L9b81", B.L9b81),
  ("ff_aac_sbr_apply.L9b86", B.L9b86),
  ("ff_aac_sbr_apply.L9b8b", B.L9b8b),
  ("ff_aac_sbr_apply.L9b90", B.L9b90),
  ("ff_aac_sbr_apply.L9b95", B.L9b95),
  ("ff_aac_sbr_apply.L9b9a", B.L9b9a),
  ("ff_aac_sbr_apply.L9b9a_1", B.L9b9a_1),
  ("ff_aac_sbr_apply.L9bc5", B.L9bc5),
  ("ff_aac_sbr_apply.L9bca", B.L9bca),
  ("ff_aac_sbr_apply.L9bcf", B.L9bcf),
  ("ff_aac_sbr_apply.L9bd4", B.L9bd4),
  ("ff_aac_sbr_apply.L9bd4_1", B.L9bd4_1),
  ("ff_aac_sbr_apply.L9bff", B.L9bff),
  ("ff_aac_sbr_apply.L9c04", B.L9c04),
  ("ff_aac_sbr_apply.L9c09", B.L9c09),
  ("ff_aac_sbr_apply.L9c0e", B.L9c0e),
  ("ff_aac_sbr_apply.L9c13", B.L9c13),
  ("ff_aac_sbr_apply.L9c18", B.L9c18),
  ("ff_aac_sbr_apply.L9c1d", B.L9c1d),
  ("ff_aac_sbr_apply.L9c22", B.L9c22),
  ("ff_aac_sbr_apply.L9c27", B.L9c27)]


/-- The text of `ff_aac_sbr_apply`: the blocks glued with their labels. -/
def body : Program := blocks.flatMap Program.blockCells

end Kraken.Examples.Sbr.Apply

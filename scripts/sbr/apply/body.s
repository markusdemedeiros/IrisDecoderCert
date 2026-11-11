ff_aac_sbr_apply:
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
ff_aac_sbr_apply.start_1:
    mov 0x57f4(%rdi),%eax
    xor %r14d,%r14d
    cmp 0x28920(%rsi),%eax
    setl -0xf0(%rbp)
    cmp $0x1,%edx
    sete %al
ff_aac_sbr_apply.start_2:
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
ff_aac_sbr_apply.start_3:
    jne ff_aac_sbr_apply.L6825
ff_aac_sbr_apply.L676e:
    mov 0x28978(%r9),%eax
    mov 0x28980(%r9),%ecx
    mov %eax,0x28974(%r9)
    mov %ecx,0x2897c(%r9)
    test %bl,%bl
    jne ff_aac_sbr_apply.L74e9
    jmp ff_aac_sbr_apply.L6838
ff_aac_sbr_apply.L6797:
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
ff_aac_sbr_apply.L6797_1:
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
ff_aac_sbr_apply.L6817:
    cmpl $0x0,0x28984(%r9)
    je ff_aac_sbr_apply.L676e
ff_aac_sbr_apply.L6825:
    movl $0x0,0x28984(%r9)
    test %bl,%bl
    jne ff_aac_sbr_apply.L74e9
ff_aac_sbr_apply.L6838:
    mov $0x1,%eax
    mov %rax,-0xc8(%rbp)
ff_aac_sbr_apply.L6838_1:
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
ff_aac_sbr_apply.L6838_2:
    vmovss LCPI14_5(%rip),%xmm3
    nop
ff_aac_sbr_apply.L68b0:
    movzbl 0x289ac(%r9,%rbx,1),%eax
    cmp $0x1,%al
    ja ff_aac_sbr_apply.L6ff7
    xor %r14d,%r14d
    jmp ff_aac_sbr_apply.L68f8
    nop
ff_aac_sbr_apply.L68d0:
    vaddss %xmm3,%xmm4,%xmm1
    vdivss %xmm1,%xmm0,%xmm0
    vmovss %xmm0,-0x15ac0(%r13,%r14,4)
    vmulss %xmm0,%xmm4,%xmm0
ff_aac_sbr_apply.L68d0_1:
    vmovss %xmm0,0x0(%r13,%r14,4)
    inc %r14
    cmp $0x2,%al
    jae ff_aac_sbr_apply.L6ff7
ff_aac_sbr_apply.L68f8:
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
ff_aac_sbr_apply.L6940:
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
ff_aac_sbr_apply.L6940_1:
    vpaddd LCPI14_2(%rip),%xmm0,%xmm0
    vcvtps2pd %xmm0,%xmm1
    vmovapd %xmm1,%xmm0
    cmp $0xf4,%cl
    jb ff_aac_sbr_apply.L69a4
    vmovsd LCPI14_3(%rip),%xmm0
ff_aac_sbr_apply.L69a4:
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
ff_aac_sbr_apply.L69d0:
    shl $0x17,%ecx
    add $0x43000000,%ecx
    vmovd %ecx,%xmm0
ff_aac_sbr_apply.L69dd:
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
ff_aac_sbr_apply.L6a10:
    vpxor %xmm4,%xmm4,%xmm4
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6a30
    add $0x95,%cl
    mov $0x1,%edx
    shl %cl,%edx
    vmovd %edx,%xmm4
    nop
ff_aac_sbr_apply.L6a30:
    vcvtss2sd %xmm0,%xmm0,%xmm1
    vucomisd %xmm2,%xmm1
    jbe ff_aac_sbr_apply.L68d0
    xor %edi,%edi
    mov $0x10,%esi
    lea L_str_33(%rip),%rdx
    xor %eax,%eax
    vmovd %xmm4,-0x30(%rbp)
ff_aac_sbr_apply.L6a30_1:
    call av_log
ff_aac_sbr_apply.L6a30_2:
    vmovd -0x30(%rbp),%xmm4
    vmovss LCPI14_5(%rip),%xmm3
    vmovsd LCPI14_4(%rip),%xmm2
    mov -0x38(%rbp),%r9
    movzbl 0x289ac(%r9,%rbx,1),%eax
    vmovaps %xmm3,%xmm0
    jmp ff_aac_sbr_apply.L68d0
    nop
ff_aac_sbr_apply.L6a90:
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
ff_aac_sbr_apply.L6abf:
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
ff_aac_sbr_apply.L6b00:
    xor %ecx,%ecx
ff_aac_sbr_apply.L6b02:
    inc %rdx
    add $0x5,%rsi
    cmp %rdx,%rax
    je ff_aac_sbr_apply.L74de
ff_aac_sbr_apply.L6b12:
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
ff_aac_sbr_apply.L6b50:
    vxorpd %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6b6c
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
ff_aac_sbr_apply.L6b6c:
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
ff_aac_sbr_apply.L6ba0:
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6bbc
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
ff_aac_sbr_apply.L6bbc:
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e414(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
ff_aac_sbr_apply.L6bbc_1:
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
ff_aac_sbr_apply.L6c1e:
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6c3a
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
ff_aac_sbr_apply.L6c3a:
    movzbl 0x53eb6(%r9,%rsi,1),%edi
    mov $0xc,%ecx
    sub %edi,%ecx
    cmp $0x8b,%edi
    jae ff_aac_sbr_apply.L6c61
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6c7d
ff_aac_sbr_apply.L6c61:
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6c7d
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
ff_aac_sbr_apply.L6c7d:
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e418(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
ff_aac_sbr_apply.L6c7d_1:
    vmovss %xmm2,0x53ed8(%r9,%rsi,4)
ff_aac_sbr_apply.L6c7d_2:
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
ff_aac_sbr_apply.L6ce0:
    mov %edi,%r8d
    mov %edi,%ecx
    jmp ff_aac_sbr_apply.L6b02
ff_aac_sbr_apply.L6cea:
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6d09
    mov $0x9c,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm2
ff_aac_sbr_apply.L6d09:
    movzbl 0x53eb7(%r9,%rsi,1),%r8d
    mov $0xc,%ecx
    sub %r8d,%ecx
    cmp $0x8b,%r8d
    jae ff_aac_sbr_apply.L6d32
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6d51
ff_aac_sbr_apply.L6d32:
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6d51
    mov $0xa1,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm3
ff_aac_sbr_apply.L6d51:
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e41c(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
ff_aac_sbr_apply.L6d51_1:
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
ff_aac_sbr_apply.L6dbc:
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6ddb
    mov $0x9c,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm2
ff_aac_sbr_apply.L6ddb:
    movzbl 0x53eb8(%r9,%rsi,1),%r8d
    mov $0xc,%ecx
    sub %r8d,%ecx
    cmp $0x8b,%r8d
    jae ff_aac_sbr_apply.L6e04
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6e23
ff_aac_sbr_apply.L6e04:
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6e23
    mov $0xa1,%cl
    sub %r8b,%cl
    mov $0x1,%r8d
    shl %cl,%r8d
    vmovd %r8d,%xmm3
ff_aac_sbr_apply.L6e23:
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e420(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
ff_aac_sbr_apply.L6e23_1:
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
ff_aac_sbr_apply.L6e8c:
    vxorps %xmm2,%xmm2,%xmm2
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6ea8
    mov $0x9c,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm2
ff_aac_sbr_apply.L6ea8:
    movzbl 0x53eb9(%r9,%rsi,1),%edi
    mov $0xc,%ecx
    sub %edi,%ecx
    cmp $0x8b,%edi
    jae ff_aac_sbr_apply.L6ecf
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    vmovd %ecx,%xmm3
    jmp ff_aac_sbr_apply.L6eeb
ff_aac_sbr_apply.L6ecf:
    vxorps %xmm3,%xmm3,%xmm3
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L6eeb
    mov $0xa1,%cl
    sub %dil,%cl
    mov $0x1,%edi
    shl %cl,%edi
    vmovd %edi,%xmm3
ff_aac_sbr_apply.L6eeb:
    vcvtss2sd %xmm2,%xmm2,%xmm4
    vucomisd %xmm4,%xmm0
    jb ff_aac_sbr_apply.L9b9a
    vaddss %xmm1,%xmm3,%xmm4
    vdivss %xmm4,%xmm2,%xmm2
    vmovss %xmm2,0x3e424(%r9,%rsi,4)
    vmulss %xmm2,%xmm3,%xmm2
ff_aac_sbr_apply.L6eeb_1:
    vmovss %xmm2,0x53ee4(%r9,%rsi,4)
ff_aac_sbr_apply.L6eeb_2:
    mov 0x74b08(%r9),%r8d
    mov %r8d,%ecx
    cmp $0x5,%r8d
    jbe ff_aac_sbr_apply.L6b02
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L6f32:
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    lea L_str_2(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
ff_aac_sbr_apply.L6f32_1:
    mov -0x38(%rbp),%r9
    movq $0x0,0x28924(%r9)
    movl $0x0,0x28930(%r9)
    movl $0x20,0x28978(%r9)
    movl $0x0,0x28980(%r9)
    movl $0xffffffff,0x41d68(%r9)
    movl $0xffffffff,0x2c2a8(%r9)
    movl $0xffffffff,0x2893c(%r9)
    movw $0xffff,0x28940(%r9)
ff_aac_sbr_apply.L6f32_2:
    cmpl $0x0,0x28984(%r9)
    jne ff_aac_sbr_apply.L6825
    jmp ff_aac_sbr_apply.L676e
ff_aac_sbr_apply.L6fbe:
    mov $0x2,%eax
    mov %rax,-0xc8(%rbp)
ff_aac_sbr_apply.L6fca:
    lea 0x289a0(%r9),%rax
    mov %rax,-0x58(%rbp)
    lea 0x3dbb0(%r9),%rax
    mov %rax,-0x50(%rbp)
    lea 0x3ddf0(%r9),%rax
    mov %rax,-0x48(%rbp)
    vmovsd LCPI14_4(%rip),%xmm1
    xor %eax,%eax
    jmp ff_aac_sbr_apply.L7044
ff_aac_sbr_apply.L6ff7:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L6ffc:
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%esi
ff_aac_sbr_apply.L7007:
    mov %esi,0x15a98(%r13)
ff_aac_sbr_apply.L700e:
    cmp $0x3,%rax
    jne ff_aac_sbr_apply.L9c13
    nop
ff_aac_sbr_apply.L7020:
    mov -0x30(%rbp),%rax
    inc %rax
    addq $0x15ac0,-0x50(%rbp)
ff_aac_sbr_apply.L7020_1:
    addq $0x15ac0,-0x48(%rbp)
ff_aac_sbr_apply.L7020_2:
    cmp -0xc8(%rbp),%rax
    je ff_aac_sbr_apply.L74de
ff_aac_sbr_apply.L7044:
    mov %rax,-0x30(%rbp)
    imul $0x15ac0,%rax,%rax
ff_aac_sbr_apply.L7044_1:
    mov -0x58(%rbp),%rcx
    lea (%rcx,%rax,1),%r13
    cmpl $0x0,0x8(%rcx,%rax,1)
    je ff_aac_sbr_apply.L71e0
    mov $0x1,%r15d
    mov -0x48(%rbp),%r12
    mov -0x50(%rbp),%r14
ff_aac_sbr_apply.L7070:
    movzbl 0xc(%r13,%r15,1),%eax
    cmp $0x1,%al
    ja ff_aac_sbr_apply.L99ee
    xor %ebx,%ebx
    jmp ff_aac_sbr_apply.L70ca
    nop
ff_aac_sbr_apply.L7090:
    xor %edi,%edi
    mov $0x10,%esi
    lea L_str_33(%rip),%rdx
    xor %eax,%eax
    call av_log
ff_aac_sbr_apply.L7090_1:
    vmovsd LCPI14_4(%rip),%xmm1
    mov -0x38(%rbp),%r9
    movl $0x3f800000,(%r12,%rbx,4)
ff_aac_sbr_apply.L7090_2:
    movzbl 0xc(%r13,%r15,1),%eax
ff_aac_sbr_apply.L70bf:
    inc %rbx
    cmp $0x2,%al
    jae ff_aac_sbr_apply.L99ee
ff_aac_sbr_apply.L70ca:
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
ff_aac_sbr_apply.L70ca_1:
    jbe ff_aac_sbr_apply.L70bf
    jmp ff_aac_sbr_apply.L7090
    nop
ff_aac_sbr_apply.L7120:
    cmp $0x30,%rbx
    jae ff_aac_sbr_apply.L9b45
    movzbl (%r14,%rbx,1),%ecx
    cmp $0xf6,%cl
    jb ff_aac_sbr_apply.L7166
    vmovsd LCPI14_3(%rip),%xmm0
    jmp ff_aac_sbr_apply.L717f
    nop
ff_aac_sbr_apply.L7140:
    shl $0x17,%ecx
    add $0x42800000,%ecx
    vmovd %ecx,%xmm0
    vmovd %xmm0,(%r12,%rbx,4)
    vcvtss2sd %xmm0,%xmm0,%xmm0
    vucomisd %xmm1,%xmm0
    ja ff_aac_sbr_apply.L7090
    jmp ff_aac_sbr_apply.L70bf
ff_aac_sbr_apply.L7166:
    mov %ecx,%edx
    shl $0x16,%edx
    and $0x3f800000,%edx
    add $0x42800000,%edx
    vmovd %edx,%xmm0
    vcvtss2sd %xmm0,%xmm0,%xmm0
ff_aac_sbr_apply.L717f:
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
ff_aac_sbr_apply.L71b0:
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
ff_aac_sbr_apply.L71e0:
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
ff_aac_sbr_apply.L71e0_1:
    jmp ff_aac_sbr_apply.L723c
ff_aac_sbr_apply.L7226:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L723c
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L723c:
    mov %edi,0x15a74(%r13)
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L7370
ff_aac_sbr_apply.L723c_1:
    movzbl 0x15a56(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7270
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7286
ff_aac_sbr_apply.L7270:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7286
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L7286:
    mov %edi,0x15a78(%r13)
    cmp $0x3,%edx
    jb ff_aac_sbr_apply.L7370
ff_aac_sbr_apply.L7286_1:
    movzbl 0x15a57(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L72ba
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L72d0
ff_aac_sbr_apply.L72ba:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L72d0
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L72d0:
    mov %edi,0x15a7c(%r13)
    cmp $0x3,%edx
    je ff_aac_sbr_apply.L7370
ff_aac_sbr_apply.L72d0_1:
    movzbl 0x15a58(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7304
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L731a
ff_aac_sbr_apply.L7304:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L731a
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L731a:
    mov %edi,0x15a80(%r13)
    cmp $0x5,%edx
    jb ff_aac_sbr_apply.L7370
ff_aac_sbr_apply.L731a_1:
    movzbl 0x15a59(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L734a
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7360
ff_aac_sbr_apply.L734a:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7360
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L7360:
    mov %edi,0x15a84(%r13)
    cmp $0x5,%edx
    jne ff_aac_sbr_apply.L9c22
ff_aac_sbr_apply.L7370:
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
ff_aac_sbr_apply.L73a1:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L73b7
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L73b7:
    mov %edi,0x15a88(%r13)
    cmp $0x1,%edx
    je ff_aac_sbr_apply.L700e
ff_aac_sbr_apply.L73b7_1:
    movzbl 0x15a5b(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L73eb
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7401
ff_aac_sbr_apply.L73eb:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7401
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L7401:
    mov %edi,0x15a8c(%r13)
    cmp $0x3,%edx
    jb ff_aac_sbr_apply.L700e
ff_aac_sbr_apply.L7401_1:
    movzbl 0x15a5c(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L7435
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L744b
ff_aac_sbr_apply.L7435:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L744b
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L744b:
    mov %edi,0x15a90(%r13)
    cmp $0x3,%edx
    je ff_aac_sbr_apply.L700e
ff_aac_sbr_apply.L744b_1:
    movzbl 0x15a5d(%r13),%esi
    mov $0x6,%ecx
    sub %esi,%ecx
    cmp $0x85,%esi
    jae ff_aac_sbr_apply.L747f
    shl $0x17,%ecx
    add $0x3f800000,%ecx
    mov %ecx,%edi
    jmp ff_aac_sbr_apply.L7495
ff_aac_sbr_apply.L747f:
    xor %edi,%edi
    cmp $0xffffff6b,%ecx
    jb ff_aac_sbr_apply.L7495
    mov $0x9b,%cl
    sub %sil,%cl
    mov $0x1,%edi
    shl %cl,%edi
ff_aac_sbr_apply.L7495:
    mov %edi,0x15a94(%r13)
    cmp $0x5,%edx
    jb ff_aac_sbr_apply.L700e
ff_aac_sbr_apply.L7495_1:
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
ff_aac_sbr_apply.L74de:
    movl $0x0,0x28928(%r9)
ff_aac_sbr_apply.L74e9:
    lea _GLOBAL_OFFSET_TABLE_(%rip),%rax
    lea 0x28920(%r9),%rcx
    mov %rcx,-0xb0(%rbp)
ff_aac_sbr_apply.L74e9_1:
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
ff_aac_sbr_apply.L74e9_2:
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
ff_aac_sbr_apply.L74e9_3:
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
ff_aac_sbr_apply.L74e9_4:
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
ff_aac_sbr_apply.L7682:
    mov -0x90(%rbp),%rax
    mov 0x2550(%rax),%rax
    mov %rax,-0x30(%rbp)
    mov %r12,%r14
ff_aac_sbr_apply.L7682_1:
    mov 0x88ae0(%r9),%rax
    mov %rax,-0x58(%rbp)
ff_aac_sbr_apply.L7682_2:
    mov 0x88ae8(%r9),%rax
    mov %rax,-0x50(%rbp)
    mov %ecx,-0xf8(%rbp)
    test $0x1,%cl
ff_aac_sbr_apply.L7682_3:
    mov -0x128(%rbp),%rax
    cmovne -0x130(%rbp),%rax
    mov %rax,-0x68(%rbp)
    mov %rdx,-0x1a0(%rbp)
    imul $0x15ac0,%rdx,%r13
ff_aac_sbr_apply.L7682_4:
    mov -0x138(%rbp),%rcx
    lea (%rcx,%r13,1),%rax
    mov %rax,-0x48(%rbp)
    lea (%rcx,%r13,1),%rdi
    add $0x2480,%rdi
    lea 0x3920(%rcx,%r13,1),%rax
    mov %rax,-0x78(%rbp)
ff_aac_sbr_apply.L7682_5:
    movslq 0x7920(%rcx,%r13,1),%r15
    lea 0x3480(%rcx,%r13,1),%rsi
    mov $0x480,%edx
    mov %rdi,%r12
    mov %r9,%rbx
    call memcpy
ff_aac_sbr_apply.L7682_6:
    mov %r13,-0x98(%rbp)
ff_aac_sbr_apply.L7682_7:
    mov -0x138(%rbp),%rax
    lea (%rax,%r13,1),%rdi
    add $0x2900,%rdi
    mov $0x1000,%edx
    mov -0x68(%rbp),%rsi
    call memcpy
ff_aac_sbr_apply.L7682_8:
    shl $0xd,%r15
    add -0x78(%rbp),%r15
    xor %r13d,%r13d
    nop
ff_aac_sbr_apply.L7750:
    lea (%r12,%r13,1),%rdx
    mov %r14,%rdi
    mov -0xf0(%rbp),%rsi
    mov $0x140,%ecx
    mov -0x30(%rbp),%rax
    call *0x38(%rax)
ff_aac_sbr_apply.L7750_1:
    mov %r14,%rdi
    call *0x88b00(%rbx)
ff_aac_sbr_apply.L7750_2:
    mov %r14,%rdi
    call *0x88b18(%rbx)
ff_aac_sbr_apply.L7750_3:
    mov $0x4,%ecx
    mov -0x58(%rbp),%rdi
    mov %r14,%rsi
    mov -0xc8(%rbp),%rdx
    call *-0x50(%rbp)
ff_aac_sbr_apply.L7750_4:
    mov %r15,%rdi
    mov %r14,%rsi
    call *0x88b20(%rbx)
ff_aac_sbr_apply.L7750_5:
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
ff_aac_sbr_apply.L7750_6:
    mov 0x7920(%r15),%eax
    xor $0x1,%eax
    mov %eax,0x7920(%r15)
ff_aac_sbr_apply.L7750_7:
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
ff_aac_sbr_apply.L7750_8:
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
ff_aac_sbr_apply.L7866:
    vmovss 0x390c(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7884
    vmovss LCPI14_10(%rip),%xmm2
ff_aac_sbr_apply.L7884:
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
ff_aac_sbr_apply.L7884_1:
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
ff_aac_sbr_apply.L78f2:
    vmovss 0x3910(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7910
    vmovss LCPI14_10(%rip),%xmm2
ff_aac_sbr_apply.L7910:
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
ff_aac_sbr_apply.L7910_1:
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
ff_aac_sbr_apply.L797e:
    vmovss 0x3914(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L799c
    vmovss LCPI14_10(%rip),%xmm2
ff_aac_sbr_apply.L799c:
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
ff_aac_sbr_apply.L799c_1:
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
ff_aac_sbr_apply.L7a0a:
    vmovss 0x3918(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7a28
    vmovss LCPI14_10(%rip),%xmm2
ff_aac_sbr_apply.L7a28:
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
ff_aac_sbr_apply.L7a28_1:
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
ff_aac_sbr_apply.L7a96:
    vmovss 0x391c(%rbx),%xmm1
    vucomiss %xmm0,%xmm1
    vmovss LCPI14_9(%rip),%xmm2
    ja ff_aac_sbr_apply.L7ab4
    vmovss LCPI14_10(%rip),%xmm2
ff_aac_sbr_apply.L7ab4:
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
ff_aac_sbr_apply.L7b00:
    movslq 0x8(%rbx),%rcx
    mov %rcx,-0x30(%rbp)
    test %rcx,%rcx
    je ff_aac_sbr_apply.L9bd4
ff_aac_sbr_apply.L7b00_1:
    mov 0x28978(%r8),%r12d
    mov 0x74c50(%r8),%eax
    test %eax,%eax
    je ff_aac_sbr_apply.L7cb0
    xor %r13d,%r13d
    xor %r15d,%r15d
ff_aac_sbr_apply.L7b2d:
    cmpb $0x0,0x74c54(%r8,%r15,1)
    je ff_aac_sbr_apply.L7c5d
    movslq %r12d,%r12
    xor %r14d,%r14d
    nop
ff_aac_sbr_apply.L7b50:
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
ff_aac_sbr_apply.L7b80:
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
ff_aac_sbr_apply.L7bb0:
    mov %edx,%r13d
ff_aac_sbr_apply.L7bb3:
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
ff_aac_sbr_apply.L7bb3_1:
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
ff_aac_sbr_apply.L7bb3_2:
    mov %rbx,%r8
    mov -0x48(%rbp),%rbx
    inc %r14d
    inc %r12
    movzbl 0x74c54(%r8,%r15,1),%eax
    cmp %eax,%r14d
    jb ff_aac_sbr_apply.L7b50
    mov 0x74c50(%r8),%eax
ff_aac_sbr_apply.L7c5d:
    inc %r15
    mov %eax,%ecx
    cmp %rcx,%r15
    jae ff_aac_sbr_apply.L8b4f
    cmp $0x6,%r15
    jne ff_aac_sbr_apply.L7b2d
    jmp ff_aac_sbr_apply.L9a5f
    nop
ff_aac_sbr_apply.L7c80:
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    mov $0x10,%esi
    lea L_str_35(%rip),%rdx
    mov %r12d,%ecx
    xor %eax,%eax
    call av_log
ff_aac_sbr_apply.L7c80_1:
    jmp ff_aac_sbr_apply.L7ce0
    nop
ff_aac_sbr_apply.L7cb0:
    mov %r12d,%eax
    add 0x28980(%r8),%eax
    sub %r12d,%eax
    jbe ff_aac_sbr_apply.L7ce4
ff_aac_sbr_apply.L7cbf:
    movslq %r12d,%rcx
    lea (%rcx,%rcx,4),%rdi
    shl $0x6,%rdi
    add -0xb8(%rbp),%rdi
    shl $0x6,%rax
    lea (%rax,%rax,4),%rdx
    xor %esi,%esi
    call memset
ff_aac_sbr_apply.L7ce0:
    mov -0x38(%rbp),%r8
ff_aac_sbr_apply.L7ce4:
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
ff_aac_sbr_apply.L7ce4_1:
    vmovaps %ymm0,0x150a0(%rbx)
    vmovaps %ymm0,0x15080(%rbx)
    vmovaps %ymm0,0x15060(%rbx)
ff_aac_sbr_apply.L7ce4_2:
    cmpl $0x0,0x8(%rbx)
    vmovss LCPI14_5(%rip),%xmm9
    je ff_aac_sbr_apply.L8790
    lea 0x15390(%rbx),%rax
    mov %rax,-0xe0(%rbp)
    lea 0x15a60(%rbx),%rax
    mov %rax,-0xd8(%rbp)
ff_aac_sbr_apply.L7ce4_3:
    mov -0x180(%rbp),%rax
    mov -0x98(%rbp),%rcx
    lea (%rax,%rcx,1),%r11
    mov $0x1,%ecx
    mov %r8,-0x60(%rbp)
ff_aac_sbr_apply.L7ce4_4:
    mov -0x188(%rbp),%rax
    mov %rax,-0x58(%rbp)
ff_aac_sbr_apply.L7ce4_5:
    mov -0xd0(%rbp),%r12
    xor %eax,%eax
    mov %r10,-0x80(%rbp)
    mov %r11,-0xe8(%rbp)
    nop
ff_aac_sbr_apply.L7db0:
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
ff_aac_sbr_apply.L7db0_1:
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
ff_aac_sbr_apply.L7e20:
    mov %r9d,%edi
    cmp -0x50(%rbp),%rdx
    je ff_aac_sbr_apply.L7e90
ff_aac_sbr_apply.L7e29:
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
ff_aac_sbr_apply.L7e60:
    vmovss (%rcx,%rsi,4),%xmm0
    vmovss %xmm0,(%r12,%r8,4)
ff_aac_sbr_apply.L7e60_1:
    movzwl (%r15,%rdx,2),%r9d
    cmp %r9,%rdi
    jae ff_aac_sbr_apply.L7e20
    inc %r8
    inc %rdi
    cmp $0x30,%r8d
    jb ff_aac_sbr_apply.L7e60
    jmp ff_aac_sbr_apply.L99e9
    nop
ff_aac_sbr_apply.L7e90:
    mov %r14,-0x68(%rbp)
    mov $0x1,%edx
ff_aac_sbr_apply.L7e90_1:
    cmpl $0x2,0x18(%rbx)
    jb ff_aac_sbr_apply.L7eb6
    movzbl 0x15a9c(%rbx,%rax,1),%ecx
    cmp 0x15aa7(%rbx),%cl
    mov $0x2,%edx
    sbb $0x0,%rdx
ff_aac_sbr_apply.L7eb6:
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
ff_aac_sbr_apply.L7eb6_1:
    je ff_aac_sbr_apply.L7f36
    mov %edi,%r10d
    sub -0x30(%rbp),%r10d
    neg %r9
    xor %r11d,%r11d
    nop
ff_aac_sbr_apply.L7f10:
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
ff_aac_sbr_apply.L7f36:
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
ff_aac_sbr_apply.L7f36_1:
    mov $0x21998,%r14d
    nop
ff_aac_sbr_apply.L7f80:
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
ff_aac_sbr_apply.L7f80_1:
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
ff_aac_sbr_apply.L8009:
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
ff_aac_sbr_apply.L8050:
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
ff_aac_sbr_apply.L8077:
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
ff_aac_sbr_apply.L8077_1:
    mov $0x21998,%r14d
    nop
ff_aac_sbr_apply.L80c0:
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
ff_aac_sbr_apply.L80c0_1:
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
ff_aac_sbr_apply.L814a:
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
ff_aac_sbr_apply.L8190:
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
ff_aac_sbr_apply.L81b7:
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
ff_aac_sbr_apply.L81b7_1:
    mov $0x21998,%r14d
    nop
ff_aac_sbr_apply.L8200:
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
ff_aac_sbr_apply.L8200_1:
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
ff_aac_sbr_apply.L828a:
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
ff_aac_sbr_apply.L82d0:
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
ff_aac_sbr_apply.L82f7:
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
ff_aac_sbr_apply.L82f7_1:
    mov $0x21998,%r14d
    nop
ff_aac_sbr_apply.L8340:
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
ff_aac_sbr_apply.L8340_1:
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
ff_aac_sbr_apply.L83ca:
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
ff_aac_sbr_apply.L8410:
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
ff_aac_sbr_apply.L8437:
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
ff_aac_sbr_apply.L8437_1:
    mov $0x21998,%ebx
    nop
ff_aac_sbr_apply.L8480:
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
ff_aac_sbr_apply.L8480_1:
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
ff_aac_sbr_apply.L8509:
    cmp $0x5,%ecx
    mov -0x38(%rbp),%r8
    jne ff_aac_sbr_apply.L9c18
    nop
ff_aac_sbr_apply.L8520:
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
ff_aac_sbr_apply.L8570:
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
ff_aac_sbr_apply.L8570_1:
    jmp ff_aac_sbr_apply.L85cd
    nop
ff_aac_sbr_apply.L85c0:
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b54
    mov %r10d,%r10d
ff_aac_sbr_apply.L85cd:
    mov %r9b,(%rcx,%r10,1)
ff_aac_sbr_apply.L85cd_1:
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
ff_aac_sbr_apply.L85cd_2:
    cmpb $0x1,(%r14,%r8,1)
    movzbl %r9b,%r9d
    cmovne %r11d,%r9d
    jmp ff_aac_sbr_apply.L862d
    nop
ff_aac_sbr_apply.L8620:
    cmp $0x2f,%r10d
    ja ff_aac_sbr_apply.L9b54
    mov %r10d,%r8d
ff_aac_sbr_apply.L862d:
    mov %r9b,(%rcx,%r8,1)
    add $0x2,%rdi
ff_aac_sbr_apply.L862d_1:
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
ff_aac_sbr_apply.L8660:
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
ff_aac_sbr_apply.L86a0:
    xor %esi,%esi
    mov %eax,%edx
    sub -0x30(%rbp),%edx
    cmp $0x31,%edx
    jae ff_aac_sbr_apply.L9b4f
ff_aac_sbr_apply.L86b0:
    inc %r13
    mov %edx,%edi
    add %r14,%rdi
    sub %eax,%ecx
    movslq %ecx,%rdx
    movzbl %sil,%esi
    vzeroupper
    call memset
ff_aac_sbr_apply.L86b0_1:
    cmp -0x50(%rbp),%r13
    vmovss LCPI14_5(%rip),%xmm9
    je ff_aac_sbr_apply.L8740
ff_aac_sbr_apply.L86d7:
    movzwl (%r15,%r13,2),%eax
    movzwl 0x2(%r15,%r13,2),%ecx
    cmp %cx,%ax
    jae ff_aac_sbr_apply.L86a0
    mov %ecx,%edx
    sub %rax,%rdx
    mov -0x78(%rbp),%rsi
    add %eax,%esi
    nop
ff_aac_sbr_apply.L8700:
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
ff_aac_sbr_apply.L8720:
    mov $0x1,%sil
    mov %eax,%edx
    sub -0x30(%rbp),%edx
    cmp $0x31,%edx
    jb ff_aac_sbr_apply.L86b0
    jmp ff_aac_sbr_apply.L9b4f
    nop
ff_aac_sbr_apply.L8740:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%eax
    mov -0x68(%rbp),%rdx
    cmp %rax,%rdx
    mov -0x38(%rbp),%r8
    jae ff_aac_sbr_apply.L8818
    lea 0x1(%rdx),%rcx
    add $0xc0,%r12
    addq $0xc0,-0x58(%rbp)
ff_aac_sbr_apply.L8740_1:
    addq $0xc0,-0x60(%rbp)
    mov %rdx,%rax
    cmp $0x8,%rdx
    jne ff_aac_sbr_apply.L7db0
    jmp ff_aac_sbr_apply.L9b7c
    nop
ff_aac_sbr_apply.L8790:
    mov 0x28978(%r8),%eax
    mov %eax,-0x30(%rbp)
    xor %eax,%eax
    jmp ff_aac_sbr_apply.L881c
ff_aac_sbr_apply.L879e:
    mov -0x90(%rbp),%rax
    mov 0x8(%rax),%rdi
    mov $0x10,%esi
    lea L_str_36(%rip),%rdx
    xor %eax,%eax
    vzeroupper
    call av_log
ff_aac_sbr_apply.L879e_1:
    mov -0x38(%rbp),%rax
    movq $0x0,0x28924(%rax)
    movl $0x0,0x28930(%rax)
    movl $0x20,0x28978(%rax)
    movl $0x0,0x28980(%rax)
    movl $0xffffffff,0x41d68(%rax)
    movl $0xffffffff,0x2c2a8(%rax)
ff_aac_sbr_apply.L879e_2:
    mov -0x168(%rbp),%rax
    movw $0xffff,0x4(%rax)
    movl $0xffffffff,(%rax)
    jmp ff_aac_sbr_apply.L9927
ff_aac_sbr_apply.L8818:
    mov -0x80(%rbp),%r10
ff_aac_sbr_apply.L881c:
    lea 0x3904(%rbx),%rcx
    mov %rcx,-0x110(%rbp)
    mov %eax,%ecx
    lea (%rcx,%rcx,2),%rdx
    shl $0x4,%rdx
    vmovups (%r10,%rdx,1),%ymm0
    vmovups 0x10(%r10,%rdx,1),%ymm1
    vmovups %ymm1,0x10(%r10)
    vmovups %ymm0,(%r10)
ff_aac_sbr_apply.L881c_1:
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
ff_aac_sbr_apply.L881c_2:
    movzbl 0x15a9d(%rbx),%r15d
    sub %r12d,%r15d
    vcvtsi2ss %r15d,%xmm15,%xmm0
    lea (%r12,%r12,1),%eax
    vmovss LCPI14_12(%rip),%xmm1
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
    add %r15d,%r15d
    mov %rdi,-0x50(%rbp)
ff_aac_sbr_apply.L881c_3:
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L881c_4:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    add %r14,%rax
    add %rax,%r12
    xor %ebx,%ebx
    nop
ff_aac_sbr_apply.L8900:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86de0(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8900_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8b2a
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8900_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8900
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8947:
    test %eax,%eax
    je ff_aac_sbr_apply.L98e0
    movslq -0x30(%rbp),%rcx
    mov %rcx,-0x60(%rbp)
    mov $0x1,%ecx
ff_aac_sbr_apply.L8947_1:
    mov -0x38(%rbp),%rsi
    mov %rsi,%rdi
    xor %r8d,%r8d
    nop
ff_aac_sbr_apply.L8970:
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
ff_aac_sbr_apply.L8970_1:
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
ff_aac_sbr_apply.L89e0:
    mov -0x48(%rbp),%rax
    movzbl 0xc(%rax,%r8,1),%ecx
    cmp $0x2,%cl
    jae ff_aac_sbr_apply.L9a64
ff_aac_sbr_apply.L89f3:
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
ff_aac_sbr_apply.L89f3_1:
    add %r13,%r15
    shl $0x6,%r15d
    add -0x80(%rbp),%r15
    vxorps %xmm1,%xmm1,%xmm1
    nop
ff_aac_sbr_apply.L8a50:
    vmovss %xmm1,-0x30(%rbp)
    mov %r15,%rdi
    mov %r12d,%esi
ff_aac_sbr_apply.L8a50_1:
    mov -0x38(%rbp),%rax
    vzeroupper
    call *0x88b08(%rax)
ff_aac_sbr_apply.L8a50_2:
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
ff_aac_sbr_apply.L8a50_3:
    jae ff_aac_sbr_apply.L89e0
    mov %rax,%rcx
    sub -0x60(%rbp),%rcx
    cmp $0x2f,%rcx
    ja ff_aac_sbr_apply.L99f8
    vcvtsi2ss %edx,%xmm15,%xmm0
    vdivss %xmm0,%xmm1,%xmm0
    inc %rax
    nop
ff_aac_sbr_apply.L8ad0:
    vmovss %xmm0,0x86de0(%rdi,%rcx,4)
ff_aac_sbr_apply.L8ad0_1:
    movzwl (%r14,%rbx,2),%edx
    cmp %rdx,%rax
    jae ff_aac_sbr_apply.L89e0
    inc %rcx
    inc %rax
    cmp $0x30,%rcx
    jb ff_aac_sbr_apply.L8ad0
    jmp ff_aac_sbr_apply.L99f8
    nop
ff_aac_sbr_apply.L8b00:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%eax
    cmp %rax,%r8
    jae ff_aac_sbr_apply.L9146
    lea 0x1(%r8),%rcx
    add $0xc0,%rdi
    cmp $0x8,%r8
    jne ff_aac_sbr_apply.L8970
    jmp ff_aac_sbr_apply.L9bff
ff_aac_sbr_apply.L8b2a:
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
ff_aac_sbr_apply.L8b4f:
    mov 0x28978(%r8),%eax
    add 0x28980(%r8),%eax
    sub %r12d,%eax
    ja ff_aac_sbr_apply.L7cbf
    jmp ff_aac_sbr_apply.L7ce4
ff_aac_sbr_apply.L8b6b:
    mov $0x1,%sil
    cmp $0x2,%ecx
    jb ff_aac_sbr_apply.L9146
ff_aac_sbr_apply.L8b77:
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
ff_aac_sbr_apply.L8b77_1:
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8b77_2:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
    nop
ff_aac_sbr_apply.L8bf0:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86ea0(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8bf0_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8c33
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8bf0_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8bf0
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8c33:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
ff_aac_sbr_apply.L8c4c:
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
ff_aac_sbr_apply.L8c4c_1:
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8c4c_2:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L8cc9:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x86f60(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8cc9_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8d0c
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8cc9_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8cc9
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8d0c:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
ff_aac_sbr_apply.L8d26:
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
ff_aac_sbr_apply.L8d26_1:
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8d26_2:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L8da3:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87020(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8da3_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8de6
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8da3_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8da3
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8de6:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
ff_aac_sbr_apply.L8dff:
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
ff_aac_sbr_apply.L8dff_1:
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8dff_2:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L8e7c:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x870e0(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8e7c_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    mov %r13,%r8
    jae ff_aac_sbr_apply.L8ebf
    mov %r12,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8e7c_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8e7c
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8ebf:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
    vmovss LCPI14_5(%rip),%xmm9
    mov %r14,%rdi
ff_aac_sbr_apply.L8ed9:
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
ff_aac_sbr_apply.L8ed9_1:
    add %r15d,%r15d
    mov %rdi,%r14
    lea (%rdi,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov %r8,%r13
    vzeroupper
    call *0x88b08(%r8)
ff_aac_sbr_apply.L8ed9_2:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L8f56:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x871a0(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L8f56_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L8f93
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r13)
ff_aac_sbr_apply.L8f56_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L8f56
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L8f93:
    mov -0x48(%rbp),%rbx
    mov 0x8(%rbx),%ecx
    test %eax,%eax
    sete %dl
    mov %ecx,%eax
    mov %r14,%rdi
ff_aac_sbr_apply.L8fa4:
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
ff_aac_sbr_apply.L8fa4_1:
    vdivss %xmm0,%xmm1,%xmm0
    vmovss %xmm0,-0x30(%rbp)
ff_aac_sbr_apply.L8fa4_2:
    add %r15d,%r15d
    lea (%r14,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov -0x38(%rbp),%r13
    vzeroupper
    call *0x88b08(%r13)
ff_aac_sbr_apply.L8fa4_3:
    shl $0x4,%r12d
    mov -0x70(%rbp),%rax
    mov -0x50(%rbp),%rcx
    add %rcx,%rax
    add %rax,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L9026:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87260(%r13,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L9026_1:
    mov 0x28980(%r13),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L9070
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r13)
ff_aac_sbr_apply.L9026_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L9026
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L9063:
    vmovss LCPI14_5(%rip),%xmm9
    jmp ff_aac_sbr_apply.L9146
ff_aac_sbr_apply.L9070:
    mov -0x48(%rbp),%rcx
    mov 0x8(%rcx),%ecx
    test %eax,%eax
    sete %sil
    mov %ecx,%eax
ff_aac_sbr_apply.L907f:
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
ff_aac_sbr_apply.L907f_1:
    vmovss %xmm0,-0x30(%rbp)
ff_aac_sbr_apply.L907f_2:
    add %r15d,%r15d
    lea (%r14,%rax,8),%rdi
    add $0x10,%rdi
    mov %r15d,%esi
    mov -0x38(%rbp),%r14
    vzeroupper
    call *0x88b08(%r14)
ff_aac_sbr_apply.L907f_3:
    shl $0x4,%ebx
    mov -0x50(%rbp),%r12
    add -0x70(%rbp),%r12
    add %rbx,%r12
    xor %ebx,%ebx
ff_aac_sbr_apply.L90f9:
    vmulss -0x30(%rbp),%xmm0,%xmm0
    vmovss %xmm0,0x87320(%r14,%rbx,4)
    inc %rbx
ff_aac_sbr_apply.L90f9_1:
    mov 0x28980(%r14),%eax
    cmp %rax,%rbx
    jae ff_aac_sbr_apply.L99c6
    mov %r12,%rdi
    mov %r15d,%esi
    call *0x88b08(%r14)
ff_aac_sbr_apply.L90f9_2:
    add $0x140,%r12
    cmp $0x30,%rbx
    jne ff_aac_sbr_apply.L90f9
    jmp ff_aac_sbr_apply.L9b95
ff_aac_sbr_apply.L913a:
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x48(%rbp),%rbx
ff_aac_sbr_apply.L9146:
    test %eax,%eax
    je ff_aac_sbr_apply.L98e0
ff_aac_sbr_apply.L914e:
    mov -0x38(%rbp),%rax
    mov 0x74b0c(%rax),%eax
    mov %rax,-0x78(%rbp)
    test %rax,%rax
    je ff_aac_sbr_apply.L98e0
ff_aac_sbr_apply.L914e_1:
    mov -0x38(%rbp),%r10
    mov 0x28978(%r10),%ecx
    movzwl 0x74c12(%r10),%eax
    mov %ax,-0x82(%rbp)
ff_aac_sbr_apply.L914e_2:
    mov -0x98(%rbp),%rax
    add -0x160(%rbp),%rax
    mov %rax,-0x98(%rbp)
    mov %ecx,%eax
    neg %eax
    mov %eax,-0xf4(%rbp)
ff_aac_sbr_apply.L914e_3:
    mov -0x158(%rbp),%rdi
    mov -0x108(%rbp),%r8
    mov -0xd0(%rbp),%r9
    mov -0x100(%rbp),%r11
    xor %r12d,%r12d
    jmp ff_aac_sbr_apply.L91f7
    nop
ff_aac_sbr_apply.L91c0:
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
ff_aac_sbr_apply.L91f7:
    mov 0x3908(%rbx),%eax
    cmp %rax,%r12
    jne ff_aac_sbr_apply.L9206
    xor %edx,%edx
    jmp ff_aac_sbr_apply.L9215
ff_aac_sbr_apply.L9206:
    mov -0x110(%rbp),%rax
    mov (%rax),%eax
    cmp %rax,%r12
    setne %dl
ff_aac_sbr_apply.L9215:
    mov %r12,%rax
    shl $0x6,%rax
    lea (%rax,%rax,2),%rsi
    mov -0xd0(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0x60(%rbp)
ff_aac_sbr_apply.L9215_1:
    mov -0x108(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xe8(%rbp)
ff_aac_sbr_apply.L9215_2:
    mov -0x170(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xe0(%rbp)
ff_aac_sbr_apply.L9215_3:
    mov -0x178(%rbp),%rax
    add %rsi,%rax
    mov %rax,-0xd8(%rbp)
ff_aac_sbr_apply.L9215_4:
    add -0x100(%rbp),%rsi
    mov %rsi,-0x80(%rbp)
    mov %edx,-0x30(%rbp)
    movzbl %dl,%eax
    vcvtsi2ss %eax,%xmm15,%xmm0
ff_aac_sbr_apply.L9215_5:
    movzwl -0x82(%rbp),%eax
    mov %eax,%esi
    xor %edx,%edx
    mov %r12,-0x58(%rbp)
    jmp ff_aac_sbr_apply.L929e
    nop
ff_aac_sbr_apply.L9290:
    cmp -0x78(%rbp),%rdx
    mov -0x48(%rbp),%rbx
    je ff_aac_sbr_apply.L91c0
ff_aac_sbr_apply.L929e:
    cmp $0x1d,%rdx
    je ff_aac_sbr_apply.L99fd
    movzwl %si,%eax
    mov %eax,%r13d
    sub %ecx,%r13d
    mov %rdx,-0x50(%rbp)
    inc %rdx
ff_aac_sbr_apply.L929e_1:
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
ff_aac_sbr_apply.L9300:
    vmovss -0x1f80(%r11,%rax,4),%xmm1
    vmovss -0x1980(%r11,%rax,4),%xmm2
    vaddss %xmm2,%xmm9,%xmm3
    vdivss %xmm3,%xmm1,%xmm4
    vmulss %xmm4,%xmm2,%xmm5
    vsqrtss %xmm5,%xmm5,%xmm5
    vmovss %xmm5,-0xc00(%r11,%rax,4)
ff_aac_sbr_apply.L9300_1:
    movzbl (%r12,%rax,1),%esi
    vcvtsi2ss %esi,%xmm15,%xmm5
    vmulss %xmm5,%xmm4,%xmm4
    vsqrtss %xmm4,%xmm4,%xmm4
    vmovss %xmm4,-0x600(%r11,%rax,4)
ff_aac_sbr_apply.L9300_2:
    cmpb $0x0,0x86c60(%r10,%rax,1)
    je ff_aac_sbr_apply.L9370
    vmulss %xmm2,%xmm1,%xmm1
    vaddss -0x1200(%r11,%rax,4),%xmm9,%xmm2
    vmulss %xmm2,%xmm3,%xmm2
    jmp ff_aac_sbr_apply.L9386
    nop
ff_aac_sbr_apply.L9370:
    vaddss -0x1200(%r11,%rax,4),%xmm9,%xmm3
    vmulss %xmm0,%xmm2,%xmm2
    vaddss %xmm2,%xmm9,%xmm2
    vmulss %xmm3,%xmm2,%xmm2
ff_aac_sbr_apply.L9386:
    vdivss %xmm2,%xmm1,%xmm1
    vsqrtss %xmm1,%xmm1,%xmm1
    vaddss LCPI14_14(%rip),%xmm1,%xmm1
    vmovss %xmm1,(%r11,%rax,4)
    inc %rax
ff_aac_sbr_apply.L9386_1:
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
ff_aac_sbr_apply.L93d0:
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
    jmp ff_aac_sbr_apply.L9530
    nop
ff_aac_sbr_apply.L93f0:
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
ff_aac_sbr_apply.L93f0_1:
    and $0x7,%r12d
    mov %rbx,-0x68(%rbp)
    vxorps %xmm1,%xmm1,%xmm1
    vxorps %xmm2,%xmm2,%xmm2
    je ff_aac_sbr_apply.L9458
    nop
ff_aac_sbr_apply.L9440:
    vaddss (%r9,%rbx,4),%xmm2,%xmm2
    vaddss 0xd80(%r9,%rbx,4),%xmm1,%xmm1
    inc %rbx
    dec %r12
    jne ff_aac_sbr_apply.L9440
ff_aac_sbr_apply.L9458:
    mov -0x68(%rbp),%r12
    sub %r14,%r12
    cmp $0xfffffffffffffff8,%r12
    ja ff_aac_sbr_apply.L9504
    add -0xf4(%rbp),%r15d
ff_aac_sbr_apply.L9470:
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
ff_aac_sbr_apply.L9470_1:
    vaddss 0xd9c(%r9,%rbx,4),%xmm1,%xmm1
    add $0x8,%rbx
    cmp %rbx,%r15
    jne ff_aac_sbr_apply.L9470
ff_aac_sbr_apply.L9504:
    vmovss LCPI14_13(%rip),%xmm3
    vaddss %xmm3,%xmm2,%xmm2
    vaddss %xmm3,%xmm1,%xmm1
    jmp ff_aac_sbr_apply.L952c
    nop
ff_aac_sbr_apply.L9520:
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
ff_aac_sbr_apply.L952c:
    mov -0x58(%rbp),%r12
ff_aac_sbr_apply.L9530:
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
ff_aac_sbr_apply.L9530_1:
    mov %r13d,%eax
    cmp $0x31,%rax
    mov $0x30,%r14d
    cmovae %rax,%r14
    cmp $0x2f,%r13d
    ja ff_aac_sbr_apply.L9a55
    nop
ff_aac_sbr_apply.L95a0:
    vmovss (%r8,%rax,4),%xmm2
    vmulss %xmm2,%xmm1,%xmm3
    vmovss 0xc00(%r8,%rax,4),%xmm4
    vdivss %xmm4,%xmm3,%xmm3
    vminss %xmm2,%xmm3,%xmm2
    vmovss %xmm2,(%r8,%rax,4)
    vminss %xmm4,%xmm1,%xmm2
ff_aac_sbr_apply.L95a0_1:
    vmovss %xmm2,0xc00(%r8,%rax,4)
    inc %rax
ff_aac_sbr_apply.L95a0_2:
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
ff_aac_sbr_apply.L9600:
    mov -0x38(%rbp),%rax
    mov -0x50(%rbp),%r14
    movzwl 0x74c12(%rax,%r14,2),%eax
    mov %eax,%r13d
    sub %ecx,%r13d
ff_aac_sbr_apply.L9617:
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
ff_aac_sbr_apply.L9617_1:
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
ff_aac_sbr_apply.L968d:
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
ff_aac_sbr_apply.L96d3:
    lea -0x1(%r12),%r14
    cmp %rax,%r14
    jne ff_aac_sbr_apply.L97b7
ff_aac_sbr_apply.L96e1:
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
ff_aac_sbr_apply.L9720:
    vcmpeqss %xmm3,%xmm5,%xmm3
    vmovss LCPI14_5(%rip),%xmm7
    vandps %xmm7,%xmm3,%xmm3
ff_aac_sbr_apply.L9731:
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
ff_aac_sbr_apply.L9731_1:
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
ff_aac_sbr_apply.L97b7:
    vmovss -0x604(%rdi,%rbx,4),%xmm4
    vxorps %xmm3,%xmm3,%xmm3
    cmpb $0x0,-0x30(%rbp)
    jne ff_aac_sbr_apply.L97f0
    vxorps %xmm6,%xmm6,%xmm6
    vmovss -0x600(%rdi,%rbx,4),%xmm5
    je ff_aac_sbr_apply.L9731
    jmp ff_aac_sbr_apply.L9720
    nop
ff_aac_sbr_apply.L97f0:
    vcmpeqss %xmm3,%xmm4,%xmm5
    vmovss LCPI14_5(%rip),%xmm6
    vandps %xmm6,%xmm5,%xmm6
    vmovss -0x600(%rdi,%rbx,4),%xmm5
    je ff_aac_sbr_apply.L9731
    jmp ff_aac_sbr_apply.L9720
    nop
ff_aac_sbr_apply.L9820:
    movzwl %si,%eax
    sub %ecx,%eax
    cmp %eax,%r13d
    jae ff_aac_sbr_apply.L9290
    cmp $0x7,%r12
    ja ff_aac_sbr_apply.L9b86
    mov %r13d,%eax
    vmovaps %xmm9,%xmm1
ff_aac_sbr_apply.L983f:
    cmp $0x31,%rax
    mov $0x30,%ebx
    cmovae %rax,%rbx
    cmp $0x2f,%rax
    ja ff_aac_sbr_apply.L9a5a
    nop
ff_aac_sbr_apply.L9860:
    vmulss 0xc00(%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,0xc00(%r8,%rax,4)
ff_aac_sbr_apply.L9860_1:
    vmulss (%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,(%r8,%rax,4)
ff_aac_sbr_apply.L9860_2:
    vmulss 0x600(%r8,%rax,4),%xmm1,%xmm2
    vmovss %xmm2,0x600(%r8,%rax,4)
    inc %rax
ff_aac_sbr_apply.L9860_3:
    mov -0x38(%rbp),%rsi
    movzwl 0x74c12(%rsi,%rdx,2),%esi
    mov %esi,%r14d
    sub %ecx,%r14d
    cmp %r14,%rax
    jae ff_aac_sbr_apply.L9290
    cmp %rax,%rbx
    jne ff_aac_sbr_apply.L9860
    jmp ff_aac_sbr_apply.L9a5a
ff_aac_sbr_apply.L98bc:
    vmovss LCPI14_13(%rip),%xmm1
    vmovaps %xmm1,%xmm2
    cmp %ebx,%r13d
    jae ff_aac_sbr_apply.L9530
    jmp ff_aac_sbr_apply.L9c27
    nop
ff_aac_sbr_apply.L98e0:
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
ff_aac_sbr_apply.L9927:
    mov -0x118(%rbp),%r12
    mov 0x7920(%rbx),%eax
ff_aac_sbr_apply.L9934:
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
ff_aac_sbr_apply.L9934_1:
    imul $0x4c00,%rcx,%rdx
    add %rdi,%rdx
    mov %eax,%eax
    imul $0x4c00,%rax,%rcx
    add %rdi,%rcx
    mov -0xb0(%rbp),%rdi
    mov -0xc0(%rbp),%r8
    mov -0x38(%rbp),%r14
    call *0x88b80(%r14)
ff_aac_sbr_apply.L9934_2:
    mov %r14,%r9
    mov $0x1,%edx
    test %bl,-0xf8(%rbp)
    mov $0x0,%ecx
    jne ff_aac_sbr_apply.L7682
    jmp ff_aac_sbr_apply.L9a02
ff_aac_sbr_apply.L99c6:
    mov -0x48(%rbp),%rax
    mov 0x8(%rax),%ecx
    mov %ecx,%eax
ff_aac_sbr_apply.L99cf:
    cmp $0x9,%ecx
    vmovss LCPI14_5(%rip),%xmm9
    mov -0x48(%rbp),%rbx
    jb ff_aac_sbr_apply.L9146
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L99e9:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L99ee:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L99f3:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L99f8:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L99fd:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a02:
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
ff_aac_sbr_apply.L9a02_1:
    jmp ff_aac_sbr_apply.L9a7d
ff_aac_sbr_apply.L9a50:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a55:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a5a:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a5f:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a64:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9a69:
    mov $0x4c00,%edx
    mov %rax,%rdi
    mov -0xa8(%rbp),%rsi
    call memcpy
ff_aac_sbr_apply.L9a7d:
    mov -0x38(%rbp),%r9
    movb $0x1,-0x39(%rbp)
ff_aac_sbr_apply.L9a85:
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
ff_aac_sbr_apply.L9a85_1:
    call sbr_qmf_synthesis
ff_aac_sbr_apply.L9a85_2:
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
ff_aac_sbr_apply.L9a85_3:
    call sbr_qmf_synthesis
ff_aac_sbr_apply.L9a85_4:
    add $0x1b8,%rsp
    jmp ff_aac_sbr_apply.L9b2b
ff_aac_sbr_apply.L9b24:
    add $0x198,%rsp
ff_aac_sbr_apply.L9b2b:
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
ff_aac_sbr_apply.done:
    ret
ff_aac_sbr_apply.L9b36:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b3b:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b40:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b45:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b4a:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b4f:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b54:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b59:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b5e:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b63:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b68:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b6d:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b72:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b77:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b7c:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b81:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b86:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b8b:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b90:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b95:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9b9a:
    lea L_str_3(%rip),%rdx
    lea L_str_34(%rip),%rcx
    lea L_src_32(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x78,%r9d
    xor %eax,%eax
    call av_log
ff_aac_sbr_apply.L9b9a_1:
    call abort
ff_aac_sbr_apply.L9bc5:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9bca:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9bcf:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9bd4:
    lea L_str_3(%rip),%rdx
    lea L_str_4(%rip),%rcx
    lea L_str_5(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x6c2,%r9d
    xor %eax,%eax
    call av_log
ff_aac_sbr_apply.L9bd4_1:
    call abort
ff_aac_sbr_apply.L9bff:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c04:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c09:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c0e:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c13:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c18:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c1d:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c22:
    ud1 0x12(%eax),%eax
ff_aac_sbr_apply.L9c27:
    ud1 0x12(%eax),%eax
    int3
    int3
    int3
    int3

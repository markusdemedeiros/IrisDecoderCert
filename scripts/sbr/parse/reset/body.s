sbr_reset:
    push %rbp
    mov %rsp,%rbp
    push %r15
sbr_reset.L1086:
    push %r14
    push %r13
sbr_reset.L108a:
    push %r12
    push %rbx
    sub $0x548,%rsp
    mov %rsi,%r12
    mov %rdi,%r15
    mov (%rsi),%ecx
    cmp $0xf9ff,%ecx
    jg sbr_reset.L10d9
    cmp $0x7cff,%ecx
    jg sbr_reset.L10fe
    cmp $0x3e80,%ecx
    je sbr_reset.L17fc
sbr_reset.L10b8:
    cmp $0x5622,%ecx
    je sbr_reset.L1814
    cmp $0x5dc0,%ecx
    jne sbr_reset.L1820
    lea sbr_offset_2(%rip),%rdi
    jmp sbr_reset.L114a
sbr_reset.L10d9:
    cmp $0x1f3ff,%ecx
    jg sbr_reset.L1127
    cmp $0xfa00,%ecx
    je sbr_reset.L111e
    cmp $0x15888,%ecx
    je sbr_reset.L1143
    cmp $0x17700,%ecx
    je sbr_reset.L1143
    jmp sbr_reset.L1820
sbr_reset.L10fe:
    cmp $0x7d00,%ecx
    je sbr_reset.L1808
    cmp $0xac44,%ecx
    je sbr_reset.L111e
    cmp $0xbb80,%ecx
    jne sbr_reset.L1820
sbr_reset.L111e:
    lea sbr_offset_4(%rip),%rdi
    jmp sbr_reset.L114a
sbr_reset.L1127:
    cmp $0x1f400,%ecx
    je sbr_reset.L1143
    cmp $0x2b110,%ecx
    je sbr_reset.L1143
    cmp $0x2ee00,%ecx
    jne sbr_reset.L1820
sbr_reset.L1143:
    lea sbr_offset_5(%rip),%rdi
sbr_reset.L114a:
    cmp $0xfa00,%ecx
    mov $0xfa0,%eax
    mov $0x1388,%edx
    cmovb %eax,%edx
    cmp $0x7d00,%ecx
    mov $0xbb8,%esi
    cmovae %edx,%esi
    mov %esi,%eax
    shl $0x7,%eax
    mov %ecx,%r8d
    shr $1,%r8d
    add %r8d,%eax
sbr_reset.L1179:
    xor %edx,%edx
    div %ecx
sbr_reset.L117d:
    movzbl 0x1c(%r12),%edx
    movsbl (%rdi,%rdx,1),%edx
    add %eax,%edx
    mov %edx,0x40(%r12)
sbr_reset.L118e:
    movzbl 0x1d(%r12),%eax
    cmp $0xd,%eax
    ja sbr_reset.L150a
    mov %r15,-0x40(%rbp)
    shl $0x8,%esi
    add %r8d,%esi
sbr_reset.L11a7:
    mov %esi,%eax
    xor %edx,%edx
    div %ecx
sbr_reset.L11ad:
    mov %eax,%r15d
    mov %r12,-0x30(%rbp)
    mov %eax,0x48(%r12)
    vcvtsi2ss %eax,%xmm15,%xmm1
sbr_reset.L11bd:
    vmovss %xmm1,-0x38(%rbp)
    vmovss LCPI5_0(%rip),%xmm0
    vdivss %xmm1,%xmm0,%xmm0
    vmovss LCPI5_1(%rip),%xmm1
    call powf
sbr_reset.L11db:
    vmulss -0x38(%rbp),%xmm0,%xmm1
    vmulss %xmm1,%xmm0,%xmm2
    vcvtss2si %xmm2,%rax
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%rcx
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%rdx
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%rsi
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%rdi
    vmulss %xmm2,%xmm0,%xmm2
sbr_reset.L1211:
    vcvtss2si %xmm2,%r8
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%r9
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%r11
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%r13
    vmulss %xmm2,%xmm0,%xmm2
    vcvtss2si %xmm2,%r12
    vmulss %xmm2,%xmm0,%xmm0
    vcvtss2si %xmm0,%r14
    mov $0x40,%r10d
sbr_reset.L1249:
    sub %r14d,%r10d
    sub %r12d,%r14d
    sub %r13d,%r12d
    sub %r11d,%r13d
    sub %r9d,%r11d
    sub %r8d,%r9d
    sub %edi,%r8d
    sub %esi,%edi
    sub %edx,%esi
    sub %ecx,%edx
    sub %eax,%ecx
    vcvtss2si %xmm1,%rbx
sbr_reset.L126b:
    sub %ebx,%eax
    sub %r15d,%ebx
    mov %bx,-0x70(%rbp)
    mov %ax,-0x6e(%rbp)
sbr_reset.L1278:
    mov %cx,-0x6c(%rbp)
    mov %dx,-0x6a(%rbp)
sbr_reset.L1280:
    mov %si,-0x68(%rbp)
    mov %di,-0x66(%rbp)
sbr_reset.L1288:
    mov %r8w,-0x64(%rbp)
    mov %r9w,-0x62(%rbp)
sbr_reset.L1292:
    mov %r11w,-0x60(%rbp)
    mov %r13w,-0x5e(%rbp)
sbr_reset.L129c:
    mov %r12w,-0x5c(%rbp)
    mov %r14w,-0x5a(%rbp)
    lea -0x58(%rbp),%rax
sbr_reset.L12aa:
    mov %r10w,-0x58(%rbp)
    lea -0x70(%rbp),%rcx
    mov %rcx,-0x570(%rbp)
sbr_reset.L12ba:
    mov %rax,-0x568(%rbp)
    mov $0x1,%eax
    jmp sbr_reset.L12d8
    nop
sbr_reset.L12d0:
    test %eax,%eax
    je sbr_reset.L1523
sbr_reset.L12d8:
    cmp $0x41,%eax
    jae sbr_reset.L3257
    dec %eax
    mov %rax,%rcx
    shl $0x4,%rcx
    mov -0x570(%rbp,%rcx,1),%rdx
    mov -0x568(%rbp,%rcx,1),%rcx
    nop
sbr_reset.L1300:
    cmp %rcx,%rdx
    jae sbr_reset.L12d0
    lea -0x2(%rcx),%rdi
    cmp %rdi,%rdx
    jae sbr_reset.L14f0
    mov %rcx,%r8
    sub %rdx,%r8
    sar $0x2,%r8
    lea (%rdx,%r8,2),%rsi
    movzwl (%rdx),%r9d
    movzwl (%rcx),%r11d
    movzwl (%rdx,%r8,2),%r8d
sbr_reset.L132d:
    cmp %r11w,%r9w
    jle sbr_reset.L1350
    cmp %r8w,%r11w
    jg sbr_reset.L135c
    mov %r9w,(%rcx)
    mov %r11d,%r8d
    jmp sbr_reset.L1360
    nop
sbr_reset.L1350:
    mov $0x1,%r10d
    cmp %r8w,%r9w
    jle sbr_reset.L136f
sbr_reset.L135c:
    mov %r9w,(%rsi)
sbr_reset.L1360:
    mov %r8w,(%rdx)
    movzwl (%rsi),%r8d
    movzwl (%rcx),%r11d
    xor %r10d,%r10d
sbr_reset.L136f:
    cmp %r11w,%r8w
    jle sbr_reset.L1390
    mov %r8w,(%rcx)
    mov %r11w,(%rsi)
    xor %r10d,%r10d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    jne sbr_reset.L13a0
    jmp sbr_reset.L12d0
    nop
sbr_reset.L1390:
    mov %r8d,%r11d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    je sbr_reset.L12d0
sbr_reset.L13a0:
    lea 0x2(%rdx),%r9
    movzwl (%rdi),%ebx
    mov %bx,(%rsi)
    mov %r11w,(%rdi)
    cmp %r8,%r9
    jbe sbr_reset.L13d9
    jmp sbr_reset.L1424
    nop
sbr_reset.L13c0:
    movzwl (%r9),%r11d
    mov %r11w,(%r8)
    mov %r14w,(%r9)
    add $0x2,%r9
    add $0xfffffffffffffffe,%r8
sbr_reset.L13d4:
    cmp %r8,%r9
    ja sbr_reset.L1420
sbr_reset.L13d9:
    movzwl (%rdi),%r11d
    nop
sbr_reset.L13e0:
    cmp %r11w,(%r9)
    jge sbr_reset.L1404
    add $0x2,%r9
    cmp %r8,%r9
    jbe sbr_reset.L13e0
    jmp sbr_reset.L1404
    nop
sbr_reset.L1400:
    add $0xfffffffffffffffe,%r8
sbr_reset.L1404:
    cmp %r8,%r9
    ja sbr_reset.L13d4
    movzwl (%r8),%r14d
    cmp %r11w,%r14w
    jg sbr_reset.L1400
    jmp sbr_reset.L13c0
    nop
sbr_reset.L1420:
    movzwl (%rdi),%r11d
sbr_reset.L1424:
    movzwl (%r9),%ebx
    mov %r11w,(%r9)
    mov %bx,(%rdi)
    test %r10d,%r10d
    je sbr_reset.L1470
    cmp %r9,%rsi
    je sbr_reset.L1442
    lea -0x2(%r9),%rdi
    cmp %rdi,%rsi
    jne sbr_reset.L1470
sbr_reset.L1442:
    mov %rdx,%rdi
    nop
sbr_reset.L1450:
    mov %rdi,%rsi
    cmp %rcx,%rdi
    jae sbr_reset.L1467
    lea 0x2(%rsi),%rdi
    movzwl (%rsi),%r10d
    cmp 0x2(%rsi),%r10w
    jle sbr_reset.L1450
sbr_reset.L1467:
    cmp %rcx,%rsi
    je sbr_reset.L12d0
sbr_reset.L1470:
    mov %rcx,%rsi
    sub %r9,%rsi
    mov %r9,%rdi
    sub %rdx,%rdi
    cmp %rdi,%rsi
    jge sbr_reset.L14c0
    cmp $0x40,%rax
    jae sbr_reset.L324d
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %rdx,-0x570(%rbp,%rsi,1)
    mov %r8,-0x568(%rbp,%rsi,1)
sbr_reset.L14a2:
    add $0x2,%r9
    mov %r9,%rdx
    inc %rax
    jmp sbr_reset.L1300
    nop
sbr_reset.L14c0:
    cmp $0x40,%rax
    jae sbr_reset.L3252
    add $0x2,%r9
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %r9,-0x570(%rbp,%rsi,1)
    mov %rcx,-0x568(%rbp,%rsi,1)
    mov %r8,%rcx
    inc %rax
    jmp sbr_reset.L1300
sbr_reset.L14f0:
    movzwl (%rdx),%esi
    movzwl (%rcx),%edi
    cmp %di,%si
    jle sbr_reset.L12d0
    mov %si,(%rcx)
    mov %di,(%rdx)
    jmp sbr_reset.L12d0
sbr_reset.L150a:
    cmp $0xf,%eax
    je sbr_reset.L161f
    cmp $0xe,%eax
    jne sbr_reset.L1762
    add %edx,%edx
    jmp sbr_reset.L1622
sbr_reset.L1523:
    mov -0x30(%rbp),%r12
    movzbl 0x1d(%r12),%eax
    test %al,%al
    mov -0x40(%rbp),%r15
    je sbr_reset.L1618
    movswl -0x70(%rbp),%edx
    add 0x48(%r12),%edx
    mov %edx,0x48(%r12)
    cmp $0x1,%al
    je sbr_reset.L1622
    movswl -0x6e(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L1555:
    mov %edx,0x48(%r12)
    cmp $0x3,%al
    jb sbr_reset.L1622
    movswl -0x6c(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0x3,%al
    je sbr_reset.L1622
    movswl -0x6a(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L157b:
    mov %edx,0x48(%r12)
    cmp $0x5,%al
    jb sbr_reset.L1622
    movswl -0x68(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0x5,%al
    je sbr_reset.L1622
    movswl -0x66(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L15a1:
    mov %edx,0x48(%r12)
    cmp $0x7,%al
    jb sbr_reset.L1622
    movswl -0x64(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0x7,%al
    je sbr_reset.L1622
    movswl -0x62(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L15bf:
    mov %edx,0x48(%r12)
    cmp $0x9,%al
    jb sbr_reset.L1622
    movswl -0x60(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0x9,%al
    je sbr_reset.L1622
    movswl -0x5e(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L15dd:
    mov %edx,0x48(%r12)
    cmp $0xb,%al
    jb sbr_reset.L1622
    movswl -0x5c(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0xb,%al
    je sbr_reset.L1622
    movswl -0x5a(%rbp),%ecx
    add %ecx,%edx
sbr_reset.L15fb:
    mov %edx,0x48(%r12)
    cmp $0xd,%al
    jb sbr_reset.L1622
    movswl -0x58(%rbp),%ecx
    add %ecx,%edx
    mov %edx,0x48(%r12)
    cmp $0xd,%al
    je sbr_reset.L1622
    ud1 0x12(%eax),%eax
sbr_reset.L1618:
    mov 0x48(%r12),%edx
    jmp sbr_reset.L1622
sbr_reset.L161f:
    lea (%rdx,%rdx,2),%edx
sbr_reset.L1622:
    cmp $0x40,%edx
    mov $0x40,%esi
    cmovb %edx,%esi
    mov %esi,0x48(%r12)
    mov (%r12),%ecx
    mov $0x30,%eax
    cmp $0x7d01,%ecx
    jl sbr_reset.L1661
    mov $0x23,%eax
    cmp $0xac44,%ecx
    je sbr_reset.L1661
    mov $0x20,%eax
sbr_reset.L1655:
    cmp $0xbb7f,%ecx
    jbe sbr_reset.L328e
sbr_reset.L1661:
    mov 0x40(%r12),%r13d
    mov %esi,%ecx
    sub %r13d,%ecx
    cmp %eax,%ecx
    jbe sbr_reset.L1684
    mov 0x8(%r15),%rdi
    lea L_str_10(%rip),%rdx
sbr_reset.L167a:
    mov $0x10,%esi
    jmp sbr_reset.L1d2a
sbr_reset.L1684:
    movzbl 0x1f(%r12),%eax
    test %eax,%eax
    je sbr_reset.L1779
    mov $0x7,%ecx
    sub %eax,%ecx
    imul $0x31,%esi,%eax
    imul $0x6e,%r13d,%edx
    lea 0x0(,%r13,2),%r14d
    mov %eax,-0x80(%rbp)
    mov %edx,-0x88(%rbp)
    cmp %edx,%eax
    cmovbe %esi,%r14d
sbr_reset.L16b7:
    mov %r14d,0x44(%r12)
    vcvtsi2ss %ecx,%xmm15,%xmm0
    vmovss %xmm0,-0x38(%rbp)
    vcvtsi2ss %r14,%xmm15,%xmm0
    mov %r13d,%eax
    vcvtsi2ss %rax,%xmm15,%xmm1
    vdivss %xmm1,%xmm0,%xmm0
sbr_reset.L16d6:
    call log2f
sbr_reset.L16db:
    vmulss -0x38(%rbp),%xmm0,%xmm0
    vcvtss2si %xmm0,%rax
    mov %rax,-0x50(%rbp)
    lea (%rax,%rax,1),%ecx
    test %ecx,%ecx
    jle sbr_reset.L17e7
    mov %r15,-0x40(%rbp)
sbr_reset.L16f8:
    mov %r12,-0x30(%rbp)
    vcvtsi2ss %r14d,%xmm15,%xmm0
    vcvtsi2ss %r13d,%xmm15,%xmm2
    vcvtsi2ss %ecx,%xmm15,%xmm1
    vblendps $0xe,LCPI5_2(%rip),%xmm0,%xmm0
    movw $0x0,-0x170(%rbp)
sbr_reset.L171d:
    vmovaps %xmm2,-0x100(%rbp)
    vinsertps $0x10,%xmm1,%xmm2,%xmm1
    vdivps %xmm1,%xmm0,%xmm0
    vmovshdup %xmm0,%xmm1
    mov %rcx,%rbx
sbr_reset.L1736:
    call powf
sbr_reset.L173b:
    lea -0x1(%rbx),%eax
    mov %rbx,-0x48(%rbp)
    lea -0x2(%rbx),%edx
    mov %eax,%ecx
    and $0x7,%ecx
    cmp $0x7,%edx
    jae sbr_reset.L1830
    xor %edx,%edx
    vmovaps -0x100(%rbp),%xmm1
    jmp sbr_reset.L1908
sbr_reset.L1762:
    mov 0x8(%r15),%rdi
    lea L_str_8(%rip),%rdx
    mov $0x10,%esi
    mov %eax,%ecx
    jmp sbr_reset.L1d2a
sbr_reset.L1779:
    movzbl 0x20(%r12),%eax
    inc %eax
    mov %eax,%edx
    and $0x2,%edx
    add %ecx,%edx
    mov %eax,%ecx
    shr %cl,%edx
    lea (%rdx,%rdx,1),%ecx
    mov %ecx,0x68(%r12)
    mov 0x8(%r15),%rdi
    test %edx,%edx
    je sbr_reset.L1d0d
sbr_reset.L17a0:
    movzbl 0x1e(%r12),%r8d
    cmp %r8d,%ecx
    jbe sbr_reset.L1d1b
    lea -0x1(%rcx),%edx
    cmp $0x30,%edx
    mov $0x30,%edi
    cmovb %edx,%edi
    cmp $0x30,%edi
    je sbr_reset.L32d2
    mov %ecx,%edx
    mov $0x1,%edi
    cmp $0x8,%ecx
    jb sbr_reset.L1ea8
sbr_reset.L17d6:
    cmp $0x20,%ecx
    jae sbr_reset.L1e09
    xor %r8d,%r8d
    jmp sbr_reset.L1e6b
sbr_reset.L17e7:
    mov 0x8(%r15),%rdi
    lea L_str_11(%rip),%rdx
    mov $0x10,%esi
    jmp sbr_reset.L1d2a
sbr_reset.L17fc:
    lea sbr_offset_0(%rip),%rdi
    jmp sbr_reset.L114a
sbr_reset.L1808:
    lea sbr_offset_3(%rip),%rdi
    jmp sbr_reset.L114a
sbr_reset.L1814:
    lea sbr_offset_1(%rip),%rdi
    jmp sbr_reset.L114a
sbr_reset.L1820:
    mov 0x8(%r15),%rdi
    lea L_str_7(%rip),%rdx
    jmp sbr_reset.L167a
sbr_reset.L1830:
    mov %eax,%esi
    and $0x7ffffff8,%esi
    xor %edx,%edx
    vmovaps -0x100(%rbp),%xmm1
    nop
sbr_reset.L1850:
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%rdi
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r8
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r9
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r10
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r11
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%rbx
sbr_reset.L1886:
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r12
    mov %r12d,%r15d
    sub %ebx,%r15d
    sub %r11d,%ebx
    sub %r10d,%r11d
    sub %r9d,%r10d
    sub %r8d,%r9d
    sub %edi,%r8d
    sub %r13d,%edi
    mov %di,-0x16e(%rbp,%rdx,2)
    mov %r8w,-0x16c(%rbp,%rdx,2)
sbr_reset.L18b8:
    mov %r9w,-0x16a(%rbp,%rdx,2)
    mov %r10w,-0x168(%rbp,%rdx,2)
sbr_reset.L18ca:
    mov %r11w,-0x166(%rbp,%rdx,2)
    mov %bx,-0x164(%rbp,%rdx,2)
sbr_reset.L18db:
    mov %r15w,-0x162(%rbp,%rdx,2)
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r13
    mov %r13d,%edi
    sub %r12d,%edi
    mov %di,-0x160(%rbp,%rdx,2)
    add $0x8,%rdx
    cmp %rdx,%rsi
    jne sbr_reset.L1850
sbr_reset.L1908:
    lea -0x16e(%rbp),%rsi
    lea -0x16e(,%rdx,2),%rdx
    add %rbp,%rdx
    xor %edi,%edi
    nop
sbr_reset.L1920:
    mov %r13d,%r8d
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r13
    mov %r13d,%r9d
    sub %r8d,%r9d
    mov %r9w,(%rdx,%rdi,2)
    inc %rdi
    cmp %rdi,%rcx
    jne sbr_reset.L1920
    sub %r13d,%r14d
    mov %r14w,-0x16e(%rbp,%rax,2)
sbr_reset.L194b:
    mov %rsi,-0x570(%rbp)
    mov -0x48(%rbp),%eax
    lea (%rsi,%rax,2),%rcx
    add $0xfffffffffffffffe,%rcx
    mov %rcx,-0x568(%rbp)
    mov $0x1,%ecx
    mov -0x30(%rbp),%r12
    mov -0x40(%rbp),%r15
    jmp sbr_reset.L1988
    nop
sbr_reset.L1980:
    test %ecx,%ecx
    je sbr_reset.L1bbd
sbr_reset.L1988:
    cmp $0x41,%ecx
    jae sbr_reset.L3266
    dec %ecx
    mov %rcx,%rdx
    shl $0x4,%rdx
    mov -0x570(%rbp,%rdx,1),%rsi
    mov -0x568(%rbp,%rdx,1),%rdx
    nop
sbr_reset.L19b0:
    cmp %rdx,%rsi
    jae sbr_reset.L1980
    lea -0x2(%rdx),%r8
    cmp %r8,%rsi
    jae sbr_reset.L1ba0
    mov %rdx,%r9
    sub %rsi,%r9
    sar $0x2,%r9
    lea (%rsi,%r9,2),%rdi
    movzwl (%rsi),%r10d
    movzwl (%rdx),%r14d
    movzwl (%rsi,%r9,2),%r9d
sbr_reset.L19dd:
    cmp %r14w,%r10w
    jle sbr_reset.L1a00
    cmp %r9w,%r14w
    jg sbr_reset.L1a0c
    mov %r10w,(%rdx)
    mov %r14d,%r9d
    jmp sbr_reset.L1a10
    nop
sbr_reset.L1a00:
    mov $0x1,%r11d
    cmp %r9w,%r10w
    jle sbr_reset.L1a1f
sbr_reset.L1a0c:
    mov %r10w,(%rdi)
sbr_reset.L1a10:
    mov %r9w,(%rsi)
    movzwl (%rdi),%r9d
    movzwl (%rdx),%r14d
    xor %r11d,%r11d
sbr_reset.L1a1f:
    cmp %r14w,%r9w
    jle sbr_reset.L1a40
    mov %r9w,(%rdx)
    mov %r14w,(%rdi)
    xor %r11d,%r11d
    lea -0x4(%rdx),%r9
    cmp %r9,%rsi
    jne sbr_reset.L1a50
    jmp sbr_reset.L1980
    nop
sbr_reset.L1a40:
    mov %r9d,%r14d
    lea -0x4(%rdx),%r9
    cmp %r9,%rsi
    je sbr_reset.L1980
sbr_reset.L1a50:
    lea 0x2(%rsi),%r10
    movzwl (%r8),%ebx
    mov %bx,(%rdi)
    mov %r14w,(%r8)
    cmp %r9,%r10
    jbe sbr_reset.L1a89
    jmp sbr_reset.L1ad4
    nop
sbr_reset.L1a70:
    movzwl (%r10),%ebx
    mov %bx,(%r9)
    mov %r13w,(%r10)
    add $0x2,%r10
    add $0xfffffffffffffffe,%r9
sbr_reset.L1a84:
    cmp %r9,%r10
    ja sbr_reset.L1ad0
sbr_reset.L1a89:
    movzwl (%r8),%r14d
    nop
sbr_reset.L1a90:
    cmp %r14w,(%r10)
    jge sbr_reset.L1ab4
    add $0x2,%r10
    cmp %r9,%r10
    jbe sbr_reset.L1a90
    jmp sbr_reset.L1ab4
    nop
sbr_reset.L1ab0:
    add $0xfffffffffffffffe,%r9
sbr_reset.L1ab4:
    cmp %r9,%r10
    ja sbr_reset.L1a84
    movzwl (%r9),%r13d
    cmp %r14w,%r13w
    jg sbr_reset.L1ab0
    jmp sbr_reset.L1a70
    nop
sbr_reset.L1ad0:
    movzwl (%r8),%r14d
sbr_reset.L1ad4:
    movzwl (%r10),%ebx
    mov %r14w,(%r10)
    mov %bx,(%r8)
    test %r11d,%r11d
    je sbr_reset.L1b20
    cmp %r10,%rdi
    je sbr_reset.L1af3
    lea -0x2(%r10),%r8
    cmp %r8,%rdi
    jne sbr_reset.L1b20
sbr_reset.L1af3:
    mov %rsi,%r8
    nop
sbr_reset.L1b00:
    mov %r8,%rdi
    cmp %rdx,%r8
    jae sbr_reset.L1b17
    lea 0x2(%rdi),%r8
    movzwl (%rdi),%r11d
    cmp 0x2(%rdi),%r11w
    jle sbr_reset.L1b00
sbr_reset.L1b17:
    cmp %rdx,%rdi
    je sbr_reset.L1980
sbr_reset.L1b20:
    mov %rdx,%rdi
    sub %r10,%rdi
    mov %r10,%r8
    sub %rsi,%r8
    cmp %r8,%rdi
    jge sbr_reset.L1b70
    cmp $0x40,%rcx
    jae sbr_reset.L325c
    mov %rcx,%rdi
    shl $0x4,%rdi
    mov %rsi,-0x570(%rbp,%rdi,1)
    mov %r9,-0x568(%rbp,%rdi,1)
sbr_reset.L1b52:
    add $0x2,%r10
    mov %r10,%rsi
    inc %rcx
    jmp sbr_reset.L19b0
    nop
sbr_reset.L1b70:
    cmp $0x40,%rcx
    jae sbr_reset.L3261
    add $0x2,%r10
    mov %rcx,%rdi
    shl $0x4,%rdi
    mov %r10,-0x570(%rbp,%rdi,1)
    mov %rdx,-0x568(%rbp,%rdi,1)
    mov %r9,%rdx
    inc %rcx
    jmp sbr_reset.L19b0
sbr_reset.L1ba0:
    movzwl (%rsi),%edi
    movzwl (%rdx),%r8d
    cmp %r8w,%di
    jle sbr_reset.L1980
    mov %di,(%rdx)
    mov %r8w,(%rsi)
    jmp sbr_reset.L1980
sbr_reset.L1bbd:
    mov -0x48(%rbp),%rcx
    cmp $0x31,%ecx
    jae sbr_reset.L32be
    movswl -0x170(%rbp,%rax,2),%edi
    movzwl 0x40(%r12),%eax
    mov %ax,-0x170(%rbp)
    lea 0x1(%rcx),%esi
    mov -0x50(%rbp),%rax
    add %eax,%eax
    neg %rax
    mov $0x1,%ecx
sbr_reset.L1bf0:
    movswl -0x170(%rbp,%rcx,2),%r8d
    test %r8d,%r8d
    jle sbr_reset.L1cf4
    add -0x172(%rbp,%rcx,2),%r8w
    mov %r8w,-0x170(%rbp,%rcx,2)
    lea (%rax,%rcx,1),%rdx
    inc %rdx
    inc %rcx
    cmp $0x1,%rdx
    jne sbr_reset.L1bf0
    mov -0x88(%rbp),%eax
    cmp %eax,-0x80(%rbp)
    jbe sbr_reset.L1da7
sbr_reset.L1c33:
    mov %edi,-0x50(%rbp)
    mov %rsi,-0x88(%rbp)
    xor %eax,%eax
    cmpb $0x0,0x20(%r12)
    sete %al
    lea LCPI5_3(%rip),%rcx
    vmovss -0x38(%rbp),%xmm0
    vmulss (%rcx,%rax,4),%xmm0,%xmm0
sbr_reset.L1c59:
    vmovss %xmm0,-0x38(%rbp)
    mov 0x44(%r12),%r13d
    mov 0x48(%r12),%r14d
    vcvtsi2ss %r14,%xmm15,%xmm0
    vcvtsi2ss %r13,%xmm15,%xmm1
    vdivss %xmm1,%xmm0,%xmm0
sbr_reset.L1c76:
    call log2f
sbr_reset.L1c7b:
    vmulss -0x38(%rbp),%xmm0,%xmm0
    vcvtss2si %xmm0,%r15
    lea (%r15,%r15,1),%ebx
    vcvtsi2ss %r14d,%xmm15,%xmm0
    vmovd %r13d,%xmm1
    vpinsrd $0x1,%ebx,%xmm1,%xmm1
    vcvtdq2ps %xmm1,%xmm1
    vblendps $0xe,LCPI5_2(%rip),%xmm0,%xmm0
    vmovaps %xmm1,-0x80(%rbp)
    vdivps %xmm1,%xmm0,%xmm0
    vmovshdup %xmm0,%xmm1
sbr_reset.L1cb4:
    call powf
sbr_reset.L1cb9:
    lea -0x1(,%r15,2),%eax
    cmp $0x2,%ebx
    jl sbr_reset.L1de3
    mov %eax,%eax
    mov %rbx,-0x38(%rbp)
    lea -0x2(%rbx),%edx
    mov %eax,%ecx
    and $0x7,%ecx
    cmp $0x7,%edx
    mov %rax,-0x100(%rbp)
    jae sbr_reset.L2112
    xor %edx,%edx
sbr_reset.L1cea:
    vmovaps -0x80(%rbp),%xmm1
    jmp sbr_reset.L21e6
sbr_reset.L1cf4:
    mov 0x8(%r15),%rdi
    lea L_str_12(%rip),%rdx
sbr_reset.L1cff:
    mov $0x10,%esi
    xor %eax,%eax
    call av_log
sbr_reset.L1d0b:
    jmp sbr_reset.L1d31
sbr_reset.L1d0d:
    lea L_str_14(%rip),%rdx
    mov $0x10,%esi
    jmp sbr_reset.L1d2a
sbr_reset.L1d1b:
    lea L_str_15(%rip),%rdx
    mov $0x10,%esi
    mov %r8d,%ecx
sbr_reset.L1d2a:
    xor %eax,%eax
    call av_log
sbr_reset.L1d31:
    lea 0x1c(%r12),%rbx
    mov 0x8(%r15),%rdi
    lea L_str_6(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
sbr_reset.L1d48:
    call av_log
sbr_reset.L1d4d:
    movq $0x0,0x4(%r12)
    movl $0x0,0x10(%r12)
sbr_reset.L1d5f:
    movl $0x20,0x58(%r12)
    movl $0x0,0x60(%r12)
sbr_reset.L1d71:
    movl $0xffffffff,0x19448(%r12)
    movl $0xffffffff,0x3988(%r12)
sbr_reset.L1d89:
    movw $0xffff,0x4(%rbx)
    movl $0xffffffff,(%rbx)
sbr_reset.L1d95:
    add $0x548,%rsp
    pop %rbx
    pop %r12
    pop %r13
    pop %r14
    pop %r15
    pop %rbp
sbr_reset.done:
    ret
sbr_reset.L1da7:
    mov -0x48(%rbp),%r13
    mov %r13d,0x68(%r12)
    movzbl 0x1e(%r12),%r14d
    movzbl %r14b,%ecx
    cmp %ecx,%r13d
    jbe sbr_reset.L1e00
    lea 0x4c1f0(%r12),%rdi
    mov -0x50(%rbp),%rdx
    shl $0x2,%edx
    or $0x2,%rdx
    lea -0x170(%rbp),%rsi
sbr_reset.L1dd9:
    call memcpy
sbr_reset.L1dde:
    jmp sbr_reset.L2012
sbr_reset.L1de3:
    sub %r13d,%r14d
    cltq
    mov %r14w,-0xee(%rbp,%rax,2)
    movswl -0xee(%rbp),%edi
    mov %rbx,%r13
    jmp sbr_reset.L2357
sbr_reset.L1e00:
    mov 0x8(%r15),%rdi
    jmp sbr_reset.L29ad
sbr_reset.L1e09:
    mov %edx,%r8d
    and $0xffffffe0,%r8d
    lea 0x1(%r8),%rdi
    vmovd %eax,%xmm0
    vpshufb LCPI5_4(%rip),%xmm0,%xmm0
    xor %r9d,%r9d
    nop
sbr_reset.L1e30:
    vmovdqu %xmm0,0x4c1f2(%r12,%r9,2)
    vmovdqu %xmm0,0x4c202(%r12,%r9,2)
sbr_reset.L1e44:
    vmovdqu %xmm0,0x4c212(%r12,%r9,2)
    vmovdqu %xmm0,0x4c222(%r12,%r9,2)
    add $0x20,%r9
    cmp %r9,%r8
    jne sbr_reset.L1e30
    cmp %edx,%r8d
    je sbr_reset.L1ec1
    test $0x18,%dl
    je sbr_reset.L1ea8
sbr_reset.L1e6b:
    mov %edx,%r9d
    and $0xfffffff8,%r9d
    lea 0x1(%r9),%rdi
    vmovd %eax,%xmm0
    vpshufb LCPI5_4(%rip),%xmm0,%xmm0
    nop
sbr_reset.L1e90:
    vmovdqu %xmm0,0x4c1f2(%r12,%r8,2)
    add $0x8,%r8
    cmp %r8,%r9
    jne sbr_reset.L1e90
    cmp %edx,%r9d
    je sbr_reset.L1ec1
sbr_reset.L1ea8:
    lea 0x1(%rdx),%r8
    nop
sbr_reset.L1eb0:
    mov %ax,0x4c1f0(%r12,%rdi,2)
    inc %rdi
    cmp %rdi,%r8
    jne sbr_reset.L1eb0
sbr_reset.L1ec1:
    imul %ecx,%eax
    add %r13d,%eax
    sub %eax,%esi
    js sbr_reset.L1ed8
    je sbr_reset.L1f08
    incw 0x4c1f0(%r12,%rdx,2)
    jmp sbr_reset.L1f08
sbr_reset.L1ed8:
    xor %eax,%eax
    cmp $0xffffffff,%esi
    setne %al
    neg %eax
    vbroadcastss LCPI5_8(%rip),%xmm0
    vpinsrw $0x1,%eax,%xmm0,%xmm0
    vmovd 0x4c1f2(%r12),%xmm1
    vpaddw %xmm0,%xmm1,%xmm0
    vmovd %xmm0,0x4c1f2(%r12)
sbr_reset.L1f08:
    mov %r13w,0x4c1f0(%r12)
    mov $0x1,%eax
    cmp $0x8,%ecx
    jb sbr_reset.L1fd5
    mov %edx,%ecx
    and $0xfffffff8,%ecx
    xor %eax,%eax
    nop
sbr_reset.L1f30:
    add 0x4c1f2(%r12,%rax,2),%r13w
    mov %r13w,0x4c1f2(%r12,%rax,2)
    add 0x4c1f4(%r12,%rax,2),%r13w
    mov %r13w,0x4c1f4(%r12,%rax,2)
    add 0x4c1f6(%r12,%rax,2),%r13w
sbr_reset.L1f5d:
    mov %r13w,0x4c1f6(%r12,%rax,2)
    add 0x4c1f8(%r12,%rax,2),%r13w
    mov %r13w,0x4c1f8(%r12,%rax,2)
    add 0x4c1fa(%r12,%rax,2),%r13w
sbr_reset.L1f81:
    mov %r13w,0x4c1fa(%r12,%rax,2)
    add 0x4c1fc(%r12,%rax,2),%r13w
    mov %r13w,0x4c1fc(%r12,%rax,2)
    add 0x4c1fe(%r12,%rax,2),%r13w
sbr_reset.L1fa5:
    mov %r13w,0x4c1fe(%r12,%rax,2)
    add 0x4c200(%r12,%rax,2),%r13w
    mov %r13w,0x4c200(%r12,%rax,2)
    add $0x8,%rax
    cmp %rax,%rcx
    jne sbr_reset.L1f30
    test $0x6,%dl
    je sbr_reset.L2003
    inc %rax
sbr_reset.L1fd5:
    lea (%r12,%rax,2),%rax
    add $0x4c1f0,%rax
    lea (%rdx,%rdx,1),%ecx
    and $0xc,%ecx
    xor %edx,%edx
    nop
sbr_reset.L1ff0:
    add (%rax,%rdx,1),%r13w
    mov %r13w,(%rax,%rdx,1)
    add $0x2,%rdx
    cmp %rdx,%rcx
    jne sbr_reset.L1ff0
sbr_reset.L2003:
    mov %r15,-0x40(%rbp)
    mov 0x68(%r12),%r13d
    movzbl 0x1e(%r12),%r14d
sbr_reset.L2012:
    movzbl %r14b,%eax
    mov %r13,-0x38(%rbp)
    sub %eax,%r13d
    mov %r13d,0x4c1e4(%r12)
    mov %r12,%rbx
    lea 0x1(%r13),%r12d
    mov %r12d,%r15d
    shr $1,%r15d
sbr_reset.L2032:
    mov %r15d,0x4c1e0(%rbx)
    cmp $0x32,%al
    jae sbr_reset.L32c8
    lea 0x4c284(%rbx),%rdi
    lea (%rbx,%rax,2),%rsi
    add $0x4c1f0,%rsi
    mov %r12d,%edx
    add %rdx,%rdx
sbr_reset.L2059:
    call memcpy
sbr_reset.L205e:
    cmp $0x31,%r13d
    jae sbr_reset.L32cd
    mov %r13d,%eax
    movzwl 0x4c284(%rbx,%rax,2),%ecx
    movzwl 0x4c284(%rbx),%r14d
    movzwl %r14w,%r10d
    mov %ecx,%eax
    sub %r10d,%eax
    mov %eax,0x60(%rbx)
    mov %rbx,-0x30(%rbp)
sbr_reset.L208b:
    mov %r10d,0x58(%rbx)
    cmp $0x41,%ecx
    jb sbr_reset.L20aa
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_16(%rip),%rdx
    mov $0x10,%esi
    jmp sbr_reset.L20c8
sbr_reset.L20aa:
    cmp $0x21,%r14w
    jb sbr_reset.L20d8
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_17(%rip),%rdx
    mov $0x10,%esi
    mov %r10d,%ecx
sbr_reset.L20c8:
    xor %eax,%eax
    call av_log
sbr_reset.L20cf:
    mov -0x30(%rbp),%r12
    jmp sbr_reset.L1d31
sbr_reset.L20d8:
    mov -0x30(%rbp),%rax
    mov %r14w,0x4c252(%rax)
    test %r15d,%r15d
    je sbr_reset.L2b30
    and $0x1,%r13d
    mov $0x1,%eax
    cmp $0xa,%r12d
    jb sbr_reset.L2aef
    cmp $0x22,%r12d
    jae sbr_reset.L29f4
    xor %r9d,%r9d
    jmp sbr_reset.L2a85
sbr_reset.L2112:
    mov %rax,%rsi
    and $0x7ffffff8,%esi
    xor %edx,%edx
    vmovaps -0x80(%rbp),%xmm1
    nop
sbr_reset.L2130:
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%rdi
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r8
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r9
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r10
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r11
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%rbx
sbr_reset.L2166:
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r12
    mov %r12d,%eax
    sub %ebx,%eax
    sub %r11d,%ebx
    sub %r10d,%r11d
    sub %r9d,%r10d
    sub %r8d,%r9d
    sub %edi,%r8d
    sub %r13d,%edi
    mov %di,-0xee(%rbp,%rdx,2)
    mov %r8w,-0xec(%rbp,%rdx,2)
sbr_reset.L2197:
    mov %r9w,-0xea(%rbp,%rdx,2)
    mov %r10w,-0xe8(%rbp,%rdx,2)
sbr_reset.L21a9:
    mov %r11w,-0xe6(%rbp,%rdx,2)
    mov %bx,-0xe4(%rbp,%rdx,2)
sbr_reset.L21ba:
    mov %ax,-0xe2(%rbp,%rdx,2)
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r13
    mov %r13d,%eax
    sub %r12d,%eax
    mov %ax,-0xe0(%rbp,%rdx,2)
    add $0x8,%rdx
    cmp %rdx,%rsi
    jne sbr_reset.L2130
sbr_reset.L21e6:
    lea -0xee(,%rdx,2),%rdx
    add %rbp,%rdx
    xor %esi,%esi
    nop
sbr_reset.L2200:
    mov %r13d,%eax
    vmulss %xmm1,%xmm0,%xmm1
    vcvtss2si %xmm1,%r13
    mov %r13d,%edi
    sub %eax,%edi
    mov %di,(%rdx,%rsi,2)
    inc %rsi
    cmp %rsi,%rcx
    jne sbr_reset.L2200
    sub %r13d,%r14d
    mov -0x100(%rbp),%rax
    mov %r14w,-0xee(%rbp,%rax,2)
sbr_reset.L2230:
    movswl -0xee(%rbp),%edi
    mov -0x38(%rbp),%r13
    mov %r13d,%eax
    mov $0x1,%ecx
    cmp $0x5,%r13d
    jae sbr_reset.L2252
    mov -0x30(%rbp),%r12
    jmp sbr_reset.L2340
sbr_reset.L2252:
    lea -0x1(%rax),%rdx
    cmp $0x11,%r13d
    mov -0x30(%rbp),%r12
    jae sbr_reset.L2267
    xor %esi,%esi
    jmp sbr_reset.L22fa
sbr_reset.L2267:
    mov %rdx,%rsi
    and $0xfffffffffffffff0,%rsi
    lea 0x1(%rsi),%rcx
    vmovd %edi,%xmm0
    vpshufd $0x0,%xmm0,%xmm0
    xor %edi,%edi
    vmovdqa %xmm0,%xmm1
    vmovdqa %xmm0,%xmm2
    vmovdqa %xmm0,%xmm3
sbr_reset.L2289:
    vpmovsxwd -0xec(%rbp,%rdi,2),%xmm4
    vpminsd %xmm4,%xmm0,%xmm0
    vpmovsxwd -0xe4(%rbp,%rdi,2),%xmm4
    vpminsd %xmm4,%xmm1,%xmm1
    vpmovsxwd -0xdc(%rbp,%rdi,2),%xmm4
    vpmovsxwd -0xd4(%rbp,%rdi,2),%xmm5
    vpminsd %xmm4,%xmm2,%xmm2
    vpminsd %xmm5,%xmm3,%xmm3
    add $0x10,%rdi
    cmp %rdi,%rsi
    jne sbr_reset.L2289
    vpminsd %xmm1,%xmm0,%xmm0
sbr_reset.L22d3:
    vpminsd %xmm3,%xmm2,%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    vpshufd $0xee,%xmm0,%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    vpshufd $0x55,%xmm0,%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    vmovd %xmm0,%edi
    test $0xc,%dl
    je sbr_reset.L2340
sbr_reset.L22fa:
    and $0xfffffffffffffffc,%rdx
    lea 0x1(%rdx),%rcx
    vmovd %edi,%xmm0
    vpshufd $0x0,%xmm0,%xmm0
    nop
sbr_reset.L2310:
    vpmovsxwd -0xec(%rbp,%rsi,2),%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    add $0x4,%rsi
    cmp %rsi,%rdx
    jne sbr_reset.L2310
    vpshufd $0xee,%xmm0,%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    vpshufd $0x55,%xmm0,%xmm1
    vpminsd %xmm1,%xmm0,%xmm0
    vmovd %xmm0,%edi
sbr_reset.L2340:
    mov %edi,%edx
    movswl -0xee(%rbp,%rcx,2),%edi
    cmp %edi,%edx
    cmovl %edx,%edi
    inc %rcx
    cmp %rcx,%rax
    jne sbr_reset.L2340
sbr_reset.L2357:
    lea -0xee(%rbp),%rax
    cmp -0x50(%rbp),%edi
    jge sbr_reset.L25ca
    mov %rax,-0x570(%rbp)
    movslq %r13d,%rcx
    mov %rcx,-0x30(%rbp)
    lea (%rax,%rcx,2),%rax
    add $0xfffffffffffffffe,%rax
sbr_reset.L237d:
    mov %rax,-0x568(%rbp)
    mov $0x1,%eax
    jmp sbr_reset.L2398
    nop
sbr_reset.L2390:
    test %eax,%eax
    je sbr_reset.L25cf
sbr_reset.L2398:
    cmp $0x41,%eax
    jae sbr_reset.L3289
    dec %eax
    mov %rax,%rcx
    shl $0x4,%rcx
    mov -0x570(%rbp,%rcx,1),%rdx
    mov -0x568(%rbp,%rcx,1),%rcx
    nop
sbr_reset.L23c0:
    cmp %rcx,%rdx
    jae sbr_reset.L2390
    lea -0x2(%rcx),%rdi
    cmp %rdi,%rdx
    jae sbr_reset.L25b0
    mov %rcx,%r8
    sub %rdx,%r8
    sar $0x2,%r8
    lea (%rdx,%r8,2),%rsi
    movzwl (%rdx),%r9d
    movzwl (%rcx),%r11d
    movzwl (%rdx,%r8,2),%r8d
sbr_reset.L23ed:
    cmp %r11w,%r9w
    jle sbr_reset.L2410
    cmp %r8w,%r11w
    jg sbr_reset.L241c
    mov %r9w,(%rcx)
    mov %r11d,%r8d
    jmp sbr_reset.L2420
    nop
sbr_reset.L2410:
    mov $0x1,%r10d
    cmp %r8w,%r9w
    jle sbr_reset.L242f
sbr_reset.L241c:
    mov %r9w,(%rsi)
sbr_reset.L2420:
    mov %r8w,(%rdx)
    movzwl (%rsi),%r8d
    movzwl (%rcx),%r11d
    xor %r10d,%r10d
sbr_reset.L242f:
    cmp %r11w,%r8w
    jle sbr_reset.L2450
    mov %r8w,(%rcx)
    mov %r11w,(%rsi)
    xor %r10d,%r10d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    jne sbr_reset.L2460
    jmp sbr_reset.L2390
    nop
sbr_reset.L2450:
    mov %r8d,%r11d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    je sbr_reset.L2390
sbr_reset.L2460:
    lea 0x2(%rdx),%r9
    movzwl (%rdi),%ebx
    mov %bx,(%rsi)
    mov %r11w,(%rdi)
    cmp %r8,%r9
    jbe sbr_reset.L2499
    jmp sbr_reset.L24e4
    nop
sbr_reset.L2480:
    movzwl (%r9),%r11d
    mov %r11w,(%r8)
    mov %r14w,(%r9)
    add $0x2,%r9
    add $0xfffffffffffffffe,%r8
sbr_reset.L2494:
    cmp %r8,%r9
    ja sbr_reset.L24e0
sbr_reset.L2499:
    movzwl (%rdi),%r11d
    nop
sbr_reset.L24a0:
    cmp %r11w,(%r9)
    jge sbr_reset.L24c4
    add $0x2,%r9
    cmp %r8,%r9
    jbe sbr_reset.L24a0
    jmp sbr_reset.L24c4
    nop
sbr_reset.L24c0:
    add $0xfffffffffffffffe,%r8
sbr_reset.L24c4:
    cmp %r8,%r9
    ja sbr_reset.L2494
    movzwl (%r8),%r14d
    cmp %r11w,%r14w
    jg sbr_reset.L24c0
    jmp sbr_reset.L2480
    nop
sbr_reset.L24e0:
    movzwl (%rdi),%r11d
sbr_reset.L24e4:
    movzwl (%r9),%ebx
    mov %r11w,(%r9)
    mov %bx,(%rdi)
    test %r10d,%r10d
    je sbr_reset.L2530
    cmp %r9,%rsi
    je sbr_reset.L2502
    lea -0x2(%r9),%rdi
    cmp %rdi,%rsi
    jne sbr_reset.L2530
sbr_reset.L2502:
    mov %rdx,%rdi
    nop
sbr_reset.L2510:
    mov %rdi,%rsi
    cmp %rcx,%rdi
    jae sbr_reset.L2527
    lea 0x2(%rsi),%rdi
    movzwl (%rsi),%r10d
    cmp 0x2(%rsi),%r10w
    jle sbr_reset.L2510
sbr_reset.L2527:
    cmp %rcx,%rsi
    je sbr_reset.L2390
sbr_reset.L2530:
    mov %rcx,%rsi
    sub %r9,%rsi
    mov %r9,%rdi
    sub %rdx,%rdi
    cmp %rdi,%rsi
    jge sbr_reset.L2580
    cmp $0x40,%rax
    jae sbr_reset.L327a
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %rdx,-0x570(%rbp,%rsi,1)
    mov %r8,-0x568(%rbp,%rsi,1)
sbr_reset.L2562:
    add $0x2,%r9
    mov %r9,%rdx
    inc %rax
    jmp sbr_reset.L23c0
    nop
sbr_reset.L2580:
    cmp $0x40,%rax
    jae sbr_reset.L327f
    add $0x2,%r9
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %r9,-0x570(%rbp,%rsi,1)
    mov %rcx,-0x568(%rbp,%rsi,1)
    mov %r8,%rcx
    inc %rax
    jmp sbr_reset.L23c0
sbr_reset.L25b0:
    movzwl (%rdx),%esi
    movzwl (%rcx),%edi
    cmp %di,%si
    jle sbr_reset.L2390
    mov %si,(%rcx)
    mov %di,(%rdx)
    jmp sbr_reset.L2390
sbr_reset.L25ca:
    movslq %r13d,%rcx
    jmp sbr_reset.L2619
sbr_reset.L25cf:
    cmp $0x31,%r13d
    jae sbr_reset.L32d7
    movswl -0xee(%rbp),%eax
    mov -0x50(%rbp),%edi
    sub %eax,%edi
    mov -0x30(%rbp),%rsi
    movswl -0xf0(%rbp,%rsi,2),%ecx
    mov %ecx,%edx
    sub %eax,%edx
    sar $1,%edx
    cmp %edx,%edi
    cmovl %edi,%edx
sbr_reset.L25fc:
    add %edx,%eax
    mov %ax,-0xee(%rbp)
    sub %edx,%ecx
    mov %cx,-0xf0(%rbp,%rsi,2)
    mov %rsi,%rcx
    lea -0xee(%rbp),%rax
sbr_reset.L2619:
    mov %rax,-0x570(%rbp)
    mov %rcx,-0x30(%rbp)
    lea (%rax,%rcx,2),%rax
    add $0xfffffffffffffffe,%rax
sbr_reset.L262c:
    mov %rax,-0x568(%rbp)
    mov $0x1,%eax
    jmp sbr_reset.L2648
    nop
sbr_reset.L2640:
    test %eax,%eax
    je sbr_reset.L287a
sbr_reset.L2648:
    cmp $0x41,%eax
    jae sbr_reset.L3284
    dec %eax
    mov %rax,%rcx
    shl $0x4,%rcx
    mov -0x570(%rbp,%rcx,1),%rdx
    mov -0x568(%rbp,%rcx,1),%rcx
    nop
sbr_reset.L2670:
    cmp %rcx,%rdx
    jae sbr_reset.L2640
    lea -0x2(%rcx),%rdi
    cmp %rdi,%rdx
    jae sbr_reset.L2860
    mov %rcx,%r8
    sub %rdx,%r8
    sar $0x2,%r8
    lea (%rdx,%r8,2),%rsi
    movzwl (%rdx),%r9d
    movzwl (%rcx),%r11d
    movzwl (%rdx,%r8,2),%r8d
sbr_reset.L269d:
    cmp %r11w,%r9w
    jle sbr_reset.L26c0
    cmp %r8w,%r11w
    jg sbr_reset.L26cc
    mov %r9w,(%rcx)
    mov %r11d,%r8d
    jmp sbr_reset.L26d0
    nop
sbr_reset.L26c0:
    mov $0x1,%r10d
    cmp %r8w,%r9w
    jle sbr_reset.L26df
sbr_reset.L26cc:
    mov %r9w,(%rsi)
sbr_reset.L26d0:
    mov %r8w,(%rdx)
    movzwl (%rsi),%r8d
    movzwl (%rcx),%r11d
    xor %r10d,%r10d
sbr_reset.L26df:
    cmp %r11w,%r8w
    jle sbr_reset.L2700
    mov %r8w,(%rcx)
    mov %r11w,(%rsi)
    xor %r10d,%r10d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    jne sbr_reset.L2710
    jmp sbr_reset.L2640
    nop
sbr_reset.L2700:
    mov %r8d,%r11d
    lea -0x4(%rcx),%r8
    cmp %r8,%rdx
    je sbr_reset.L2640
sbr_reset.L2710:
    lea 0x2(%rdx),%r9
    movzwl (%rdi),%ebx
    mov %bx,(%rsi)
    mov %r11w,(%rdi)
    cmp %r8,%r9
    jbe sbr_reset.L2749
    jmp sbr_reset.L2794
    nop
sbr_reset.L2730:
    movzwl (%r9),%r11d
    mov %r11w,(%r8)
    mov %r14w,(%r9)
    add $0x2,%r9
    add $0xfffffffffffffffe,%r8
sbr_reset.L2744:
    cmp %r8,%r9
    ja sbr_reset.L2790
sbr_reset.L2749:
    movzwl (%rdi),%r11d
    nop
sbr_reset.L2750:
    cmp %r11w,(%r9)
    jge sbr_reset.L2774
    add $0x2,%r9
    cmp %r8,%r9
    jbe sbr_reset.L2750
    jmp sbr_reset.L2774
    nop
sbr_reset.L2770:
    add $0xfffffffffffffffe,%r8
sbr_reset.L2774:
    cmp %r8,%r9
    ja sbr_reset.L2744
    movzwl (%r8),%r14d
    cmp %r11w,%r14w
    jg sbr_reset.L2770
    jmp sbr_reset.L2730
    nop
sbr_reset.L2790:
    movzwl (%rdi),%r11d
sbr_reset.L2794:
    movzwl (%r9),%ebx
    mov %r11w,(%r9)
    mov %bx,(%rdi)
    test %r10d,%r10d
    je sbr_reset.L27e0
    cmp %r9,%rsi
    je sbr_reset.L27b2
    lea -0x2(%r9),%rdi
    cmp %rdi,%rsi
    jne sbr_reset.L27e0
sbr_reset.L27b2:
    mov %rdx,%rdi
    nop
sbr_reset.L27c0:
    mov %rdi,%rsi
    cmp %rcx,%rdi
    jae sbr_reset.L27d7
    lea 0x2(%rsi),%rdi
    movzwl (%rsi),%r10d
    cmp 0x2(%rsi),%r10w
    jle sbr_reset.L27c0
sbr_reset.L27d7:
    cmp %rcx,%rsi
    je sbr_reset.L2640
sbr_reset.L27e0:
    mov %rcx,%rsi
    sub %r9,%rsi
    mov %r9,%rdi
    sub %rdx,%rdi
    cmp %rdi,%rsi
    jge sbr_reset.L2830
    cmp $0x40,%rax
    jae sbr_reset.L3270
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %rdx,-0x570(%rbp,%rsi,1)
    mov %r8,-0x568(%rbp,%rsi,1)
sbr_reset.L2812:
    add $0x2,%r9
    mov %r9,%rdx
    inc %rax
    jmp sbr_reset.L2670
    nop
sbr_reset.L2830:
    cmp $0x40,%rax
    jae sbr_reset.L3275
    add $0x2,%r9
    mov %rax,%rsi
    shl $0x4,%rsi
    mov %r9,-0x570(%rbp,%rsi,1)
    mov %rcx,-0x568(%rbp,%rsi,1)
    mov %r8,%rcx
    inc %rax
    jmp sbr_reset.L2670
sbr_reset.L2860:
    movzwl (%rdx),%esi
    movzwl (%rcx),%edi
    cmp %di,%si
    jle sbr_reset.L2640
    mov %si,(%rcx)
    mov %di,(%rdx)
    jmp sbr_reset.L2640
sbr_reset.L287a:
    movzwl 0x44(%r12),%eax
    mov %ax,-0xf0(%rbp)
    test %r13d,%r13d
    jle sbr_reset.L2949
    add %r15d,%r15d
    neg %r15
    mov $0x4,%ecx
sbr_reset.L289b:
    cmp $0x34,%rcx
    je sbr_reset.L32c3
    movzwl -0xf6(%rbp,%rcx,2),%eax
    test %ax,%ax
    jle sbr_reset.L29cd
    add -0xf8(%rbp,%rcx,2),%ax
    mov %ax,-0xf6(%rbp,%rcx,2)
    movzwl -0xf4(%rbp,%rcx,2),%eax
    test %ax,%ax
    jle sbr_reset.L29d3
    add -0xf6(%rbp,%rcx,2),%ax
    mov %ax,-0xf4(%rbp,%rcx,2)
sbr_reset.L28e7:
    lea (%r15,%rcx,1),%rax
    cmp $0x2,%rax
    je sbr_reset.L2949
    movzwl -0xf2(%rbp,%rcx,2),%eax
    test %ax,%ax
    jle sbr_reset.L29d9
    add -0xf4(%rbp,%rcx,2),%ax
    mov %ax,-0xf2(%rbp,%rcx,2)
    movzwl -0xf0(%rbp,%rcx,2),%eax
    test %ax,%ax
    jle sbr_reset.L29dc
    add -0xf2(%rbp,%rcx,2),%ax
sbr_reset.L292b:
    mov %ax,-0xf0(%rbp,%rcx,2)
    lea (%r15,%rcx,1),%rax
    add $0x4,%rax
    add $0x4,%rcx
    cmp $0x4,%rax
    jne sbr_reset.L289b
sbr_reset.L2949:
    add -0x48(%rbp),%r13d
    mov %r13d,0x68(%r12)
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    jle sbr_reset.L29b9
    movzbl 0x1e(%r12),%r14d
    movzbl %r14b,%ecx
    cmp %ecx,%r13d
    jbe sbr_reset.L29ad
    lea 0x4c1f0(%r12),%rdi
    mov -0x88(%rbp),%rbx
    lea (%rbx,%rbx,1),%rdx
sbr_reset.L297e:
    lea -0x170(%rbp),%rsi
    call memcpy
sbr_reset.L298a:
    lea (%r12,%rbx,2),%rdi
    add $0x4c1f0,%rdi
    mov -0x30(%rbp),%rdx
    add %rdx,%rdx
    lea -0xee(%rbp),%rsi
sbr_reset.L29a3:
    call memcpy
sbr_reset.L29a8:
    jmp sbr_reset.L2012
sbr_reset.L29ad:
    lea L_str_15(%rip),%rdx
    jmp sbr_reset.L167a
sbr_reset.L29b9:
    lea L_str_14(%rip),%rdx
    mov $0x10,%esi
    mov %r13d,%ecx
    jmp sbr_reset.L1d2a
sbr_reset.L29cd:
    add $0xfffffffffffffffd,%rcx
    jmp sbr_reset.L29dc
sbr_reset.L29d3:
    add $0xfffffffffffffffe,%rcx
    jmp sbr_reset.L29dc
sbr_reset.L29d9:
    dec %rcx
sbr_reset.L29dc:
    movswl %ax,%r8d
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_13(%rip),%rdx
    jmp sbr_reset.L1cff
sbr_reset.L29f4:
    mov %r15d,%eax
    and $0xf,%eax
    mov $0x10,%edx
    cmovne %rax,%rdx
    mov %r15,%r9
    sub %rdx,%r9
    lea 0x1(%r9),%rax
    lea 0x0(,%r13,2),%edi
    mov -0x30(%rbp),%r8
    mov %r8,%rsi
    sub %rdi,%rsi
    add $0x4c2b8,%rsi
sbr_reset.L2a26:
    xor %edi,%edi
    vmovdqa LCPI5_6(%rip),%xmm0
sbr_reset.L2a30:
    vmovdqu -0x30(%rsi,%rdi,4),%xmm1
    vmovdqu -0x20(%rsi,%rdi,4),%xmm2
    vmovdqu -0x10(%rsi,%rdi,4),%xmm3
    vmovdqu (%rsi,%rdi,4),%xmm4
    vpshufb %xmm0,%xmm1,%xmm1
    vpshufb %xmm0,%xmm2,%xmm2
    vpunpcklqdq %xmm2,%xmm1,%xmm1
    vmovdqu %xmm1,0x4c254(%r8,%rdi,2)
    vpshufb %xmm0,%xmm3,%xmm1
    vpshufb %xmm0,%xmm4,%xmm2
    vpunpcklqdq %xmm2,%xmm1,%xmm1
    vmovdqu %xmm1,0x4c264(%r8,%rdi,2)
sbr_reset.L2a77:
    add $0x10,%rdi
    cmp %rdi,%r9
    jne sbr_reset.L2a30
    cmp $0x5,%edx
    jb sbr_reset.L2aef
sbr_reset.L2a85:
    mov %r15d,%eax
    and $0x3,%eax
    mov $0x4,%esi
    cmovne %rax,%rsi
    mov %r15,%rdx
    sub %rsi,%rdx
    neg %rsi
    lea (%r15,%rsi,1),%rax
    inc %rax
    sub %r9,%rdx
    mov -0x30(%rbp),%r8
    lea (%r8,%r9,2),%rsi
sbr_reset.L2aaf:
    add $0x4c254,%rsi
    lea 0x0(,%r13,2),%edi
    lea (%r8,%r9,4),%r8
    sub %rdi,%r8
    add $0x4c288,%r8
    xor %edi,%edi
    vmovq LCPI5_9(%rip),%xmm0
sbr_reset.L2ad6:
    vmovdqu (%r8,%rdi,4),%xmm1
    vpshufb %xmm0,%xmm1,%xmm1
    vmovq %xmm1,(%rsi,%rdi,2)
    add $0x4,%rdi
    cmp %rdi,%rdx
    jne sbr_reset.L2ad6
sbr_reset.L2aef:
    mov %r15,%r8
    sub %rax,%r8
    inc %r8
    mov -0x30(%rbp),%rsi
    lea (%rsi,%rax,2),%rdx
    add $0x4c252,%rdx
    add %r13d,%r13d
    lea (%rsi,%rax,4),%rax
    sub %r13,%rax
    add $0x4c284,%rax
    xor %esi,%esi
    nop
sbr_reset.L2b20:
    movzwl (%rax,%rsi,4),%edi
    mov %di,(%rdx,%rsi,2)
    inc %rsi
    cmp %rsi,%r8
    jne sbr_reset.L2b20
sbr_reset.L2b30:
    mov %r10d,-0x80(%rbp)
    mov %ecx,-0x50(%rbp)
    mov -0x30(%rbp),%r12
    movzbl 0x21(%r12),%eax
    vcvtsi2ss %eax,%xmm15,%xmm0
sbr_reset.L2b45:
    vmovss %xmm0,-0x48(%rbp)
    mov 0x48(%r12),%eax
    vcvtsi2ss %rax,%xmm15,%xmm0
    movswl %r14w,%eax
    vcvtsi2ss %eax,%xmm15,%xmm1
    vdivss %xmm1,%xmm0,%xmm0
sbr_reset.L2b60:
    call log2f
sbr_reset.L2b65:
    vmulss -0x48(%rbp),%xmm0,%xmm0
    vcvtss2si %xmm0,%rax
    cmp $0x2,%rax
    mov $0x1,%ecx
    cmovge %rax,%rcx
    mov %ecx,0x4c1e8(%r12)
    cmp $0x6,%ecx
    jb sbr_reset.L2bb5
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_18(%rip),%rdx
    mov $0x10,%esi
sbr_reset.L2b9d:
    xor %eax,%eax
    call av_log
sbr_reset.L2ba4:
    movl $0x1,0x4c1e8(%r12)
    jmp sbr_reset.L1d31
sbr_reset.L2bb5:
    mov %r14w,0x4c2e6(%r12)
    test %ecx,%ecx
    mov -0x38(%rbp),%r11
    je sbr_reset.L2c89
    mov %ecx,%eax
    and $0x7,%eax
    cmp $0x1,%eax
    jne sbr_reset.L2bde
    xor %esi,%esi
    mov $0x1,%r8d
    jmp sbr_reset.L2c5b
sbr_reset.L2bde:
    mov %ecx,%r9d
    and $0x6,%r9d
    xor %esi,%esi
    mov %ecx,%r10d
    xor %r8d,%r8d
sbr_reset.L2bed:
    mov %r15d,%eax
    sub %esi,%eax
    xor %edx,%edx
    div %r10d
    mov %eax,%edi
    add %esi,%edi
    cmp $0x19,%edi
    jae sbr_reset.L32b9
    mov %edi,%eax
    movzwl 0x4c252(%r12,%rax,2),%eax
    mov %ax,0x4c2e8(%r12,%r8,2)
    mov %r15d,%eax
sbr_reset.L2c1b:
    sub %edi,%eax
    lea -0x1(%r10),%esi
    xor %edx,%edx
    div %esi
    mov %eax,%esi
    add %edi,%esi
    cmp $0x18,%esi
    ja sbr_reset.L32b9
    mov %esi,%eax
    movzwl 0x4c252(%r12,%rax,2),%eax
    mov %ax,0x4c2ea(%r12,%r8,2)
    add $0x2,%r8
sbr_reset.L2c4a:
    add $0xfffffffe,%r10d
    cmp %r8,%r9
    jne sbr_reset.L2bed
    test $0x1,%cl
    je sbr_reset.L2c89
    inc %r8
sbr_reset.L2c5b:
    inc %ecx
    sub %esi,%r15d
    sub %r8d,%ecx
    mov %r15d,%eax
    xor %edx,%edx
    div %ecx
    add %esi,%eax
    cmp $0x18,%eax
    ja sbr_reset.L32b9
    mov %eax,%eax
    movzwl 0x4c252(%r12,%rax,2),%eax
    mov %ax,0x4c2e6(%r12,%r8,2)
sbr_reset.L2c89:
    mov (%r12),%ecx
    mov 0x40(%r12),%esi
    mov %ecx,%eax
    sar $1,%eax
    add $0x1f4000,%eax
    cltd
    idiv %ecx
    lea 0x4c1f0(%r12),%rcx
    mov %rcx,-0x48(%rbp)
    movl $0x0,0x4c330(%r12)
    mov %r11d,%edi
    cmp -0x50(%rbp),%eax
    jae sbr_reset.L30df
sbr_reset.L2cc2:
    lea 0x4c1f0(%r12),%rcx
    movzwl (%rcx),%ecx
    xor %edi,%edi
    cmp %ecx,%eax
    jle sbr_reset.L30df
    movzwl 0x4c1f2(%r12),%ecx
    mov $0x1,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c1f4(%r12),%ecx
    mov $0x2,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2d03:
    movzwl 0x4c1f6(%r12),%ecx
    mov $0x3,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c1f8(%r12),%ecx
    mov $0x4,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c1fa(%r12),%ecx
    mov $0x5,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2d45:
    movzwl 0x4c1fc(%r12),%ecx
    mov $0x6,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c1fe(%r12),%ecx
    mov $0x7,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c200(%r12),%ecx
    mov $0x8,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2d87:
    movzwl 0x4c202(%r12),%ecx
    mov $0x9,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c204(%r12),%ecx
    mov $0xa,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c206(%r12),%ecx
    mov $0xb,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2dc9:
    movzwl 0x4c208(%r12),%ecx
    mov $0xc,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c20a(%r12),%ecx
    mov $0xd,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c20c(%r12),%ecx
    mov $0xe,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2e0b:
    movzwl 0x4c20e(%r12),%ecx
    mov $0xf,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c210(%r12),%ecx
    mov $0x10,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c212(%r12),%ecx
    mov $0x11,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2e4d:
    movzwl 0x4c214(%r12),%ecx
    mov $0x12,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c216(%r12),%ecx
    mov $0x13,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c218(%r12),%ecx
    mov $0x14,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2e8f:
    movzwl 0x4c21a(%r12),%ecx
    mov $0x15,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c21c(%r12),%ecx
    mov $0x16,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c21e(%r12),%ecx
    mov $0x17,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2ed1:
    movzwl 0x4c220(%r12),%ecx
    mov $0x18,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c222(%r12),%ecx
    mov $0x19,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c224(%r12),%ecx
    mov $0x1a,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2f13:
    movzwl 0x4c226(%r12),%ecx
    mov $0x1b,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c228(%r12),%ecx
    mov $0x1c,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c22a(%r12),%ecx
    mov $0x1d,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2f55:
    movzwl 0x4c22c(%r12),%ecx
    mov $0x1e,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c22e(%r12),%ecx
    mov $0x1f,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c230(%r12),%ecx
    mov $0x20,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2f97:
    movzwl 0x4c232(%r12),%ecx
    mov $0x21,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c234(%r12),%ecx
    mov $0x22,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c236(%r12),%ecx
    mov $0x23,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L2fd9:
    movzwl 0x4c238(%r12),%ecx
    mov $0x24,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c23a(%r12),%ecx
    mov $0x25,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c23c(%r12),%ecx
    mov $0x26,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L301b:
    movzwl 0x4c23e(%r12),%ecx
    mov $0x27,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c240(%r12),%ecx
    mov $0x28,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c242(%r12),%ecx
    mov $0x29,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L305d:
    movzwl 0x4c244(%r12),%ecx
    mov $0x2a,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c246(%r12),%ecx
    mov $0x2b,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c248(%r12),%ecx
    mov $0x2c,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L3093:
    movzwl 0x4c24a(%r12),%ecx
    mov $0x2d,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c24c(%r12),%ecx
    mov $0x2e,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
    movzwl 0x4c24e(%r12),%ecx
    mov $0x2f,%edi
    cmp %ecx,%eax
    jbe sbr_reset.L30df
sbr_reset.L30c9:
    movzwl 0x4c250(%r12),%ecx
    mov $0x30,%edi
    cmp %ecx,%eax
    ja sbr_reset.L32dc
sbr_reset.L30df:
    mov $0xffffffff,%eax
    xor %r8d,%r8d
    xor %ecx,%ecx
    mov $0xffffffff,%r15d
    mov %esi,%r9d
    mov -0x80(%rbp),%r10d
    jmp sbr_reset.L312e
sbr_reset.L30f8:
    inc %ecx
    mov %ecx,0x4c330(%r12)
    mov %r11d,%r14d
    mov %r11d,%r10d
sbr_reset.L3108:
    mov -0x38(%rbp),%rdx
    mov -0x48(%rbp),%rbx
    movzwl (%rbx,%rdi,2),%ebx
    sub %r11d,%ebx
    cmp $0x3,%ebx
    cmovl %edx,%edi
    mov %r9d,%r15d
    mov %r14d,%r9d
    cmp %r11w,-0x50(%rbp)
    je sbr_reset.L320e
sbr_reset.L312e:
    mov %eax,%r11d
    mov %edi,%eax
    cmp %r11d,%edi
    jne sbr_reset.L3141
    cmp %r15d,%r9d
    je sbr_reset.L31d5
sbr_reset.L3141:
    mov %eax,%edi
    cmp $0x30,%edi
    ja sbr_reset.L326b
    lea (%r9,%rsi,1),%r14d
    mov -0x48(%rbp),%rdx
    lea (%rdx,%rdi,2),%r15
    xor %r12d,%r12d
    nop
sbr_reset.L3160:
    movzwl (%r15,%r12,2),%r11d
    lea (%rsi,%r11,1),%r13d
    and $0x1,%r13d
    mov %r13d,%ebx
    not %ebx
    add %r14d,%ebx
    cmp %r11d,%ebx
    jae sbr_reset.L318c
    dec %r12
    lea (%rdi,%r12,1),%r11d
    cmp $0x31,%r11d
    jb sbr_reset.L3160
sbr_reset.L3187:
    jmp sbr_reset.L326b
sbr_reset.L318c:
    cmp $0x6,%ecx
    jae sbr_reset.L31f5
    mov %ecx,%ebx
    mov %r11d,%r14d
    sub %r10d,%r14d
    test %r14d,%r14d
    cmovle %r8d,%r14d
    mov -0x30(%rbp),%rdx
    mov %r14b,0x4c334(%rdx,%rbx,1)
    mov %r14d,%r15d
    add %r13d,%r15d
    mov %esi,%r12d
sbr_reset.L31b5:
    sub %r15d,%r12d
    mov %r12b,0x4c33a(%rdx,%rbx,1)
    mov %rdx,%r12
    test %r14b,%r14b
    jne sbr_reset.L30f8
    mov -0x80(%rbp),%r14d
    jmp sbr_reset.L3108
sbr_reset.L31d5:
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_19(%rip),%rdx
    mov $0x10,%esi
    xor %eax,%eax
sbr_reset.L31eb:
    call av_log
sbr_reset.L31f0:
    jmp sbr_reset.L1d31
sbr_reset.L31f5:
    mov -0x40(%rbp),%r15
    mov 0x8(%r15),%rdi
    lea L_str_20(%rip),%rdx
    mov $0x10,%esi
    jmp sbr_reset.L20c8
sbr_reset.L320e:
    cmp $0x2,%ecx
    jb sbr_reset.L3228
    dec %ecx
    cmpb $0x2,0x4c334(%r12,%rcx,1)
    ja sbr_reset.L3228
    mov %ecx,0x4c330(%r12)
sbr_reset.L3228:
    mov %r12,%rdi
    call sbr_make_f_tablelim
sbr_reset.L3230:
    movl $0x0,0x15b2c(%r12)
    movl $0x0,0x2b5ec(%r12)
    jmp sbr_reset.L1d95
sbr_reset.L324d:
    ud1 0x12(%eax),%eax
sbr_reset.L3252:
    ud1 0x12(%eax),%eax
sbr_reset.L3257:
    ud1 0x12(%eax),%eax
sbr_reset.L325c:
    ud1 0x12(%eax),%eax
sbr_reset.L3261:
    ud1 0x12(%eax),%eax
sbr_reset.L3266:
    ud1 0x12(%eax),%eax
sbr_reset.L326b:
    ud1 0x12(%eax),%eax
sbr_reset.L3270:
    ud1 0x12(%eax),%eax
sbr_reset.L3275:
    ud1 0x12(%eax),%eax
sbr_reset.L327a:
    ud1 0x12(%eax),%eax
sbr_reset.L327f:
    ud1 0x12(%eax),%eax
sbr_reset.L3284:
    ud1 0x12(%eax),%eax
sbr_reset.L3289:
    ud1 0x12(%eax),%eax
sbr_reset.L328e:
    lea L_str_3(%rip),%rdx
    lea L_str_9(%rip),%rcx
    lea L_str_5(%rip),%r8
    xor %edi,%edi
    xor %esi,%esi
    mov $0x159,%r9d
    xor %eax,%eax
sbr_reset.L32af:
    call av_log
sbr_reset.L32b4:
    call abort
sbr_reset.L32b9:
    ud1 0x12(%eax),%eax
sbr_reset.L32be:
    ud1 0x12(%eax),%eax
sbr_reset.L32c3:
    ud1 0x12(%eax),%eax
sbr_reset.L32c8:
    ud1 0x12(%eax),%eax
sbr_reset.L32cd:
    ud1 0x12(%eax),%eax
sbr_reset.L32d2:
    ud1 0x12(%eax),%eax
sbr_reset.L32d7:
    ud1 0x12(%eax),%eax
sbr_reset.L32dc:
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
sbr_reset.L32ec:
    int3
    int3
    int3
    int3

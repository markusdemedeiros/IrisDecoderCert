# Test: VEX packed forms of the SBR cluster
subq $128, %rsp
movq %rsp, %rbx
movl $0x3f800000, 0(%rbx)      # 1.0
movl $0x40000000, 4(%rbx)      # 2.0
movl $0x40400000, 8(%rbx)      # 3.0
movl $0x40800000, 12(%rbx)     # 4.0
movl $0x3dcccccd, 16(%rbx)     # 0.1
movl $0xbfc00000, 20(%rbx)     # -1.5
movl $0x41200000, 24(%rbx)     # 10.0
movl $0xc0a00000, 28(%rbx)     # -5.0
movl $0x80000000, 32(%rbx)     # sign masks
movl $0x00000000, 36(%rbx)
movl $0x80000000, 40(%rbx)
movl $0x00000000, 44(%rbx)
movl $0x00000001, 48(%rbx)     # integers
movl $0xfffffffe, 52(%rbx)
movl $0x7fffffff, 56(%rbx)
movl $0x00010000, 60(%rbx)
vmovaps 0(%rbx), %xmm0
vmovaps 16(%rbx), %xmm1
vmovaps 32(%rbx), %xmm2
vmovdqa 48(%rbx), %xmm3
vbroadcastss 16(%rbx), %xmm4
vbroadcastss 20(%rbx), %ymm5
vdivps %xmm1, %xmm0, %xmm6
vsubps %xmm1, %xmm0, %xmm7
vaddsubps %xmm1, %xmm0, %xmm8
vandps %xmm2, %xmm1, %xmm9
vandnps %xmm1, %xmm2, %xmm10
vblendvps %xmm2, 16(%rbx), %xmm0, %xmm11
vinsertps $0x1c, %xmm1, %xmm0, %xmm12
vinsertps $0x90, %xmm1, %xmm0, %xmm13
vpermilps $0x1b, 16(%rbx), %xmm14
vshufpd $0x1, %xmm1, %xmm0, %xmm15
vmovdqa %xmm15, 64(%rbx)
movq 64(%rbx), %r8
movq 72(%rbx), %r9
vmovshdup %xmm1, %xmm15
vmovlps %xmm15, 80(%rbx)
movq 80(%rbx), %r10
vmovsldup %xmm1, %xmm15
movq $0, %rcx
vmovlps %xmm15, 88(%rbx,%rcx,1)
movq 88(%rbx), %r11
vpaddd 48(%rbx), %xmm3, %xmm15
vpextrd $0x1, %xmm15, %r12d
vpextrd $0x3, %xmm15, %r13d
vpand 32(%rbx), %xmm3, %xmm15
vpextrd $0x0, %xmm15, %r14d
vpxor %xmm3, %xmm2, %xmm15
vpextrd $0x2, %xmm15, %r15d
vpslld $0x16, %xmm3, %xmm15
vpextrd $0x0, %xmm15, %eax
vpextrd $0x3, %xmm15, %edx
vpslld $0x20, %xmm3, %xmm15
vpextrd $0x1, %xmm15, %esi
movl $0xdeadbeef, %edi
vpinsrd $0x1, %edi, %xmm3, %xmm15
vpblendw $0xc, %xmm15, %xmm0, %xmm15
vpextrd $0x1, %xmm15, %edi
vpextrd $0x0, %xmm15, %ecx
vpxor %xmm15, %xmm15, %xmm15
movq $0, %rbx
cmpq $1, %rcx

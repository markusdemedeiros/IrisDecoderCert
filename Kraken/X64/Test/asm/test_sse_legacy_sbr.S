# Test: legacy SSE/SSE2/SSE3 forms of sbrdsp.asm; destinations keep bits 255..128
subq $160, %rsp
movq %rsp, %rbx
movl $0x3f800000, 0(%rbx)      # 1.0
movl $0x40000000, 4(%rbx)      # 2.0
movl $0x40400000, 8(%rbx)      # 3.0
movl $0x40800000, 12(%rbx)     # 4.0
movl $0x3dcccccd, 16(%rbx)     # 0.1
movl $0xbfc00000, 20(%rbx)     # -1.5
movl $0x41200000, 24(%rbx)     # 10.0
movl $0xc0a00000, 28(%rbx)     # -5.0
movl $0x11111111, 32(%rbx)
movl $0x22222222, 36(%rbx)
movl $0x11111111, 40(%rbx)
movl $0x44444444, 44(%rbx)
# fill every register's upper half first
vmovups 0(%rbx), %ymm0
vmovups 0(%rbx), %ymm1
vmovups 16(%rbx), %ymm2
vmovups 0(%rbx), %ymm3
vmovups 16(%rbx), %ymm4
vmovups 0(%rbx), %ymm5
vmovups 16(%rbx), %ymm6
vmovups 0(%rbx), %ymm7
vmovups 16(%rbx), %ymm8
vmovups 0(%rbx), %ymm9
vmovups 16(%rbx), %ymm10
vmovups 0(%rbx), %ymm11
vmovups 16(%rbx), %ymm12
vmovups 0(%rbx), %ymm13
vmovups 16(%rbx), %ymm14
vmovups 0(%rbx), %ymm15
movss 16(%rbx), %xmm0          # zeroes 127..32
movss %xmm2, %xmm1             # merges
movss %xmm1, 64(%rbx)
movl 64(%rbx), %eax
addss %xmm2, %xmm1
addss 24(%rbx), %xmm1
movq $1, %rcx
movsd 8(%rbx,%rcx,8), %xmm3    # 16(%rbx)
movlps (%rbx), %xmm4
movlps 8(%rbx,%rcx,4), %xmm5   # 12(%rbx)
movhps 16(%rbx), %xmm6
movhps %xmm6, 72(%rbx)
movq 72(%rbx), %rdx
movlps %xmm5, 80(%rbx)
movq 80(%rbx), %rsi
movlhps %xmm2, %xmm7
movhlps %xmm2, %xmm8
shufps $0x1b, %xmm2, %xmm9
shufps $0x14, 16(%rbx), %xmm10
unpcklps %xmm2, %xmm11
unpckhps (%rbx), %xmm12
haddps %xmm2, %xmm13
movddup (%rbx,%rcx,8), %xmm14
movshdup %xmm2, %xmm15
movq %xmm15, 88(%rbx)
movq 88(%rbx), %rdi
movq 88(%rbx), %xmm15
movdqa 32(%rbx), %xmm2
movdqa %xmm2, 96(%rbx)
movdqu 4(%rbx), %xmm2
movdqu %xmm2, 116(%rbx)
movq 116(%rbx), %r8
movdqa 16(%rbx), %xmm2
pxor (%rbx), %xmm2
pand %xmm0, %xmm2
pcmpeqd 32(%rbx), %xmm3
pshufd $0x1b, %xmm2, %xmm3
punpckldq %xmm2, %xmm4
punpckhdq 32(%rbx), %xmm5
movdqa %xmm4, %xmm6
movq $0, %rbx
cmpq $1, %rcx

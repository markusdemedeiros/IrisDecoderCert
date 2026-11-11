# Test: VEX integer forms of the SBR reset code: vmovdqu (unaligned, indexed),
# vpaddw, vpinsrw, vpminsd, vpshufb (incl. the high-bit zeroing), vpshufd,
# vpunpcklqdq, vblendps, vpmovsxwd (m64) and vcvtdq2ps.
subq $128, %rsp
movq %rsp, %rbx
movl $0x00010002, 0(%rbx)
movl $0xfffe7fff, 4(%rbx)
movl $0x80000000, 8(%rbx)
movl $0x00000005, 12(%rbx)
movl $0x0f0e0d0c, 16(%rbx)     # pshufb control: bytes 12..15 and zeroing bits
movl $0x80010203, 20(%rbx)
movl $0x07060504, 24(%rbx)
movl $0x0b8a0908, 28(%rbx)
movl $0x7ffffffe, 32(%rbx)
movl $0xfffffff9, 36(%rbx)
movl $0x00000003, 40(%rbx)
movl $0x80000001, 44(%rbx)
movq $1, %rsi
movq $2, %rdi
# unaligned loads: (r,r,4) and d(r,r,4)
vmovdqu (%rbx,%rsi,4), %xmm0                 # bytes 4..19
vmovdqu -4(%rbx,%rdi,4), %xmm1               # bytes 4..19
vmovdqu (%rbx), %xmm2                        # bytes 0..15
vmovdqu 32(%rbx), %xmm3                      # bytes 32..47
vmovdqu 16(%rbx), %xmm4                      # pshufb control
vpaddw %xmm0, %xmm2, %xmm5
movl $0x1234abcd, %eax
vpinsrw $0x1, %eax, %xmm5, %xmm6
vpinsrw $0xf, %eax, %xmm2, %xmm7             # imm & 7 = 7
vpminsd %xmm3, %xmm2, %xmm8
vpshufb %xmm4, %xmm2, %xmm9
vpshufb 16(%rbx), %xmm3, %xmm10
vpshufd $0x1b, %xmm2, %xmm11
vpshufd $0x0, 32(%rbx), %xmm12
vpunpcklqdq %xmm3, %xmm2, %xmm13
vblendps $0xa, %xmm3, %xmm2, %xmm14
vblendps $0xe, 32(%rbx), %xmm2, %xmm15
# unaligned store d(r,r,2), read back
vmovdqu %xmm14, 49(%rbx,%rsi,2)
movq 51(%rbx), %r8
movq 59(%rbx), %r9
# vpmovsxwd from m64 at d(r,r,2)
vpmovsxwd 2(%rbx,%rsi,2), %xmm0              # words at bytes 4..11
vcvtdq2ps %xmm3, %xmm1
vcvtdq2ps 0(%rbx), %xmm4
addq $128, %rsp
movq $0, %rbx

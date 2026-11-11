# Test: the 256-bit (ymm) forms of the VEX integer instructions added for the SBR
# parser, which the parser accepts but the SBR code uses only at 128 bits:
# vmovdqu (load and store), vcvtdq2ps, vblendps (imm bits 4..7 select the upper
# lane), vpaddw, vpminsd, vpshufb and vpshufd (per 128-bit lane), vpunpcklqdq
# (per 128-bit lane) and vpsrld with an xmm count.
subq $128, %rsp
movq %rsp, %rbx
movl $0x00010002, 0(%rbx)
movl $0xfffe7fff, 4(%rbx)
movl $0x80000000, 8(%rbx)
movl $0x00000005, 12(%rbx)
movl $0x0f0e0d0c, 16(%rbx)
movl $0x80010203, 20(%rbx)
movl $0x07060504, 24(%rbx)
movl $0x0b8a0908, 28(%rbx)
movl $0x7ffffffe, 32(%rbx)
movl $0xfffffff9, 36(%rbx)
movl $0x00000003, 40(%rbx)
movl $0x80000001, 44(%rbx)
movl $0x03020100, 48(%rbx)
movl $0x8f0e0706, 52(%rbx)
movl $0x0c0d0a0b, 56(%rbx)
movl $0x01800908, 60(%rbx)
movq $1, %rsi
# unaligned 256-bit loads
vmovdqu 4(%rbx), %ymm0                       # bytes 4..35
vmovdqu (%rbx,%rsi,8), %ymm1                 # bytes 8..39
vmovdqu 32(%rbx), %ymm2                      # bytes 32..63
vmovdqu 16(%rbx), %ymm3                      # pshufb control (both lanes)
vpaddw %ymm0, %ymm1, %ymm4
vpminsd %ymm1, %ymm2, %ymm5
vpshufb %ymm3, %ymm0, %ymm6
vpshufb 32(%rbx), %ymm1, %ymm7
vpshufd $0x1b, %ymm0, %ymm8
vpshufd $0x4e, 8(%rbx), %ymm9
vpunpcklqdq %ymm1, %ymm0, %ymm10
vpunpcklqdq 24(%rbx), %ymm2, %ymm11
vblendps $0xa5, %ymm1, %ymm0, %ymm12
vblendps $0x3c, 16(%rbx), %ymm2, %ymm13
vcvtdq2ps %ymm0, %ymm14
vcvtdq2ps 12(%rbx), %ymm15
# unaligned 256-bit store, read back
vmovdqu %ymm4, 66(%rbx)
movq 66(%rbx), %r8
movq 74(%rbx), %r9
movq 82(%rbx), %r10
movq 90(%rbx), %r11
# vpsrld ymm with an xmm count: 3, then 32 (all lanes zero)
movq $3, %rax
vmovq %rax, %xmm1
vpsrld %xmm1, %ymm2, %ymm1
movq $32, %rax
vmovq %rax, %xmm3
vpsrld %xmm3, %ymm0, %ymm3
addq $128, %rsp
movq $0, %rbx
movq $0, %rax

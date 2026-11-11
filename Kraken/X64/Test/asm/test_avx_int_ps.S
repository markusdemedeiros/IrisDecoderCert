# Test: VEX integer forms of the PS parser code: vpcmpeqd (register, memory,
# same register), vpsrld with an xmm count (0, 5, 31, 32, and counts whose
# low 32 bits are small but whose low 64 bits are not; the high quadword of
# the count is ignored), and vpmovzxdq (register and m64).
subq $128, %rsp
movq %rsp, %rbx
movl $0x80000001, 0(%rbx)
movl $0xffffffff, 4(%rbx)
movl $0x00000000, 8(%rbx)
movl $0x7fffffff, 12(%rbx)
movl $0x80000001, 16(%rbx)     # equal, different, different, equal to 0..15
movl $0xfffffffe, 20(%rbx)
movl $0x00000001, 24(%rbx)
movl $0x7fffffff, 28(%rbx)
movl $0x89abcdef, 32(%rbx)
movl $0x01234567, 36(%rbx)
vmovdqu 0(%rbx), %xmm0
vmovdqu 16(%rbx), %xmm1
vpcmpeqd %xmm1, %xmm0, %xmm2
vpcmpeqd 16(%rbx), %xmm0, %xmm3
vpcmpeqd %xmm4, %xmm4, %xmm4
vpcmpeqd %xmm5, %xmm5, %xmm5
vpcmpeqd %ymm1, %ymm0, %ymm6
# counts
movl $5, %eax
vmovd %eax, %xmm7
vpsrld %xmm7, %xmm0, %xmm8
movl $31, %eax
vmovd %eax, %xmm7
vpsrld %xmm7, %xmm0, %xmm9
movl $32, %eax
vmovd %eax, %xmm7
vpsrld %xmm7, %xmm0, %xmm10
movq $0x100000003, %rax        # low 32 bits 3, low 64 bits large
vmovq %rax, %xmm7
vpsrld %xmm7, %xmm0, %xmm11
movl $0, %eax
vmovd %eax, %xmm7
vpsrld %xmm7, %xmm0, %xmm12
movl $4, %eax
vpinsrd $0x2, %eax, %xmm4, %xmm7   # count: low qword 0xffffffffffffffff
vpsrld %xmm7, %xmm0, %xmm13
movl $0, %eax
vmovd %eax, %xmm7
vpinsrd $0x2, %eax, %xmm7, %xmm7   # high quadword ignored
movl $7, %eax
vpinsrd $0x0, %eax, %xmm7, %xmm7
movl $0xffffffff, %eax
vpinsrd $0x3, %eax, %xmm7, %xmm7
vpsrld %xmm7, %xmm0, %xmm14
vpsrld %xmm7, %xmm0, %xmm0     # dst = src
# vpmovzxdq
vpmovzxdq %xmm1, %xmm15
vpmovzxdq 32(%rbx), %xmm5
movq $1, %rsi
vpmovzxdq 28(%rbx,%rsi,4), %xmm1
addq $128, %rsp
movq $0, %rbx
movq $0, %rsi

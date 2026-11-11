# Test: VEX vinsertf128 (register and memory forms, lane 0 and 1) and AVX2
# vpermps (register and memory forms; the reversal mask of
# ff_vector_fmul_reverse_avx2, and a mask with index bits above bit 2 set,
# which vpermps ignores).

subq $0x80, %rsp
movl $0x3f800000, 0(%rsp)   # 1.0
movl $0x40000000, 4(%rsp)   # 2.0
movl $0x40400000, 8(%rsp)   # 3.0
movl $0x40800000, 12(%rsp)  # 4.0
movl $0x40a00000, 16(%rsp)  # 5.0
movl $0x40c00000, 20(%rsp)  # 6.0
movl $0x40e00000, 24(%rsp)  # 7.0
movl $0x41000000, 28(%rsp)  # 8.0
movl $0x41100000, 32(%rsp)  # 9.0
movl $0x41200000, 36(%rsp)  # 10.0
movl $0x41300000, 40(%rsp)  # 11.0
movl $0x41400000, 44(%rsp)  # 12.0
movl $0x41500000, 48(%rsp)  # 13.0
movl $0x41600000, 52(%rsp)  # 14.0
movl $0x41700000, 56(%rsp)  # 15.0
movl $0x41800000, 60(%rsp)  # 16.0
# pd_reverse: dd 7, 6, 5, 4, 3, 2, 1, 0
movl $7, 64(%rsp)
movl $6, 68(%rsp)
movl $5, 72(%rsp)
movl $4, 76(%rsp)
movl $3, 80(%rsp)
movl $2, 84(%rsp)
movl $1, 88(%rsp)
movl $0, 92(%rsp)
# a mask with high bits: 0x10, 0xfffffff9, 2, 0x23, 4, 5, 6, 0x80000007
movl $0x10, 96(%rsp)
movl $0xfffffff9, 100(%rsp)
movl $2, 104(%rsp)
movl $0x23, 108(%rsp)
movl $4, 112(%rsp)
movl $5, 116(%rsp)
movl $6, 120(%rsp)
movl $0x80000007, 124(%rsp)

vmovups 0(%rsp), %ymm0
vmovups 32(%rsp), %ymm1

# vinsertf128, as in ff_vector_fmul_reverse_avx: xmm load, then the other lane
vmovups 16(%rsp), %xmm2
vinsertf128 $0x1, 0(%rsp), %ymm2, %ymm2
vshufps $0x1b, %ymm2, %ymm2, %ymm2
# lane 0, memory, unaligned
vinsertf128 $0x0, 36(%rsp), %ymm0, %ymm3
# register forms, both lanes
vinsertf128 $0x0, %xmm1, %ymm0, %ymm4
vinsertf128 $0x1, %xmm1, %ymm0, %ymm5
# imm with bits above bit 0 (only bit 0 counts)
vinsertf128 $0x3, %xmm1, %ymm0, %ymm6

# vpermps, as in ff_vector_fmul_reverse_avx2: mask in ymm7, table from memory
vmovups 64(%rsp), %ymm7
vpermps 0(%rsp), %ymm7, %ymm8
vpermps 4(%rsp), %ymm7, %ymm9
# register form, high index bits ignored
vmovups 96(%rsp), %ymm10
vpermps %ymm0, %ymm10, %ymm11
# destination equal to the index register
vmovups 64(%rsp), %ymm12
vpermps %ymm1, %ymm12, %ymm12

addq $0x80, %rsp

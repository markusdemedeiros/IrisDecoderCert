# Test: VEX vfmadd132ps (dst := dst * src2 + src1, rounded once), in register
# and memory forms, on xmm and ymm registers. Same lane values as
# test_avx_fma.S (a * b + c with a in the destination, b the third operand and
# c the second). No lane produces a NaN: Kraken's NaN bit patterns differ from x86's.

subq $0x60, %rsp

# a at 0, b at 32, c at 64
movl $0x3f800800, 0(%rsp)    # (1+2^-12)^2 - 1 = 2^-11 + 2^-24 exactly
movl $0x3f800800, 32(%rsp)
movl $0xbf800000, 64(%rsp)
movl $0x40000000, 4(%rsp)    # 2 * 3 + 1
movl $0x40400000, 36(%rsp)
movl $0x3f800000, 68(%rsp)
movl $0x80000001, 8(%rsp)    # -tiny * tiny + 0 underflows to -0
movl $0x00000001, 40(%rsp)
movl $0x00000000, 72(%rsp)
movl $0x00000000, 12(%rsp)   # +0 * 5 + -0 = +0
movl $0x40a00000, 44(%rsp)
movl $0x80000000, 76(%rsp)
movl $0x3fc00000, 16(%rsp)   # 1.5 * 2 - 3 cancels exactly to +0
movl $0x40000000, 48(%rsp)
movl $0xc0400000, 80(%rsp)
movl $0x7f7fffff, 20(%rsp)   # FLT_MAX * 2 - FLT_MAX: no intermediate overflow
movl $0x40000000, 52(%rsp)
movl $0xff7fffff, 84(%rsp)
movl $0x00800000, 24(%rsp)   # 2^-126 * 0.5 + 2^-149 is subnormal
movl $0x3f000000, 56(%rsp)
movl $0x00000001, 88(%rsp)
movl $0x3f800001, 28(%rsp)   # (1+2^-23)(1-2^-24) - 1 = 2^-24 - 2^-47 exactly
movl $0x3f7fffff, 60(%rsp)
movl $0xbf800000, 92(%rsp)

# memory form, as in ff_vector_fmul_add_fma3: vfmadd132ps m256, c, a
vmovups 0(%rsp), %ymm0
vmovups 64(%rsp), %ymm2
vfmadd132ps 32(%rsp), %ymm2, %ymm0

# register form
vmovups 0(%rsp), %ymm1
vmovups 32(%rsp), %ymm3
vfmadd132ps %ymm3, %ymm2, %ymm1

# xmm forms clear bits 255:128 of the destination
vmovups 0(%rsp), %ymm4
vfmadd132ps %xmm3, %xmm2, %xmm4
vmovups 0(%rsp), %ymm5
vfmadd132ps 32(%rsp), %xmm2, %xmm5

# unaligned memory operand
vmovups 0(%rsp), %ymm6
vfmadd132ps 4(%rsp), %ymm2, %ymm6

addq $0x60, %rsp

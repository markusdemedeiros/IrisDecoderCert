# Test: VEX scalar float forms (vmovss/vmovsd memory forms, scalar arithmetic,
# compares, conversions, vmovd/vmovq)
subq $128, %rsp
movq %rsp, %rbx
movl $0x3f800000, 0(%rbx)      # 1.0
movl $0x40400000, 4(%rbx)      # 3.0
movl $0x3dcccccd, 8(%rbx)      # 0.1
movl $0xbfc00000, 12(%rbx)     # -1.5
movl $0x41200000, 16(%rbx)     # 10.0
movl $0x40000000, 20(%rbx)     # 2.0
movabsq $0x3fb999999999999a, %rax
movq %rax, 24(%rbx)            # 0.1 (double)
movabsq $0x3ff8000000000000, %rax
movq %rax, 32(%rbx)            # 1.5 (double)
movl $0x7fc00000, 40(%rbx)     # NaN
movl $0x40490fdb, 44(%rbx)     # pi
# Loads zero bits 255..32, whatever was there
vmovups (%rbx), %ymm0
vmovups (%rbx), %ymm1
vmovss (%rbx), %xmm0           # 1.0
movq $1, %rcx
vmovss 4(%rbx,%rcx,4), %xmm1   # 0.1
vmovss (%rbx,%rcx,4), %xmm2    # 3.0
vmovss 8(%rbx,%rcx,8), %xmm3   # 10.0
vmovss 2(%rbx,%rcx,2), %xmm4   # 3.0
vmovss 12(%rbx), %xmm5         # -1.5
# Arithmetic, register and memory sources; upper elements from src1
vaddss %xmm1, %xmm0, %xmm6
vaddss 4(%rbx), %xmm6, %xmm6   # 1.1 + 3
vaddss (%rbx,%rcx,4), %xmm6, %xmm6
vmulss %xmm1, %xmm2, %xmm7     # 0.3
vmulss 16(%rbx), %xmm7, %xmm7
vmulss (%rbx,%rcx,8), %xmm7, %xmm7
vdivss %xmm2, %xmm0, %xmm8     # 1/3
vdivss 20(%rbx), %xmm8, %xmm8
vsubss %xmm1, %xmm5, %xmm9     # -1.6
vminss %xmm5, %xmm0, %xmm10    # -1.5
vminss 16(%rbx), %xmm0, %xmm11 # 1.0
vsqrtss %xmm2, %xmm2, %xmm12   # sqrt 3
vsqrtss 44(%rbx), %xmm6, %xmm13
# Stores, several shapes
vmovss %xmm6, 48(%rbx)
vmovss %xmm7, 48(%rbx,%rcx,4)
vmovss %xmm8, (%rbx,%rcx,8)
vmovss %xmm9, 52(%rbx,%rcx,8)
movl 48(%rbx), %r8d
movl 52(%rbx), %r9d
movl 8(%rbx), %r10d
movl 60(%rbx), %r11d
# Double precision
vmovsd 24(%rbx), %xmm14        # 0.1
vmovsd (%rbx,%rcx,8), %xmm15   # 8(%rbx): bits of 0.1f and -1.5f
vmulsd 32(%rbx), %xmm14, %xmm14
vmulsd 24(%rbx,%rcx,8), %xmm14, %xmm14
vmovsd %xmm14, 64(%rbx)
movq 64(%rbx), %r12
# Conversions
vcvtss2sd %xmm1, %xmm1, %xmm15
vcvtsd2ss %xmm14, %xmm2, %xmm3
movl $-7, %esi
vcvtsi2ss %esi, %xmm4, %xmm4
movl $16777217, %esi           # rounds
vcvtsi2ss %esi, %xmm5, %xmm5
vmovq 24(%rbx), %xmm0
vcvtps2pd %xmm6, %xmm1
# vmovd / vmovq
movl $0x12345678, %esi
vmovd %esi, %xmm2
vmovd %xmm2, %edi
vmovd %xmm3, 72(%rbx)
vmovd 72(%rbx), %xmm9
vmovd %xmm4, (%rbx,%rcx,4)
movl 4(%rbx), %r13d
vmovq %xmm14, 80(%rbx)
vmovq 80(%rbx), %xmm10
movq 80(%rbx), %r14
vmovapd %xmm5, %xmm11
vxorpd %xmm12, %xmm12, %xmm12
movq $0, %rbx
cmpq $1, %rcx

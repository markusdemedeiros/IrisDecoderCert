# Test: vcvtss2si with a 64-bit destination rounds to nearest, ties to even;
# NaN, infinities and out-of-range values give 0x8000000000000000.
subq $16, %rsp
movl $0x40200000, %eax         # 2.5 -> 2
vmovd %eax, %xmm0
vcvtss2si %xmm0, %rbx
movl $0x40600000, %eax         # 3.5 -> 4
vmovd %eax, %xmm0
vcvtss2si %xmm0, %rcx
movl $0xc0200000, %eax         # -2.5 -> -2
vmovd %eax, %xmm0
vcvtss2si %xmm0, %rdx
movl $0xbfe00000, %eax         # -1.75 -> -2
vmovd %eax, %xmm0
vcvtss2si %xmm0, %rsi
movl $0x3f000000, %eax         # 0.5 -> 0
vmovd %eax, %xmm0
vcvtss2si %xmm0, %rdi
movl $0x3fc00000, %eax         # 1.5 -> 2
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r8
movl $0x5f0ac723, %eax         # 1e19 -> indefinite
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r9
movl $0xdf0ac723, %eax         # -1e19 -> indefinite
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r10
movl $0x5f000000, %eax         # 2^63 -> indefinite
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r11
movl $0xdf000000, %eax         # -2^63 fits
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r12
movl $0x7fc00000, %eax         # NaN -> indefinite
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r13
movl $0xff800000, %eax         # -inf -> indefinite
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r14
movl $0x4b7fffff, %eax         # 16777215.0
vmovd %eax, %xmm0
vcvtss2si %xmm0, %r15
movl $0xc2f70000, (%rsp)       # -123.5 from memory (m32) -> -124
vcvtss2si (%rsp), %rbp
movl $0x80000000, %eax         # -0.0 -> 0
vmovd %eax, %xmm1
vcvtss2si %xmm1, %rax
addq $16, %rsp

# Test: vucomiss/vucomisd flags (greater, less, equal, unordered), jnp, vcmpltss/vcmpeqss
subq $64, %rsp
movq %rsp, %rbx
movl $0x3f800000, 0(%rbx)      # 1.0
movl $0x40400000, 4(%rbx)      # 3.0
movl $0x7fc00000, 8(%rbx)      # NaN
movl $0x3f800000, 12(%rbx)     # 1.0
vmovss 0(%rbx), %xmm0
vmovss 4(%rbx), %xmm1
vmovss 8(%rbx), %xmm2
vmovss 12(%rbx), %xmm3
# 1.0 vs 3.0: less, CF
vucomiss %xmm1, %xmm0
setb %al
sete %ah
setp %cl
# 3.0 vs 1.0: greater
vucomiss %xmm0, %xmm1
seta %dl
setp %dh
# equal
vucomiss %xmm3, %xmm0
sete %sil
setb %dil
# unordered: ZF, PF, CF all set
vucomiss %xmm2, %xmm0
sete %r8b
setp %r9b
setb %r10b
jnp unord_bad
movq $1, %r11
jmp unord_done
unord_bad:
movq $2, %r11
unord_done:
# doubles
vcvtss2sd %xmm0, %xmm0, %xmm4
vcvtss2sd %xmm1, %xmm1, %xmm5
vucomisd %xmm5, %xmm4
setb %r12b
vcvtss2sd %xmm2, %xmm2, %xmm6
vucomisd %xmm6, %xmm4
setp %r13b
# vcmpss
vcmpltss %xmm1, %xmm0, %xmm7   # 1 < 3: all ones
vcmpltss %xmm0, %xmm1, %xmm8   # 3 < 1: zero
vcmpeqss %xmm3, %xmm0, %xmm9   # equal
vcmpeqss %xmm2, %xmm2, %xmm10  # NaN == NaN: false
vcmpltss 4(%rbx), %xmm0, %xmm11
vcmpless %xmm0, %xmm3, %xmm12
movq $0, %rbx
cmpq $1, %r11

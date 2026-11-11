# Undefined flags: cf, pf, af, zf, sf, of
# Test: div / idiv on 8, 32 and 64 bits, register and memory divisors, with
# truncation toward zero and remainders taking the dividend's sign. Only
# non-faulting cases (a #DE has no successor state to compare).
subq $16, %rsp
# 32-bit unsigned: 0x1_12345678 / 16; the upper halves of rax/rdx are cleared
movabsq $0xffffffff12345678, %rax
movabsq $0xffffffff00000001, %rdx
movl $0x10, %ecx
divl %ecx
movq %rax, %r8
movq %rdx, %r9
# 32-bit signed: -7 / 2 = -3 rem -1
movl $-7, %eax
cltd
movl $2, %ecx
idivl %ecx
movq %rax, %r10
movq %rdx, %r11
# 32-bit signed: 7 / -2 = -3 rem 1 (unsuffixed mnemonic)
movl $7, %eax
cltd
movl $-2, %ecx
idiv %ecx
movq %rax, %r12
movq %rdx, %r13
# INT_MIN / 1 fits
movl $0x80000000, %eax
cltd
movl $1, %ecx
idiv %ecx
movq %rax, %r14
movq %rdx, %r15
# 64-bit unsigned with a nonzero high half
movabsq $0x123456789abcdef0, %rax
movq $0x5, %rdx
movabsq $0x10000000000, %rcx
divq %rcx
movq %rax, %rsi
movq %rdx, %rdi
# 32-bit memory divisor (unsuffixed register form above, suffixed here)
movl $3, (%rsp)
movl $100, %eax
xorl %edx, %edx
divl (%rsp)
shlq $32, %rdx
orq %rdx, %rax
movq %rax, %rbp
# 64-bit signed: -100 / 7 = -14 rem -2
movq $-1, %rdx
movq $-100, %rax
movq $7, %rcx
idivq %rcx
movq %rax, %rbx
xorq %rdx, %rbx
# 8-bit: ax / cl -> al quotient, ah remainder; the rest of rax is kept
movabsq $0x1122334455660107, %rax
movb $0x10, %cl
divb %cl
movq %rax, %rcx
# 8-bit signed: -100 / 7 = -14 rem -2
movl $0xabcdff9c, %eax
movb $7, %dl
idivb %dl
addq $16, %rsp

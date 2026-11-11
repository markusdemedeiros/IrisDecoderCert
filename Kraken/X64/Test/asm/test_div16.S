# Undefined flags: cf, pf, af, zf, sf, of
# Test: 16-bit div / idiv (dx:ax by a 16-bit divisor; quotient to ax, remainder
# to dx, the rest of rax and rdx kept), register and memory divisors. Only
# non-faulting cases (a #DE has no successor state to compare).
subq $16, %rsp
# unsigned: 0x0001_2345 / 0x10 = 0x1234 rem 5
movabsq $0x1122334455662345, %rax
movabsq $0x7766554433220001, %rdx
movw $0x10, %cx
divw %cx
movq %rax, %r8
movq %rdx, %r9
# signed: -1000 / 7 = -142 rem -6 (dx:ax = sign extension of ax)
movabsq $0xaaaabbbbccccfc18, %rax
movabsq $0x111122223333ffff, %rdx
movw $7, %cx
idivw %cx
movq %rax, %r10
movq %rdx, %r11
# signed, memory divisor: 1000 / -7 = -142 rem 6
movw $-7, (%rsp)
movq $1000, %rax
xorq %rdx, %rdx
idivw (%rsp)
movq %rax, %r12
movq %rdx, %r13
# unsigned, memory divisor, unsuffixed register form
movw $0x300, 2(%rsp)
movq $0xffff, %rax
movq $0x2ff, %rdx
divw 2(%rsp)
movq %rax, %r14
movq %rdx, %r15
movw $9, %cx
movq $100, %rax
xorq %rdx, %rdx
div %cx
movq %rax, %rsi
movq %rdx, %rdi
addq $16, %rsp

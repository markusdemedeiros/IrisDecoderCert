# Test: cltd (Intel cdq) sets edx to the sign of eax and clears the upper half of rdx;
# flags are unchanged.
movabsq $0x123456789abcdef0, %rdx
movl $0x80000001, %eax
cltd
movq %rdx, %rbx
movabsq $0xfedcba9876543210, %rdx
movl $0x7fffffff, %eax
cltd
movq %rdx, %rcx
movabsq $0xffffffff00000000, %rax
cmpq $1, %rax
cltd

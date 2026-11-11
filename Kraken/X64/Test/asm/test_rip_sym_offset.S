# Test: `sym+off(%rip)` and `sym-off(%rip)` address the symbol plus or minus
# the offset
  lea next(%rip), %rax
next:
  lea next+16(%rip), %rcx
  lea next-0x8(%rip), %rdx
  lea next(%rip), %rbx
  subq %rax, %rcx
  subq %rax, %rdx
  subq %rax, %rbx
  movl $0, %eax

# Test: movzbl/movzwl with memory sources, inc r32/r64, cltq, jp/jnp
pushq $0x1234f6a5
pushq $0x7f80ff01
movq %rsp, %rbx
movq $1, %rsi
movzbl (%rbx), %eax            # 0x01
movzbl 3(%rbx), %ecx           # 0x7f
movzbl 1(%rbx,%rsi,1), %edx    # 0x80
movzbl (%rbx,%rsi,1), %ebp     # 0xff
movzwl (%rbx), %edi            # 0xff01
movzwl 8(%rbx,%rsi,2), %r8d    # 0x1234
movzwl 8(%rbx), %r9d           # 0xf6a5
leaq 8(%rbx), %r10
movzwl (%r10,%rsi,2), %r10d    # 0x1234
movq $0, %rbx
# inc
inc %eax                       # 2
inc %r9                        # 0xf6a6
movl $0x7fffffff, %r11d
inc %r11d                      # OF
setl %r12b
movq $-1, %r13
inc %r13                       # ZF, CF untouched
setz %r14b
setc %r15b
# cltq
movl $0x80000005, %esi
movl %esi, %eax
cltq
movq %rax, %rsi
movl $0x7ffffff0, %eax
cltq
# jp / jnp: cmp of 3 against 0 leaves 3 (two bits set, PF = 1)
movl $3, %ecx
cmpl $0, %ecx
jnp par_bad1
jp par_ok1
par_bad1:
movq $0xbad, %rcx
par_ok1:
# 7 has three bits: PF = 0
movl $7, %edx
cmpl $0, %edx
jp par_bad2
jnp par_ok2
par_bad2:
movq $0xbad, %rdx
par_ok2:
cmpq $5, %rdi

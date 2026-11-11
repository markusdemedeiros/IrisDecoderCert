# Undefined flags: af

# Test: the sign condition codes s and ns (sets/setns, js/jns, cmovs/cmovns),
# including a case where signed overflow makes sf differ from the signed order.

  movq $0, %rax
  movq $0, %rbx
  movq $0, %rcx
  movq $0, %rdx
  movq $0, %rsi
  movq $0, %rdi
  movq $0, %r8
  movq $0, %r9

  # 1 - 2 = -1: sf=1
  movq $1, %r14
  movq $2, %r15
  cmpq %r15, %r14
  sets %al
  setns %bl

  # 5 - 5 = 0: sf=0
  movq $5, %r14
  cmpq %r14, %r14
  sets %cl
  setns %dl

  # INT64_MIN - 1 overflows to a positive value: sf=0 (though INT64_MIN < 1)
  movabsq $0x8000000000000000, %r14
  movq $1, %r15
  cmpq %r15, %r14
  sets %sil
  setns %dil

  # cmovs / cmovns after a negative 32-bit result
  movl $3, %r10d
  movl $7, %r11d
  movl $0x11, %r12d
  movl $0x22, %r13d
  subl %r11d, %r10d
  cmovs %r12d, %r8d
  cmovns %r13d, %r9d

  # js / jns
  movq $-4, %r14
  testq %r14, %r14
  jns sign_bad
  js sign_ok
sign_bad:
  movq $0xbad, %r14
sign_ok:
  movq $4, %r15
  testq %r15, %r15
  js sign_bad2
  jns sign_ok2
sign_bad2:
  movq $0xbad, %r15
sign_ok2:

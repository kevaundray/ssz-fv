# SysV: RDI=left, RSI=right, RDX=byte count; signed int result in EAX.
# Returns the first unequal unsigned-byte difference, or zero. Readable inputs
# may overlap each other or the RET slot. Zero count requires no input access.
# No stores or stack scratch; the caller supplies a valid RET slot.
.text
.globl memcmp
.type memcmp,@function
memcmp:
  xorl %eax, %eax
  testq %rdx, %rdx
  jz .Lmemcmp_done
.Lmemcmp_loop:
  movzbl (%rdi), %eax
  movzbl (%rsi), %ecx
  subl %ecx, %eax
  jnz .Lmemcmp_done
  addq $1, %rdi
  addq $1, %rsi
  subq $1, %rdx
  jnz .Lmemcmp_loop
.Lmemcmp_done:
  ret
.size memcmp, .-memcmp
.section .note.GNU-stack,"",@progbits

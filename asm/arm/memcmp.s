// AAPCS64: X0=left, X1=right, X2=byte count; signed int result in W0.
// Returns the first unequal unsigned-byte difference, or zero. Readable inputs
// may overlap. Zero count requires no input access. No stores or stack scratch.
.text
.globl memcmp
.type memcmp,%function
memcmp:
  mov x3, x0
  mov w0, wzr
  cbz x2, .Lmemcmp_done
.Lmemcmp_loop:
  ldrb w4, [x3], #1
  ldrb w5, [x1], #1
  subs w0, w4, w5
  b.ne .Lmemcmp_done
  sub x2, x2, #1
  cbnz x2, .Lmemcmp_loop
.Lmemcmp_done:
  ret
.size memcmp, .-memcmp
.section .note.GNU-stack,"",%progbits

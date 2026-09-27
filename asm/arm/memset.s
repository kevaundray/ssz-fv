/* AAPCS64: X0 destination, low byte of W1 fill value, X2 byte count.
 * Empty fills access no data; sub-vector fills skip DUP setup.
 * X0 retains the original destination; no stack space is used.
 */
.text
.p2align 4
.global memset
.type memset,%function
memset:
 mov x3,x0
 cmp x2,#16
 b.lo .Lfill_tail
 dup v0.16b,w1
.Lfill_bulk:
 str q0,[x3],#16
 sub x2,x2,#16
 cmp x2,#16
 b.hs .Lfill_bulk
.Lfill_tail:
 cbz x2,.Lfill_done
.Lfill_byte:
 strb w1,[x3],#1
 sub x2,x2,#1
 cbnz x2,.Lfill_byte
.Lfill_done:
 ret
.size memset,.-memset
.section .note.GNU-stack,"",%progbits

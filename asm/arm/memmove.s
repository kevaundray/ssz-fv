// AAPCS64: X0=destination, X1=source, X2=byte count; returns the original X0.
// Caller provides readable/writable, nonwrapping buffer ranges. Overlap is allowed;
// each 16-byte vector is loaded before its store. Zero length and equal pointers
// return without buffer access. No stack scratch; code must remain immutable.
// Backward pointer setup stays outside the supported negative post-index loops.
.text
.p2align 4
.global memmove
.type memmove,%function
memmove:
 cbz x2,.Lmove_forward_done
 sub x4,x0,x1
 cbz x4,.Lmove_forward_done
 cmp x0,x1
 b.hs .Lmove_backward
 mov x3,x0
 cmp x2,#16
 b.lo .Lmove_forward_tail
.Lmove_forward_bulk:
 ldr q0,[x1],#16
 str q0,[x3],#16
 sub x2,x2,#16
 cmp x2,#16
 b.hs .Lmove_forward_bulk
.Lmove_forward_tail:
 cbz x2,.Lmove_forward_done
.Lmove_forward_byte:
 ldrb w4,[x1],#1
 strb w4,[x3],#1
 sub x2,x2,#1
 cbnz x2,.Lmove_forward_byte
.Lmove_forward_done:
 ret
.Lmove_backward:
 add x1,x1,x2
 add x3,x0,x2
 cmp x2,#16
 b.lo .Lmove_backward_small
 sub x1,x1,#16
 sub x3,x3,#16
.Lmove_backward_bulk:
 ldr q0,[x1],#-16
 str q0,[x3],#-16
 sub x2,x2,#16
 cmp x2,#16
 b.hs .Lmove_backward_bulk
.Lmove_backward_tail:
 cbz x2,.Lmove_backward_done
 add x1,x1,#15
 add x3,x3,#15
 b .Lmove_backward_byte
.Lmove_backward_small:
 sub x1,x1,#1
 sub x3,x3,#1
.Lmove_backward_byte:
 ldrb w4,[x1],#-1
 strb w4,[x3],#-1
 sub x2,x2,#1
 cbnz x2,.Lmove_backward_byte
.Lmove_backward_done:
 ret
.size memmove,.-memmove
.section .note.GNU-stack,"",%progbits

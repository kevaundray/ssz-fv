.text
.p2align 4
.global memcpy
.type memcpy,%function
memcpy:
 mov x3,x0
 cmp x2,#16
 b.lo .Lcopy_tail
.Lcopy_bulk:
 ldr q0,[x1],#16
 str q0,[x3],#16
 sub x2,x2,#16
 cmp x2,#16
 b.hs .Lcopy_bulk
.Lcopy_tail:
 cbz x2,.Lcopy_done
.Lcopy_byte:
 ldrb w4,[x1],#1
 strb w4,[x3],#1
 sub x2,x2,#1
 cbnz x2,.Lcopy_byte
.Lcopy_done:
 ret
.size memcpy,.-memcpy
.section .note.GNU-stack,"",%progbits

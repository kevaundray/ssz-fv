// AAPCS64 unsigned 128-bit division: X1:X0 / X3:X2 -> X1:X0.
// The divisor must be nonzero. No memory accesses or stack scratch.
// A one-word divisor uses one limb pass when the high quotient is zero,
// otherwise two passes. A two-word divisor has a one-word quotient.
.text
.p2align 4
.global __udivti3
.type __udivti3,%function
__udivti3:
    cmp x1, x3
    b.lo .Ludiv_zero
    b.hi .Ludiv_dispatch
    cmp x0, x2
    b.lo .Ludiv_zero
.Ludiv_dispatch:
    cbnz x3, .Ludiv_wide
    cmp x2, #1
    b.eq .Ludiv_one
    mov x4, x0
    mov x0, xzr
    mov x7, #64
    cmp x1, x2
    b.hs .Ludiv_high
    mov x6, x1
    mov x5, x4
    mov x1, xzr
    mov x8, xzr
    b .Ludiv_word_loop
.Ludiv_high:
    mov x6, xzr
    mov x5, x1
    mov x1, xzr
    mov x8, #1
.Ludiv_word_loop:
    add x0, x0, x0
    adds x5, x5, x5
    adcs x6, x6, x6
    b.cs .Ludiv_word_subtract
    cmp x6, x2
    b.lo .Ludiv_word_next
.Ludiv_word_subtract:
    sub x6, x6, x2
    add x0, x0, #1
.Ludiv_word_next:
    subs x7, x7, #1
    b.ne .Ludiv_word_loop
    cbz x8, .Ludiv_word_done
    mov x1, x0
    mov x0, xzr
    mov x5, x4
    mov x7, #64
    mov x8, xzr
    b .Ludiv_word_loop
.Ludiv_word_done:
    ret
.Ludiv_wide:
    mov x4, x0
    mov x5, x1
    mov x6, xzr
    mov x0, xzr
    mov x7, #64
.Ludiv_wide_loop:
    add x0, x0, x0
    adds x4, x4, x4
    adcs x5, x5, x5
    adc x6, x6, x6
    cmp x6, x3
    b.hi .Ludiv_wide_subtract
    b.lo .Ludiv_wide_next
    cmp x5, x2
    b.lo .Ludiv_wide_next
.Ludiv_wide_subtract:
    subs x5, x5, x2
    sbc x6, x6, x3
    add x0, x0, #1
.Ludiv_wide_next:
    subs x7, x7, #1
    b.ne .Ludiv_wide_loop
    mov x1, xzr
    ret
.Ludiv_one:
    ret
.Ludiv_zero:
    mov x0, xzr
    mov x1, xzr
    ret
.size __udivti3, .-__udivti3
.section .note.GNU-stack,"",%progbits

# SysV unsigned 128-bit division: RSI:RDI / RCX:RDX -> RDX:RAX.
# The divisor must be nonzero. No memory writes or stack scratch.
# A one-word divisor uses one limb pass when the high quotient is zero,
# otherwise two passes. A two-word divisor has a one-word quotient.
.text
.p2align 4
.global __udivti3
.type __udivti3,@function
__udivti3:
    cmpq %rcx, %rsi
    jb .Ludiv_zero
    ja .Ludiv_dispatch
    cmpq %rdx, %rdi
    jb .Ludiv_zero
.Ludiv_dispatch:
    testq %rcx, %rcx
    jnz .Ludiv_wide
    cmpq $1, %rdx
    je .Ludiv_one
    xorl %eax, %eax
    xorl %r8d, %r8d
    movl $64, %r11d
    cmpq %rdx, %rsi
    jae .Ludiv_high
    movq %rsi, %r9
    movq %rdi, %rsi
    xorl %r10d, %r10d
    jmp .Ludiv_word_loop
.Ludiv_high:
    xorl %r9d, %r9d
    movl $1, %r10d
.Ludiv_word_loop:
    addq %rax, %rax
    addq %rsi, %rsi
    adcq %r9, %r9
    jb .Ludiv_word_subtract
    cmpq %rdx, %r9
    jb .Ludiv_word_next
.Ludiv_word_subtract:
    subq %rdx, %r9
    addq $1, %rax
.Ludiv_word_next:
    subq $1, %r11
    jnz .Ludiv_word_loop
    testq %r10, %r10
    jnz .Ludiv_second
    movq %r8, %rdx
    ret
.Ludiv_second:
    movq %rax, %r8
    movq %rdi, %rsi
    xorl %eax, %eax
    movl $64, %r11d
    xorl %r10d, %r10d
    jmp .Ludiv_word_loop
.Ludiv_wide:
    movq %rsi, %r9
    xorl %r10d, %r10d
    xorl %eax, %eax
    movl $64, %r11d
.Ludiv_wide_loop:
    addq %rax, %rax
    addq %rdi, %rdi
    adcq %r9, %r9
    adcq %r10, %r10
    cmpq %rcx, %r10
    ja .Ludiv_wide_subtract
    jb .Ludiv_wide_next
    cmpq %rdx, %r9
    jb .Ludiv_wide_next
.Ludiv_wide_subtract:
    subq %rdx, %r9
    sbbq %rcx, %r10
    addq $1, %rax
.Ludiv_wide_next:
    subq $1, %r11
    jnz .Ludiv_wide_loop
    xorl %edx, %edx
    ret
.Ludiv_one:
    movq %rdi, %rax
    movq %rsi, %rdx
    ret
.Ludiv_zero:
    xorl %eax, %eax
    xorl %edx, %edx
    ret
.size __udivti3, .-__udivti3
.section .note.GNU-stack,"",@progbits

.text
.p2align 4
.global memcpy
.type memcpy,@function
memcpy:
 movq %rdi,%rax
 cmpq $8,%rdx
 jb .Lcopy_tail
.Lcopy_bulk:
 movq (%rsi),%r8
 movq %r8,(%rdi)
 addq $8,%rsi
 addq $8,%rdi
 subq $8,%rdx
 cmpq $8,%rdx
 jae .Lcopy_bulk
.Lcopy_tail:
 testq %rdx,%rdx
 jz .Lcopy_done
.Lcopy_byte:
 movb (%rsi),%cl
 movb %cl,(%rdi)
 addq $1,%rsi
 addq $1,%rdi
 subq $1,%rdx
 jnz .Lcopy_byte
.Lcopy_done:
 ret
.size memcpy,.-memcpy
.section .note.GNU-stack,"",@progbits

# SysV: RDI=destination, RSI=source, RDX=byte count; returns the original RDI.
# Caller provides readable/writable, nonwrapping buffer ranges. Overlap is allowed;
# every 8-byte chunk is loaded before it is stored. Zero length and equal pointers
# return without buffer access. No stack scratch; source may include the RET slot,
# but destination must not overwrite it or the immutable code image.
.text
.p2align 4
.global memmove
.type memmove,@function
memmove:
 movq %rdi,%rax
 testq %rdx,%rdx
 jz .Lmove_forward_done
 cmpq %rsi,%rdi
 je .Lmove_forward_done
 ja .Lmove_backward
 cmpq $8,%rdx
 jb .Lmove_forward_tail
.Lmove_forward_bulk:
 movq (%rsi),%r8
 movq %r8,(%rdi)
 addq $8,%rsi
 addq $8,%rdi
 subq $8,%rdx
 cmpq $8,%rdx
 jae .Lmove_forward_bulk
.Lmove_forward_tail:
 testq %rdx,%rdx
 jz .Lmove_forward_done
.Lmove_forward_byte:
 movb (%rsi),%cl
 movb %cl,(%rdi)
 addq $1,%rsi
 addq $1,%rdi
 subq $1,%rdx
 jnz .Lmove_forward_byte
.Lmove_forward_done:
 ret
.Lmove_backward:
 addq %rdx,%rsi
 addq %rdx,%rdi
 cmpq $8,%rdx
 jb .Lmove_backward_tail
.Lmove_backward_bulk:
 subq $8,%rsi
 subq $8,%rdi
 movq (%rsi),%r8
 movq %r8,(%rdi)
 subq $8,%rdx
 cmpq $8,%rdx
 jae .Lmove_backward_bulk
.Lmove_backward_tail:
 testq %rdx,%rdx
 jz .Lmove_backward_done
.Lmove_backward_byte:
 subq $1,%rsi
 subq $1,%rdi
 movb (%rsi),%cl
 movb %cl,(%rdi)
 subq $1,%rdx
 jnz .Lmove_backward_byte
.Lmove_backward_done:
 ret
.size memmove,.-memmove
.section .note.GNU-stack,"",@progbits

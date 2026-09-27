/* SysV: RDI destination, low byte of ESI fill value, RDX byte count.
 * Empty fills access no data; sub-word fills skip broadcast setup.
 * RAX returns the original destination; no stack space is used.
 */
.text
.p2align 4
.global memset
.type memset,@function
memset:
 movq %rdi,%rax
 cmpq $8,%rdx
 jb .Lfill_tail
 movzbl %sil,%r8d
 movabsq $0x0101010101010101,%r9
 imulq %r8,%r9
.Lfill_bulk:
 movq %r9,(%rdi)
 addq $8,%rdi
 subq $8,%rdx
 cmpq $8,%rdx
 jae .Lfill_bulk
.Lfill_tail:
 testq %rdx,%rdx
 jz .Lfill_done
.Lfill_byte:
 movb %sil,(%rdi)
 addq $1,%rdi
 subq $1,%rdx
 jnz .Lfill_byte
.Lfill_done:
 ret
.size memset,.-memset
.section .note.GNU-stack,"",@progbits

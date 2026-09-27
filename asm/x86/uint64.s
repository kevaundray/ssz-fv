	.file	"uint64.d86e5fdaafac4763-cgu.0"
	.section	.text.ssz_load_u64,"ax",@progbits
	.globl	ssz_load_u64
	.p2align	4
	.type	ssz_load_u64,@function
ssz_load_u64:
	.cfi_startproc
	movq	(%rdi), %rax
	retq
.Lfunc_end0:
	.size	ssz_load_u64, .Lfunc_end0-ssz_load_u64
	.cfi_endproc

	.section	.text.ssz_store_u64,"ax",@progbits
	.globl	ssz_store_u64
	.p2align	4
	.type	ssz_store_u64,@function
ssz_store_u64:
	.cfi_startproc
	movq	%rsi, (%rdi)
	retq
.Lfunc_end1:
	.size	ssz_store_u64, .Lfunc_end1-ssz_store_u64
	.cfi_endproc

	.ident	"rustc version 1.94.0 (4a4ef493e 2026-03-02)"
	.section	".note.GNU-stack","",@progbits

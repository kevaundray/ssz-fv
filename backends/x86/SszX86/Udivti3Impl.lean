import SszX86.Impl

namespace SszX86.Udivti3

open Kraken.X64.Parser

/-- The fixed, generic SysV unsigned-128 divider. Internal labels have the same
positions as the assembler's `.Ludiv_*` labels. -/
def program : Program := parse("
  cmpq %rcx, %rsi
  jb udiv_zero
  ja udiv_dispatch
  cmpq %rdx, %rdi
  jb udiv_zero
udiv_dispatch:
  testq %rcx, %rcx
  jnz udiv_wide
  cmpq $1, %rdx
  je udiv_one
  xorl %eax, %eax
  xorl %r8d, %r8d
  movl $64, %r11d
  cmpq %rdx, %rsi
  jae udiv_high
  movq %rsi, %r9
  movq %rdi, %rsi
  xorl %r10d, %r10d
  jmp udiv_word_loop
udiv_high:
  xorl %r9d, %r9d
  movl $1, %r10d
udiv_word_loop:
  addq %rax, %rax
  addq %rsi, %rsi
  adcq %r9, %r9
  jb udiv_word_subtract
  cmpq %rdx, %r9
  jb udiv_word_next
udiv_word_subtract:
  subq %rdx, %r9
  addq $1, %rax
udiv_word_next:
  subq $1, %r11
  jnz udiv_word_loop
  testq %r10, %r10
  jnz udiv_second
  movq %r8, %rdx
  ret
udiv_second:
  movq %rax, %r8
  movq %rdi, %rsi
  xorl %eax, %eax
  movl $64, %r11d
  xorl %r10d, %r10d
  jmp udiv_word_loop
udiv_wide:
  movq %rsi, %r9
  xorl %r10d, %r10d
  xorl %eax, %eax
  movl $64, %r11d
udiv_wide_loop:
  addq %rax, %rax
  addq %rdi, %rdi
  adcq %r9, %r9
  adcq %r10, %r10
  cmpq %rcx, %r10
  ja udiv_wide_subtract
  jb udiv_wide_next
  cmpq %rdx, %r9
  jb udiv_wide_next
udiv_wide_subtract:
  subq %rdx, %r9
  sbbq %rcx, %r10
  addq $1, %rax
udiv_wide_next:
  subq $1, %r11
  jnz udiv_wide_loop
  xorl %edx, %edx
  ret
udiv_one:
  movq %rdi, %rax
  movq %rsi, %rdx
  ret
udiv_zero:
  xorl %eax, %eax
  xorl %edx, %edx
  ret
")

/-- Exact assembled lengths, including zero-byte labels; total size 197. -/
@[instance_reducible]
def layout (base : Int64) : Layout :=
  { start := base
    size := fun i =>
      [3, 6, 2, 3, 6, 0, 3, 2, 4, 6, 2, 3, 6, 3, 2, 3, 3, 3, 2,
       0, 3, 6, 0, 3, 3, 3, 2, 3, 2, 0, 3, 4, 0, 4, 2, 3, 2, 3, 1,
       0, 3, 3, 2, 6, 3, 2, 0, 3, 3, 2, 6, 0, 3, 3, 3, 3, 3, 2, 2,
       3, 2, 0, 3, 3, 4, 0, 4, 2, 2, 1, 0, 3, 3, 1, 0, 2, 2, 1][i]?.getD 0 }

def executable (base : Int64) : Executable := layout base program

abbrev step (base : Int64) := @step1 (layout base) (executable base)

end SszX86.Udivti3

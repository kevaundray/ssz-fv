import SszX86.Impl

namespace SszX86

open Kraken.X64.Parser

/-- The complete memmove, with a separate RET for each direction so that every
conditional branch has a short displacement. Code and data remain separate in
Kraken; mapped ordinary byte memory is the runtime contract. -/
def memmoveProgram : Program := parse("
  movq %rdi, %rax
  testq %rdx, %rdx
  jz move_forward_done
  cmpq %rsi, %rdi
  je move_forward_done
  ja move_backward
  cmpq $8, %rdx
  jb move_forward_tail
move_forward_bulk:
  movq (%rsi), %r8
  movq %r8, (%rdi)
  addq $8, %rsi
  addq $8, %rdi
  subq $8, %rdx
  cmpq $8, %rdx
  jae move_forward_bulk
move_forward_tail:
  testq %rdx, %rdx
  jz move_forward_done
move_forward_byte:
  movb (%rsi), %cl
  movb %cl, (%rdi)
  addq $1, %rsi
  addq $1, %rdi
  subq $1, %rdx
  jnz move_forward_byte
move_forward_done:
  ret
move_backward:
  addq %rdx, %rsi
  addq %rdx, %rdi
  cmpq $8, %rdx
  jb move_backward_tail
move_backward_bulk:
  subq $8, %rsi
  subq $8, %rdi
  movq (%rsi), %r8
  movq %r8, (%rdi)
  subq $8, %rdx
  cmpq $8, %rdx
  jae move_backward_bulk
move_backward_tail:
  testq %rdx, %rdx
  jz move_backward_done
move_backward_byte:
  subq $1, %rsi
  subq $1, %rdi
  movb (%rsi), %cl
  movb %cl, (%rdi)
  subq $1, %rdx
  jnz move_backward_byte
move_backward_done:
  ret
")

/-- Actual instruction sizes, not the parser's hash-based fake layout. -/
@[instance_reducible]
def memmoveLayout (base : Int64) : Layout :=
  { start := base
    size := fun i =>
      [3,3,2,3,2,2,4,2,0,3,3,4,4,4,4,2,0,3,2,0,2,2,4,4,4,2,0,1,
       0,3,3,4,2,0,4,4,3,3,4,4,2,0,3,2,0,4,4,2,2,4,2,0,1][i]?.getD 0 }

def memmoveExecutable (base : Int64) : Executable := memmoveLayout base memmoveProgram

end SszX86

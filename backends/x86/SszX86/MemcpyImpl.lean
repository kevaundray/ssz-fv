import SszX86.Impl

namespace SszX86

open Kraken.X64.Parser

/-- The nineteen instructions in `asm/x86/memcpy.s`, including both loops and
`ret`. Labels occupy no bytes. The layout below is the actual assembler layout,
not Kraken's hash-based `fakeLayout`. -/
def memcpyProgram : Program := parse("
  movq %rdi, %rax
  cmpq $8, %rdx
  jb copy_tail
copy_bulk:
  movq (%rsi), %r8
  movq %r8, (%rdi)
  addq $8, %rsi
  addq $8, %rdi
  subq $8, %rdx
  cmpq $8, %rdx
  jae copy_bulk
copy_tail:
  testq %rdx, %rdx
  jz copy_done
copy_byte:
  movb (%rsi), %cl
  movb %cl, (%rdi)
  addq $1, %rsi
  addq $1, %rdi
  subq $1, %rdx
  jnz copy_byte
copy_done:
  ret
")

/-- Byte offsets are relative to the actual symbol address `base`. -/
@[instance_reducible]
def memcpyLayout (base : Int64) : Layout :=
  { start := base
    size := fun i =>
      [3, 4, 2, 0, 3, 3, 4, 4, 4, 4, 2, 0, 3, 2, 0, 2, 2, 4, 4, 4, 2, 0, 1][i]?.getD 0 }

def memcpyExecutable (base : Int64) : Executable := memcpyLayout base memcpyProgram

end SszX86

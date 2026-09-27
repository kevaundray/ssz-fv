import SszX86.Impl

namespace SszX86

open Kraken.X64.Parser

/-- The actual eighteen instructions in `asm/x86/memset.s`, including both
loops and `ret`. Labels occupy no bytes. The layout below is the actual
assembler layout, not Kraken's hash-based `fakeLayout`. -/
def memsetProgram : Program := parse("
  movq %rdi, %rax
  cmpq $8, %rdx
  jb tail44
  movzbl %sil, %r8d
  movabsq $0x0101010101010101, %r9
  imulq %r8, %r9
bulk27:
  movq %r9, (%rdi)
  addq $8, %rdi
  subq $8, %rdx
  cmpq $8, %rdx
  jae bulk27
tail44:
  testq %rdx, %rdx
  jz done62
byte49:
  movb %sil, (%rdi)
  addq $1, %rdi
  subq $1, %rdx
  jnz byte49
done62:
  ret
")

/-- Byte offsets are relative to the actual symbol address `base`. -/
@[instance_reducible]
def memsetLayout (base : Int64) : Layout :=
  { start := base
    size := fun i =>
      [3, 4, 2, 4, 10, 4, 0, 3, 4, 4, 4, 2, 0, 3, 2, 0, 3, 4, 4, 2, 0, 1][i]?.getD 0 }

def memsetExecutable (base : Int64) : Executable := memsetLayout base memsetProgram

end SszX86

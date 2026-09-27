import SszX86.Impl

namespace SszX86

open Kraken.X64.Parser

/-- Explicit ASTs are necessary because the pinned parser accepts only register
sources for MOVZX. These are the ordinary pinned ISA memory-load operations. -/
def memcmpLoadLeft : Directive := .instr (.regular .W64 .W32
  (.movzx (.reg .eax) (.mem (w := .W8) { base := some (.reg .rdi), idx := none })))
def memcmpLoadRight : Directive := .instr (.regular .W64 .W32
  (.movzx (.reg .ecx) (.mem (w := .W8) { base := some (.reg .rsi), idx := none })))

def memcmpProgram : Program :=
  parse("
    xorl %eax, %eax
    testq %rdx, %rdx
    jz done31
  loop7:
  ") ++ [memcmpLoadLeft, memcmpLoadRight] ++ parse("
    subl %ecx, %eax
    jnz done31
    addq $1, %rdi
    addq $1, %rsi
    subq $1, %rdx
    jnz loop7
  done31:
    ret
  ")

/-- The real 32-byte object layout, including zero-size labels. -/
@[instance_reducible]
def memcmpLayout (base : Int64) : Layout :=
  { start := base
    size := fun i => [2, 3, 2, 0, 3, 3, 2, 2, 4, 4, 4, 2, 0, 1][i]?.getD 0 }

def memcmpExecutable (base : Int64) : Executable := memcmpLayout base memcmpProgram

end SszX86

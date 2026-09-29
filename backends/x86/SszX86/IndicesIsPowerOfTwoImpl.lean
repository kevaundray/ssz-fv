module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesIsPowerOfTwo
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2166000
def machineSize : Nat := 119

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rdi,%rdi")),
  (3, 2, parse("je indices_is_power_of_two_u91")),
  (5, 4, parse("leaq 0x1(%rsi),%rax")),
  (9, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (16, 4, parse("cmpq $0x1,%rax")),
  (20, 2, parse("je indices_is_power_of_two_u109")),
  (22, 4, parse("leaq -0x1(%rax),%rcx")),
  (26, 6, parse("cmpq $0x0,-0x10(%rdi,%rax,8)")),
  (32, 3, parse("movq %rcx,%rax")),
  (35, 2, parse("je indices_is_power_of_two_u16")),
  (37, 2, parse("xorl %edx,%edx")),
  (39, 3, parse("xorl %r8d,%r8d")),
  (42, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (12)))))]),
  (44, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (48, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r8 .W64))))]),
  (51, 3, parse("cmpq %r8,%rcx")),
  (54, 2, parse("je indices_is_power_of_two_u114")),
  (56, 3, parse("cmpq %rsi,%r8")),
  (59, 2, parse("jae indices_is_power_of_two_u48")),
  (61, 4, parse("movq (%rdi,%r8,8),%r9")),
  (65, 3, parse("testq %r9,%r9")),
  (68, 2, parse("je indices_is_power_of_two_u48")),
  (70, 2, parse("xorl %eax,%eax")),
  (72, 3, parse("testb $0x1,%dl")),
  (75, 2, parse("jne indices_is_power_of_two_u88")),
  (77, 4, parse("leaq -0x1(%r9),%r10")),
  (81, 2, parse("movb $0x1,%dl")),
  (83, 3, parse("andq %r9,%r10")),
  (86, 2, parse("je indices_is_power_of_two_u48")),
  (88, 2, parse("andb $0x1,%al")),
  (90, 1, parse("retq ")),
  (91, 3, parse("testq %rsi,%rsi")),
  (94, 2, parse("je indices_is_power_of_two_u109")),
  (96, 4, parse("leaq -0x1(%rsi),%rax")),
  (100, 3, parse("testq %rax,%rsi")),
  (103, 3, parse("sete %al")),
  (106, 2, parse("andb $0x1,%al")),
  (108, 1, parse("retq ")),
  (109, 2, parse("xorl %eax,%eax")),
  (111, 2, parse("andb $0x1,%al")),
  (113, 1, parse("retq ")),
  (114, 2, parse("movl %edx,%eax")),
  (116, 2, parse("andb $0x1,%al")),
  (118, 1, parse("retq "))]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 44 := by
  have h0 : programChunk0.length = 44 := by rfl
  simp only [program, List.length_append, h0]

def labels : List (String × Nat) := [
  ("indices_is_power_of_two_u16", 16),
  ("indices_is_power_of_two_u48", 48),
  ("indices_is_power_of_two_u88", 88),
  ("indices_is_power_of_two_u91", 91),
  ("indices_is_power_of_two_u109", 109),
  ("indices_is_power_of_two_u114", 114)]


def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, BoolCodec.step, step1, Executable.step, hc.fetch row hr]

end SszX86.IndicesIsPowerOfTwo

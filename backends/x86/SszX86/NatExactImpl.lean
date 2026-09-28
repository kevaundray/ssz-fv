module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatExact
open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def entry : Nat := 0

def program : List (Nat × Nat × Program) := [
  (0, 3, parse("movq (%rsi),%r8")),
  (3, 4, parse("movq 0x8(%rsi),%rcx")),
  (7, 2, parse("xorl %eax,%eax")),
  (9, 3, parse("testq %r8,%r8")),
  (12, 2, parse("je natExact_u61")),
  (14, 4, parse("leaq 0x1(%rcx),%r9")),
  (18, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (28, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (32, 4, parse("cmpq $0x1,%r9")),
  (36, 2, parse("je natExact_u74")),
  (38, 4, parse("leaq -0x1(%r9),%r10")),
  (42, 6, parse("cmpq $0x0,-0x10(%r8,%r9,8)")),
  (48, 3, parse("movq %r10,%r9")),
  (51, 2, parse("je natExact_u32")),
  (53, 4, parse("cmpq $0x3,%r10")),
  (57, 2, parse("jb natExact_u79")),
  (59, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (47)))))]),
  (61, 3, parse("xorl %r8d,%r8d")),
  (64, 3, parse("xorq %rdx,%rcx")),
  (67, 3, parse("orq %r8,%rcx")),
  (70, 2, parse("jne natExact_u108")),
  (72, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (97)))))]),
  (74, 3, parse("testq %rcx,%rcx")),
  (77, 2, parse("je natExact_u175")),
  (79, 3, parse("movq (%r8),%r9")),
  (82, 4, parse("cmpq $0x2,%rcx")),
  (86, 2, parse("jb natExact_u94")),
  (88, 4, parse("movq 0x8(%r8),%r8")),
  (92, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3)))))]),
  (94, 3, parse("xorl %r8d,%r8d")),
  (97, 3, parse("movq %r9,%rcx")),
  (100, 3, parse("xorq %rdx,%rcx")),
  (103, 3, parse("orq %r8,%rcx")),
  (106, 2, parse("je natExact_u171")),
  (108, 7, parse("movq $0x1,(%rdi)")),
  (115, 8, parse("movq $0x0,0x8(%rdi)")),
  (123, 3, parse("movq (%rsi),%rax")),
  (126, 4, parse("movq 0x8(%rsi),%rcx")),
  (130, 4, parse("movq %rax,0x10(%rdi)")),
  (134, 4, parse("movq %rcx,0x18(%rdi)")),
  (138, 8, parse("movq $0x0,0x20(%rdi)")),
  (146, 4, parse("movq %rdx,0x28(%rdi)")),
  (150, 8, parse("movq $0x0,0x30(%rdi)")),
  (158, 8, parse("movq $0x0,0x38(%rdi)")),
  (166, 5, parse("movl $0x3,%eax")),
  (171, 3, parse("movl %eax,0x40(%rdi)")),
  (174, 1, parse("retq ")),
  (175, 3, parse("xorl %r8d,%r8d")),
  (178, 2, parse("xorl %ecx,%ecx")),
  (180, 3, parse("xorq %rdx,%rcx")),
  (183, 3, parse("orq %r8,%rcx")),
  (186, 2, parse("jne natExact_u108")),
  (188, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-19)))))])]

def labels : List (String × Nat) := [
  ("natExact_u32", 32),
  ("natExact_u61", 61),
  ("natExact_u74", 74),
  ("natExact_u79", 79),
  ("natExact_u94", 94),
  ("natExact_u108", 108),
  ("natExact_u171", 171),
  ("natExact_u175", 175)]

theorem all_instructions : program.all (fun row => match row.2.2 with
    | [.instr _] => true
    | _ => false) = true := by decide

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

@[instance_reducible]
def layout (e : Executable) : Layout :=
  { start := e.1, size := fun i => (e.2[i]?.map Prod.snd).getD 0 }

abbrev step (e : Executable) := @step1 (layout e) e

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, step1, Executable.step, hc.fetch row hr]

end SszX86.NatExact

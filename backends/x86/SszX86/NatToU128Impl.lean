module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatToU128
open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def entry : Nat := 0

def program : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rsi,%rsi")),
  (3, 2, parse("je natToU128_u58")),
  (5, 4, parse("leaq 0x1(%rdx),%rax")),
  (9, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (16, 4, parse("cmpq $0x1,%rax")),
  (20, 2, parse("je natToU128_u62")),
  (22, 4, parse("leaq -0x1(%rax),%r8")),
  (26, 6, parse("cmpq $0x0,-0x10(%rsi,%rax,8)")),
  (32, 3, parse("movq %r8,%rax")),
  (35, 2, parse("je natToU128_u16")),
  (37, 2, parse("xorl %eax,%eax")),
  (39, 5, parse("movl $0x0,%ecx")),
  (44, 4, parse("cmpq $0x3,%r8")),
  (48, 2, parse("jb natToU128_u67")),
  (50, 3, parse("movq %rax,(%rdi)")),
  (53, 4, parse("movq %rcx,0x8(%rdi)")),
  (57, 1, parse("retq ")),
  (58, 2, parse("xorl %eax,%eax")),
  (60, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (34)))))]),
  (62, 3, parse("testq %rdx,%rdx")),
  (65, 2, parse("je natToU128_u92")),
  (67, 3, parse("movq (%rsi),%rcx")),
  (70, 4, parse("cmpq $0x2,%rdx")),
  (74, 2, parse("jb natToU128_u85")),
  (76, 4, parse("movq 0x8(%rsi),%rax")),
  (80, 3, parse("movq %rcx,%rdx")),
  (83, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (11)))))]),
  (85, 2, parse("xorl %eax,%eax")),
  (87, 3, parse("movq %rcx,%rdx")),
  (90, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (4)))))]),
  (92, 2, parse("xorl %eax,%eax")),
  (94, 2, parse("xorl %edx,%edx")),
  (96, 4, parse("movq %rax,0x18(%rdi)")),
  (100, 4, parse("movq %rdx,0x10(%rdi)")),
  (104, 5, parse("movl $0x1,%eax")),
  (109, 2, parse("xorl %ecx,%ecx")),
  (111, 3, parse("movq %rax,(%rdi)")),
  (114, 4, parse("movq %rcx,0x8(%rdi)")),
  (118, 1, parse("retq "))]

def labels : List (String × Nat) := [
  ("natToU128_u16", 16),
  ("natToU128_u58", 58),
  ("natToU128_u62", 62),
  ("natToU128_u67", 67),
  ("natToU128_u85", 85),
  ("natToU128_u92", 92)]

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

end SszX86.NatToU128

module

public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics

@[expose] public section

namespace SszX86.BoolCodec
open Kraken.X64.Parser

def entry : Nat := 45

/-- Actual postdispatch Boolean instructions: function-relative PC, encoded
width, and ISA directives. Gaps are other native decoder branches, NOT padding.
Unconditional jumps carry the actual next-PC-relative displacement. -/
def program : List (Nat × Nat × Program) := [
  (45, 4, parse("cmpq $0x1,%r14")),
  (49, 6, parse("jne boolScope")),
  (55, 3, [.instr (.regular .W64 .W32 (.movzx (.reg .eax) (.mem (w := .W8) { base := some (.reg .rdx), idx := none })))]),
  (58, 2, parse("testl %eax,%eax")),
  (60, 6, parse("je boolZero")),
  (66, 3, parse("cmpl $0x1,%eax")),
  (69, 6, parse("jne boolBad")),
  (75, 6, parse("movw $0x100,0x10(%rdi)")),
  (81, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 5428))))]),
  (1580, 8, parse("movq $0x0,0x40(%rdi)")),
  (1588, 8, parse("movq $0x0,0x38(%rdi)")),
  (1596, 8, parse("movq $0x0,0x18(%rdi)")),
  (1604, 8, parse("movq $0x1,0x20(%rdi)")),
  (1612, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 2365))))]),
  (2663, 6, parse("movw $0x0,0x10(%rdi)")),
  (2669, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 2840))))]),
  (2674, 8, parse("movq $0x0,0x40(%rdi)")),
  (2682, 8, parse("movq $0x0,0x38(%rdi)")),
  (2690, 8, parse("movq $0x0,0x30(%rdi)")),
  (2698, 8, parse("movq $0x0,0x28(%rdi)")),
  (2706, 8, parse("movq $0x1,0x8(%rdi)")),
  (2714, 8, parse("movq $0x0,0x10(%rdi)")),
  (2722, 8, parse("movq $0x0,0x18(%rdi)")),
  (2730, 4, parse("movq %rax,0x20(%rdi)")),
  (2734, 7, parse("movl $0xd,0x48(%rdi)")),
  (2741, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 4967))))]),
  (3982, 8, parse("movq $0x1,0x8(%rdi)")),
  (3990, 8, parse("movq $0x0,0x10(%rdi)")),
  (3998, 8, parse("movq $0x0,0x28(%rdi)")),
  (4006, 4, parse("movq %r14,0x30(%rdi)")),
  (4010, 7, parse("movl $0x3,0x48(%rdi)")),
  (4017, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 3691))))]),
  (5514, 7, parse("movq $0x0,(%rdi)")),
  (5521, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 2194))))]),
  (7713, 7, parse("movq $0x1,(%rdi)")),
  (7720, 7, parse("addq $0x138,%rsp")),
  (7727, 1, parse("popq %rbx")),
  (7728, 2, parse("popq %r12")),
  (7730, 2, parse("popq %r13")),
  (7732, 2, parse("popq %r14")),
  (7734, 2, parse("popq %r15")),
  (7736, 1, parse("popq %rbp")),
  (7737, 1, parse("retq "))]

/-- Labels are only metadata for Kraken's conditional-branch representation. -/
def labels : List (String × Nat) :=
  [("boolScope", 1580), ("boolZero", 2663), ("boolBad", 2674)]

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

/-- Selected fetches in the ambient executable. Other native branches remain
unconstrained. Conditional targets are explicit; labels at their destination
are included in the fetch lists, so these hypotheses are jointly realizable. -/
structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

/-- The nominal layout is derived from the ambient executable's real sizes;
`step1` itself executes the size-tagged directives fetched from `e`. -/
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

end SszX86.BoolCodec

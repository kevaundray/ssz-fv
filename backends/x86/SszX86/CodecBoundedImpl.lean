module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecBounded
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2220688
def machineSize : Nat := 122

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r12")),
  (7, 1, parse("pushq %rbx")),
  (8, 3, parse("movq %rdi,%rbx")),
  (11, 2, parse("xorl %ebp,%ebp")),
  (13, 3, parse("cmpl $0x1,(%rsi)")),
  (16, 2, parse("jne codec_bounded_u110")),
  (18, 3, parse("movq %rdx,%r14")),
  (21, 4, parse("movq 0x8(%rsi),%r15")),
  (25, 4, parse("movq 0x10(%rsi),%r12")),
  (29, 3, parse("movq (%rdx),%rdi")),
  (32, 4, parse("movq 0x8(%rdx),%rsi")),
  (36, 3, parse("movq %r15,%rdx")),
  (39, 3, parse("movq %r12,%rcx")),
  (42, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-66287)))))]),
  (47, 2, parse("testb %al,%al")),
  (49, 2, parse("jle codec_bounded_u110")),
  (51, 7, parse("movq $0x1,(%rbx)")),
  (58, 8, parse("movq $0x0,0x8(%rbx)")),
  (66, 4, parse("movq %r15,0x10(%rbx)")),
  (70, 4, parse("movq %r12,0x18(%rbx)")),
  (74, 3, parse("movq (%r14),%rax")),
  (77, 4, parse("movq 0x8(%r14),%rcx")),
  (81, 4, parse("movq %rax,0x20(%rbx)")),
  (85, 4, parse("movq %rcx,0x28(%rbx)")),
  (89, 8, parse("movq $0x0,0x30(%rbx)")),
  (97, 8, parse("movq $0x0,0x38(%rbx)")),
  (105, 5, parse("movl $0x2,%ebp")),
  (110, 3, parse("movl %ebp,0x40(%rbx)")),
  (113, 1, parse("popq %rbx")),
  (114, 2, parse("popq %r12")),
  (116, 2, parse("popq %r14")),
  (118, 2, parse("popq %r15")),
  (120, 1, parse("popq %rbp")),
  (121, 1, parse("retq "))]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 37 := by
  have h0 : programChunk0.length = 37 := by rfl
  simp only [program, h0]

def labels : List (String × Nat) := [
  ("codec_bounded_u110", 110)]

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

def natCompareOffset : Int := -66240

end SszX86.CodecBounded

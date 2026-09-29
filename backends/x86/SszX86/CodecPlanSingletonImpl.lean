module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecPlanSingleton
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2195472
def machineSize : Nat := 193

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 3, parse("movq (%rsi),%rax")),
  (3, 4, parse("movq 0x10(%rsi),%r8")),
  (7, 3, parse("movq %r8,%r9")),
  (10, 3, parse("addq %rax,%r9")),
  (13, 2, parse("jb codec_plan_singleton_u122")),
  (15, 4, parse("cmpq $0xfffffffffffffff8,%r9")),
  (19, 2, parse("ja codec_plan_singleton_u122")),
  (21, 4, parse("leaq 0x7(%r9),%rcx")),
  (25, 4, parse("andq $0xfffffffffffffff8,%rcx")),
  (29, 3, parse("subq %r9,%rcx")),
  (32, 3, parse("addq %r8,%rcx")),
  (35, 2, parse("jb codec_plan_singleton_u122")),
  (37, 4, parse("cmpq $0xffffffffffffffd7,%rcx")),
  (41, 2, parse("ja codec_plan_singleton_u122")),
  (43, 4, parse("leaq 0x28(%rcx),%r8")),
  (47, 4, parse("cmpq 0x8(%rsi),%r8")),
  (51, 2, parse("ja codec_plan_singleton_u122")),
  (53, 4, parse("movq %r8,0x10(%rsi)")),
  (57, 4, parse("leaq (%rax,%rcx,1),%rsi")),
  (61, 4, parse("movq 0x20(%rdx),%r8")),
  (65, 5, parse("movq %r8,0x20(%rax,%rcx,1)")),
  (70, 4, parse("movq 0x18(%rdx),%r8")),
  (74, 5, parse("movq %r8,0x18(%rax,%rcx,1)")),
  (79, 4, parse("movq 0x10(%rdx),%r8")),
  (83, 5, parse("movq %r8,0x10(%rax,%rcx,1)")),
  (88, 3, parse("movq (%rdx),%r8")),
  (91, 4, parse("movq 0x8(%rdx),%rdx")),
  (95, 5, parse("movq %rdx,0x8(%rax,%rcx,1)")),
  (100, 4, parse("movq %r8,(%rax,%rcx,1)")),
  (104, 2, parse("xorl %eax,%eax")),
  (106, 5, parse("movl $0x1,%ecx")),
  (111, 3, parse("movq %rsi,(%rdi)")),
  (114, 4, parse("movq %rcx,0x8(%rdi)")),
  (118, 3, parse("movl %eax,0x40(%rdi)")),
  (121, 1, parse("retq ")),
  (122, 8, parse("movq $0x0,0x38(%rdi)")),
  (130, 8, parse("movq $0x0,0x30(%rdi)")),
  (138, 8, parse("movq $0x0,0x28(%rdi)")),
  (146, 8, parse("movq $0x0,0x20(%rdi)")),
  (154, 8, parse("movq $0x0,0x18(%rdi)")),
  (162, 8, parse("movq $0x0,0x10(%rdi)")),
  (170, 5, parse("movl $0x8000,%eax")),
  (175, 5, parse("movl $0x1,%esi")),
  (180, 2, parse("xorl %ecx,%ecx")),
  (182, 3, parse("movq %rsi,(%rdi)")),
  (185, 4, parse("movq %rcx,0x8(%rdi)")),
  (189, 3, parse("movl %eax,0x40(%rdi)")),
  (192, 1, parse("retq "))]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 48 := by
  have h0 : programChunk0.length = 48 := by rfl
  simp only [program, h0]

def labels : List (String × Nat) := [
  ("codec_plan_singleton_u122", 122)]

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

end SszX86.CodecPlanSingleton

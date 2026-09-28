module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatFromU128
open Kraken.X64.Parser

def entry : Nat := 0

def program : List (Nat × Nat × Program) := [
  (0, 2, parse("xorl %eax,%eax")),
  (2, 3, parse("testq %rdx,%rdx")),
  (5, 2, parse("jne natFromU128_u20")),
  (7, 2, parse("xorl %ecx,%ecx")),
  (9, 3, parse("movq %rcx,(%rdi)")),
  (12, 4, parse("movq %rsi,0x8(%rdi)")),
  (16, 3, parse("movl %eax,0x40(%rdi)")),
  (19, 1, parse("retq ")),
  (20, 3, parse("movq (%rcx),%r8")),
  (23, 4, parse("movq 0x10(%rcx),%r10")),
  (27, 3, parse("movq %r10,%r11")),
  (30, 3, parse("addq %r8,%r11")),
  (33, 2, parse("jb natFromU128_u106")),
  (35, 4, parse("cmpq $0xfffffffffffffff8,%r11")),
  (39, 2, parse("ja natFromU128_u106")),
  (41, 4, parse("leaq 0x7(%r11),%r9")),
  (45, 4, parse("andq $0xfffffffffffffff8,%r9")),
  (49, 3, parse("subq %r11,%r9")),
  (52, 3, parse("addq %r10,%r9")),
  (55, 2, parse("jb natFromU128_u106")),
  (57, 4, parse("cmpq $0xffffffffffffffef,%r9")),
  (61, 2, parse("ja natFromU128_u106")),
  (63, 4, parse("leaq 0x10(%r9),%r10")),
  (67, 4, parse("cmpq 0x8(%rcx),%r10")),
  (71, 2, parse("ja natFromU128_u106")),
  (73, 4, parse("movq %r10,0x10(%rcx)")),
  (77, 4, parse("leaq (%r8,%r9,1),%rcx")),
  (81, 4, parse("movq %rsi,(%r8,%r9,1)")),
  (85, 5, parse("movq %rdx,0x8(%r8,%r9,1)")),
  (90, 5, parse("movl $0x2,%esi")),
  (95, 3, parse("movq %rcx,(%rdi)")),
  (98, 4, parse("movq %rsi,0x8(%rdi)")),
  (102, 3, parse("movl %eax,0x40(%rdi)")),
  (105, 1, parse("retq ")),
  (106, 8, parse("movq $0x0,0x38(%rdi)")),
  (114, 8, parse("movq $0x0,0x30(%rdi)")),
  (122, 8, parse("movq $0x0,0x28(%rdi)")),
  (130, 8, parse("movq $0x0,0x20(%rdi)")),
  (138, 8, parse("movq $0x0,0x18(%rdi)")),
  (146, 8, parse("movq $0x0,0x10(%rdi)")),
  (154, 5, parse("movl $0x8000,%eax")),
  (159, 5, parse("movl $0x1,%ecx")),
  (164, 2, parse("xorl %esi,%esi")),
  (166, 3, parse("movq %rcx,(%rdi)")),
  (169, 4, parse("movq %rsi,0x8(%rdi)")),
  (173, 3, parse("movl %eax,0x40(%rdi)")),
  (176, 1, parse("retq "))]

def labels : List (String × Nat) := [
  ("natFromU128_u20", 20),
  ("natFromU128_u106", 106)]

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

end SszX86.NatFromU128

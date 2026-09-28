module

public import SszX86.DelimitedImpl

@[expose] public section

namespace SszX86.BitList
open Kraken.X64.Parser

def listEntry : Nat := 1192
def progressiveEntry : Nat := 1240
def delimitedOffset : Int := 8960

def program : List (Nat × Nat × Program) := [
  (1192, 4, parse("movq 0x8(%rbp),%rax")),
  (1196, 4, parse("movq 0x10(%rbp),%rcx")),
  (1200, 5, parse("movq %rcx,0x20(%rsp)")),
  (1205, 5, parse("movq %rax,0x18(%rsp)")),
  (1210, 9, parse("movq $0x1,0x10(%rsp)")),
  (1219, 5, parse("leaq 0x10(%rsp),%rsi")),
  (1224, 3, parse("movq %r14,%rcx")),
  (1227, 3, parse("movq %rbx,%r8")),
  (1230, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 7725))))]),
  (1235, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 6480))))]),
  (1240, 4, parse("addq $0x8,%rbp")),
  (1244, 3, parse("movq %rbp,%rsi")),
  (1247, 3, parse("movq %r14,%rcx")),
  (1250, 3, parse("movq %rbx,%r8")),
  (1253, 7, parse("addq $0x138,%rsp")),
  (1260, 1, parse("popq %rbx")),
  (1261, 2, parse("popq %r12")),
  (1263, 2, parse("popq %r13")),
  (1265, 2, parse("popq %r14")),
  (1267, 2, parse("popq %r15")),
  (1269, 1, parse("popq %rbp")),
  (1270, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 7685))))]),
  (7720, 7, parse("addq $0x138,%rsp")),
  (7727, 1, parse("popq %rbx")),
  (7728, 2, parse("popq %r12")),
  (7730, 2, parse("popq %r13")),
  (7732, 2, parse("popq %r14")),
  (7734, 2, parse("popq %r15")),
  (7736, 1, parse("popq %rbp")),
  (7737, 1, parse("retq "))]

theorem all_instructions : program.all (fun row => match row.2.2 with
    | [.instr _] => true | _ => false) = true := by decide

def labels : List (String × Nat) := []

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row

structure JointCodeAt (e : Executable) (base : Int64) : Prop where
  body : CodeAt e base
  delimited : Delimited.CodeAt e (base + Int64.ofInt delimitedOffset)
  compare : NatCompare.CodeAt e
    ((base + Int64.ofInt delimitedOffset) + Int64.ofInt Delimited.compareOffset)

abbrev step := Delimited.step

theorem step_at (e : Executable) (base : Int64) (hc : CodeAt e base)
    (row : Nat × Nat × Program) (hr : row ∈ program)
    (s : MachineData) (post : MachineState → Prop) :
    step e (s, base + Int64.ofNat row.1) post ↔
      (@Directives.interp e.labels (directives row) s (base + Int64.ofNat row.1)
        (fun pc state => .done (state, pc))).All post := by
  simp only [step, Delimited.step, step1, Executable.step, hc.fetch row hr]

end SszX86.BitList

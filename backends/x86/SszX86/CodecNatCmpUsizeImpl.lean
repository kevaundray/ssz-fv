module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecNatCmpUsize
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2172512
def machineSize : Nat := 102

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rdi,%rdi")),
  (3, 2, parse("je codec_nat_cmp_usize_u46")),
  (5, 4, parse("leaq 0x1(%rsi),%rax")),
  (9, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (16, 4, parse("cmpq $0x1,%rax")),
  (20, 2, parse("je codec_nat_cmp_usize_u50")),
  (22, 4, parse("leaq -0x1(%rax),%rcx")),
  (26, 6, parse("cmpq $0x0,-0x10(%rdi,%rax,8)")),
  (32, 3, parse("movq %rcx,%rax")),
  (35, 2, parse("je codec_nat_cmp_usize_u16")),
  (37, 4, parse("cmpq $0x3,%rcx")),
  (41, 2, parse("jb codec_nat_cmp_usize_u55")),
  (43, 2, parse("movb $0x1,%al")),
  (45, 1, parse("retq ")),
  (46, 2, parse("xorl %ecx,%ecx")),
  (48, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (31)))))]),
  (50, 3, parse("testq %rsi,%rsi")),
  (53, 2, parse("je codec_nat_cmp_usize_u77")),
  (55, 3, parse("movq (%rdi),%rax")),
  (58, 4, parse("cmpq $0x2,%rsi")),
  (62, 2, parse("jb codec_nat_cmp_usize_u70")),
  (64, 4, parse("movq 0x8(%rdi),%rcx")),
  (68, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2)))))]),
  (70, 2, parse("xorl %ecx,%ecx")),
  (72, 3, parse("movq %rax,%rsi")),
  (75, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (4)))))]),
  (77, 2, parse("xorl %ecx,%ecx")),
  (79, 2, parse("xorl %esi,%esi")),
  (81, 2, parse("xorl %eax,%eax")),
  (83, 3, parse("cmpq %rsi,%rdx")),
  (86, 3, parse("sbbq %rcx,%rax")),
  (89, 3, parse("setb %al")),
  (92, 3, parse("cmpq %rdx,%rsi")),
  (95, 4, parse("sbbq $0x0,%rcx")),
  (99, 2, parse("sbbb $0x0,%al")),
  (101, 1, parse("retq "))]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 36 := by
  have h0 : programChunk0.length = 36 := by rfl
  simp only [program, h0]

def labels : List (String × Nat) := [
  ("codec_nat_cmp_usize_u16", 16),
  ("codec_nat_cmp_usize_u46", 46),
  ("codec_nat_cmp_usize_u50", 50),
  ("codec_nat_cmp_usize_u55", 55),
  ("codec_nat_cmp_usize_u70", 70),
  ("codec_nat_cmp_usize_u77", 77)]

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

end SszX86.CodecNatCmpUsize

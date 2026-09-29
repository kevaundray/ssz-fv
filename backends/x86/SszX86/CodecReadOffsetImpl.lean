module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecReadOffset
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2216048
def machineSize : Nat := 113

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rax")),
  (1, 3, parse("testq %rsi,%rsi")),
  (4, 2, parse("je codec_read_offset_u59")),
  (6, 4, parse("cmpq $0x1,%rsi")),
  (10, 2, parse("je codec_read_offset_u68")),
  (12, 4, parse("cmpq $0x2,%rsi")),
  (16, 2, parse("jbe codec_read_offset_u83")),
  (18, 4, parse("cmpq $0x3,%rsi")),
  (22, 2, parse("je codec_read_offset_u98")),
  (24, 3, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rcx .W32)) (.mem (w := .W8) { base := some (.reg .rdi), idx := none, disp := .int64 (0) })))]),
  (27, 4, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .rdi), idx := none, disp := .int64 (1) })))]),
  (31, 4, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rdx .W32)) (.mem (w := .W8) { base := some (.reg .rdi), idx := none, disp := .int64 (2) })))]),
  (35, 4, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rsi .W32)) (.mem (w := .W8) { base := some (.reg .rdi), idx := none, disp := .int64 (3) })))]),
  (39, 3, parse("shll $0x18,%esi")),
  (42, 3, parse("shll $0x10,%edx")),
  (45, 3, parse("shll $0x8,%eax")),
  (48, 3, parse("orq %rcx,%rax")),
  (51, 3, parse("orq %rdx,%rax")),
  (54, 3, parse("orq %rsi,%rax")),
  (57, 1, parse("popq %rcx")),
  (58, 1, parse("retq ")),
  (59, 2, parse("xorl %edi,%edi")),
  (61, 2, parse("xorl %esi,%esi")),
  (63, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-84128)))))]),
  (68, 5, parse("movl $0x1,%edi")),
  (73, 5, parse("movl $0x1,%esi")),
  (78, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-84143)))))]),
  (83, 5, parse("movl $0x2,%edi")),
  (88, 5, parse("movl $0x2,%esi")),
  (93, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-84158)))))]),
  (98, 5, parse("movl $0x3,%edi")),
  (103, 5, parse("movl $0x3,%esi")),
  (108, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-84173)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 33 := by
  have h0 : programChunk0.length = 33 := by rfl
  simp only [program, h0]

def labels : List (String × Nat) := [
  ("codec_read_offset_u59", 59),
  ("codec_read_offset_u68", 68),
  ("codec_read_offset_u83", 83),
  ("codec_read_offset_u98", 98)]

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

def panicBoundsCheckOffset : Int := -84060

end SszX86.CodecReadOffset

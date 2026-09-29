module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecIsFixed
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2193664
def machineSize : Nat := 132

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 2, parse("pushq %r14")),
  (2, 1, parse("pushq %rbx")),
  (3, 1, parse("pushq %rax")),
  (4, 3, parse("movq (%rdi),%rax")),
  (7, 4, parse("cmpq $0x7,%rax")),
  (11, 2, parse("jne codec_is_fixed_u29")),
  (13, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (16, 4, parse("movq 0x18(%rdi),%rdi")),
  (20, 3, parse("movq (%rdi),%rax")),
  (23, 4, parse("cmpq $0x7,%rax")),
  (27, 2, parse("je codec_is_fixed_u16")),
  (29, 4, parse("cmpq $0xb,%rax")),
  (33, 2, parse("ja codec_is_fixed_u122")),
  (35, 7, [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-95606)}))]),
  (42, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))]),
  (46, 3, parse("addq %rcx,%rax")),
  (49, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))]),
  (51, 2, parse("movb $0x1,%al")),
  (53, 4, parse("addq $0x8,%rsp")),
  (57, 1, parse("popq %rbx")),
  (58, 2, parse("popq %r14")),
  (60, 1, parse("retq ")),
  (61, 5, parse("movl $0x18,%eax")),
  (66, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (5)))))]),
  (68, 5, parse("movl $0x8,%eax")),
  (73, 4, parse("movq (%rdi,%rax,1),%rbx")),
  (77, 5, parse("movq 0x8(%rdi,%rax,1),%rax")),
  (82, 4, parse("shlq $0x3,%rax")),
  (86, 4, parse("leaq (%rax,%rax,2),%r14")),
  (90, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (96, 3, parse("testq %r14,%r14")),
  (99, 2, parse("je codec_is_fixed_u51")),
  (101, 4, parse("movq 0x10(%rbx),%rdi")),
  (105, 4, parse("addq $0x18,%rbx")),
  (109, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-114)))))]),
  (114, 4, parse("addq $0xffffffffffffffe8,%r14")),
  (118, 2, parse("testb %al,%al")),
  (120, 2, parse("jne codec_is_fixed_u96")),
  (122, 2, parse("xorl %eax,%eax")),
  (124, 4, parse("addq $0x8,%rsp")),
  (128, 1, parse("popq %rbx")),
  (129, 2, parse("popq %r14")),
  (131, 1, parse("retq "))]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0

theorem program_length : program.length = 43 := by
  have h0 : programChunk0.length = 43 := by rfl
  simp only [program, h0]

def labels : List (String × Nat) := [
  ("codec_is_fixed_u16", 16),
  ("codec_is_fixed_u29", 29),
  ("codec_is_fixed_u51", 51),
  ("codec_is_fixed_u96", 96),
  ("codec_is_fixed_u122", 122)]

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

def tableOffset : Int := -95564
def tableAddress (base : Int64) : BitVec 64 :=
  (base + Int64.ofInt tableOffset).toBitVec

def tableBytes : List UInt8 :=
  [0x7f, 0x75, 0x01, 0x00, 0x7f, 0x75, 0x01, 0x00, 0x7f, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0x7f, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0xc6, 0x75, 0x01, 0x00, 0x90, 0x75, 0x01, 0x00, 0x89, 0x75, 0x01, 0x00]

def tableDestinations : List Nat := [51, 51, 51, 122, 51, 122, 122, 122, 122, 122, 68, 61]

def TableAt (m : DataMem) (base : Int64) : Prop :=
  ∀ i (hi : i < tableBytes.length),
    m.get? (tableAddress base + BitVec.ofNat 64 i) = some tableBytes[i]

def isFixedOffset : Int := 0

end SszX86.CodecIsFixed

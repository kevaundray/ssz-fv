module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatCompare
open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def entry : Nat := 0

def program : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rdi,%rdi")),
  (3, 2, parse("je natCompare_u39")),
  (5, 4, parse("leaq 0x1(%rsi),%rax")),
  (9, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (16, 4, parse("cmpq $0x1,%rax")),
  (20, 2, parse("je natCompare_u87")),
  (22, 4, parse("leaq -0x1(%rax),%r8")),
  (26, 6, parse("cmpq $0x0,-0x10(%rdi,%rax,8)")),
  (32, 3, parse("movq %r8,%rax")),
  (35, 2, parse("je natCompare_u16")),
  (37, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (10)))))]),
  (39, 3, parse("xorl %r8d,%r8d")),
  (42, 3, parse("testq %rsi,%rsi")),
  (45, 4, parse("setne %r8b")),
  (49, 3, parse("testq %rdx,%rdx")),
  (52, 2, parse("je natCompare_u95")),
  (54, 4, parse("leaq 0x1(%rcx),%rax")),
  (58, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (64, 4, parse("cmpq $0x1,%rax")),
  (68, 2, parse("je natCompare_u107")),
  (70, 4, parse("leaq -0x1(%rax),%r9")),
  (74, 6, parse("cmpq $0x0,-0x10(%rdx,%rax,8)")),
  (80, 3, parse("movq %r9,%rax")),
  (83, 2, parse("je natCompare_u64")),
  (85, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (23)))))]),
  (87, 3, parse("xorl %r8d,%r8d")),
  (90, 3, parse("testq %rdx,%rdx")),
  (93, 2, parse("jne natCompare_u54")),
  (95, 3, parse("xorl %r9d,%r9d")),
  (98, 3, parse("testq %rcx,%rcx")),
  (101, 4, parse("setne %r9b")),
  (105, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3)))))]),
  (107, 3, parse("xorl %r9d,%r9d")),
  (110, 3, parse("cmpq %r9,%r8")),
  (113, 3, parse("seta %al")),
  (116, 2, parse("sbbb $0x0,%al")),
  (118, 3, parse("cmpq %r9,%r8")),
  (121, 6, parse("jne natCompare_u372")),
  (127, 3, parse("testq %rdi,%rdi")),
  (130, 6, parse("je natCompare_u278")),
  (136, 3, parse("decq %r8")),
  (139, 3, parse("testq %rdx,%rdx")),
  (142, 2, parse("jne natCompare_u172")),
  (144, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (117)))))]),
  (160, 4, parse("movq (%rdx,%r8,8),%r9")),
  (164, 3, parse("decq %r8")),
  (167, 3, parse("cmpq %r9,%rax")),
  (170, 2, parse("jne natCompare_u226")),
  (172, 4, parse("cmpq $0xffffffffffffffff,%r8")),
  (176, 6, parse("je natCompare_u370")),
  (182, 3, parse("cmpq %rsi,%r8")),
  (185, 2, parse("jae natCompare_u208")),
  (187, 4, parse("movq (%rdi,%r8,8),%rax")),
  (191, 3, parse("cmpq %rcx,%r8")),
  (194, 2, parse("jb natCompare_u160")),
  (196, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (17)))))]),
  (208, 2, parse("xorl %eax,%eax")),
  (210, 3, parse("cmpq %rcx,%r8")),
  (213, 2, parse("jb natCompare_u160")),
  (215, 3, parse("xorl %r9d,%r9d")),
  (218, 3, parse("decq %r8")),
  (221, 3, parse("cmpq %r9,%rax")),
  (224, 2, parse("je natCompare_u172")),
  (226, 3, parse("cmpq %r9,%rax")),
  (229, 3, parse("seta %al")),
  (232, 2, parse("sbbb $0x0,%al")),
  (234, 1, parse("retq ")),
  (240, 4, parse("movq (%rdi,%r8,8),%rax")),
  (244, 4, parse("subq $0x1,%r8")),
  (248, 6, parse("movl $0x0,%r9d")),
  (254, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r9 .W64) (.reg (.low .rcx .W64))))]),
  (258, 3, parse("cmpq %r9,%rax")),
  (261, 2, parse("jne natCompare_u226")),
  (263, 4, parse("cmpq $0xffffffffffffffff,%r8")),
  (267, 2, parse("je natCompare_u370")),
  (269, 3, parse("cmpq %rsi,%r8")),
  (272, 2, parse("jb natCompare_u240")),
  (274, 2, parse("xorl %eax,%eax")),
  (276, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-34)))))]),
  (278, 3, parse("testq %rdx,%rdx")),
  (281, 2, parse("je natCompare_u364")),
  (283, 3, parse("decq %r8")),
  (286, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (8)))))]),
  (288, 3, parse("movq %rdi,%r8")),
  (291, 3, parse("cmpq %r9,%rax")),
  (294, 2, parse("jne natCompare_u226")),
  (296, 4, parse("cmpq $0xffffffffffffffff,%r8")),
  (300, 2, parse("je natCompare_u370")),
  (302, 3, parse("movq %r8,%rdi")),
  (305, 4, parse("subq $0x1,%rdi")),
  (309, 5, parse("movl $0x0,%eax")),
  (314, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rax .W64) (.reg (.low .rsi .W64))))]),
  (318, 6, parse("movl $0x0,%r9d")),
  (324, 3, parse("cmpq %rcx,%r8")),
  (327, 2, parse("jae natCompare_u288")),
  (329, 4, parse("movq (%rdx,%r8,8),%r9")),
  (333, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-47)))))]),
  (336, 5, parse("movl $0x0,%eax")),
  (341, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rax .W64) (.reg (.low .rsi .W64))))]),
  (345, 6, parse("movl $0x0,%r9d")),
  (351, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r9 .W64) (.reg (.low .rcx .W64))))]),
  (355, 3, parse("cmpq %r9,%rax")),
  (358, 6, parse("jne natCompare_u226")),
  (364, 4, parse("subq $0x1,%r8")),
  (368, 2, parse("jae natCompare_u336")),
  (370, 2, parse("xorl %eax,%eax")),
  (372, 1, parse("retq "))]

def labels : List (String × Nat) := [
  ("natCompare_u16", 16),
  ("natCompare_u39", 39),
  ("natCompare_u54", 54),
  ("natCompare_u64", 64),
  ("natCompare_u87", 87),
  ("natCompare_u95", 95),
  ("natCompare_u107", 107),
  ("natCompare_u160", 160),
  ("natCompare_u172", 172),
  ("natCompare_u208", 208),
  ("natCompare_u226", 226),
  ("natCompare_u240", 240),
  ("natCompare_u278", 278),
  ("natCompare_u288", 288),
  ("natCompare_u336", 336),
  ("natCompare_u364", 364),
  ("natCompare_u370", 370),
  ("natCompare_u372", 372)]

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

end SszX86.NatCompare

module

public import SszX86.NatCompareImpl

@[expose] public section

namespace SszX86.Delimited
open Kraken.X64.Parser

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def entry : Nat := 0
def compareOffset : Int := -59232

def program : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rcx,%rcx")),
  (3, 6, parse("je delimited_u153")),
  (9, 5, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := some ⟨.rcx, .W8⟩, disp := .int64 (-1) })))]),
  (14, 2, parse("testb %al,%al")),
  (16, 6, parse("je delimited_u233")),
  (22, 1, parse("pushq %rbp")),
  (23, 2, parse("pushq %r15")),
  (25, 2, parse("pushq %r14")),
  (27, 2, parse("pushq %r13")),
  (29, 2, parse("pushq %r12")),
  (31, 1, parse("pushq %rbx")),
  (32, 4, parse("subq $0x28,%rsp")),
  (36, 4, parse("leaq -0x1(%rcx),%r13")),
  (40, 3, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.reg (.low .rax .W8))))]),
  (43, 5, parse("leaq -0x10(%rsp),%rsp")),
  (48, 4, parse("movq %r11,(%rsp)")),
  (52, 5, parse("movq %r10,0x8(%rsp)")),
  (57, 3, parse("movl %eax,%r11d")),
  (60, 3, parse("testl %r11d,%r11d")),
  (63, 2, parse("je delimited_u89")),
  (65, 7, parse("movq $0xffffffffffffffff,%r10")),
  (72, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (75, 3, parse("shrl $1,%r11d")),
  (78, 2, parse("jne delimited_u72")),
  (80, 3, parse("movl %r10d,%ebx")),
  (83, 4, parse("cmpq $0xffffffffffffffff,%r10")),
  (87, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))]),
  (89, 4, parse("movq (%rsp),%r11")),
  (93, 5, parse("movq 0x8(%rsp),%r10")),
  (98, 5, parse("leaq 0x10(%rsp),%rsp")),
  (103, 3, parse("movq %r13,%rbp")),
  (106, 4, parse("shrq $0x3d,%rbp")),
  (110, 4, parse("leaq (%rbx,%r13,8),%r14")),
  (114, 10, parse("movabsq $0x2000000000000001,%rax")),
  (124, 3, parse("cmpq %rax,%rcx")),
  (127, 6, parse("jae delimited_u269")),
  (133, 3, parse("xorl %r8d,%r8d")),
  (136, 3, parse("movq %r14,%r15")),
  (139, 3, parse("cmpl $0x1,(%rsi)")),
  (142, 6, parse("je delimited_u374")),
  (148, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (370)))))]),
  (153, 8, parse("movq $0x1,0x8(%rdi)")),
  (161, 8, parse("movq $0x0,0x10(%rdi)")),
  (169, 8, parse("movq $0x0,0x18(%rdi)")),
  (177, 8, parse("movq $0x0,0x20(%rdi)")),
  (185, 8, parse("movq $0x0,0x28(%rdi)")),
  (193, 8, parse("movq $0x0,0x30(%rdi)")),
  (201, 8, parse("movq $0x0,0x38(%rdi)")),
  (209, 8, parse("movq $0x0,0x40(%rdi)")),
  (217, 7, parse("movl $0x10,0x48(%rdi)")),
  (224, 5, parse("movl $0x1,%eax")),
  (229, 3, parse("movq %rax,(%rdi)")),
  (232, 1, parse("retq ")),
  (233, 2, parse("xorl %eax,%eax")),
  (235, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (240, 3, parse("cmpq %rax,%rcx")),
  (243, 6, parse("je delimited_u582")),
  (249, 4, parse("cmpb $0x0,(%rdx,%rax,1)")),
  (253, 4, parse("leaq 0x1(%rax),%rax")),
  (257, 2, parse("je delimited_u240")),
  (259, 5, parse("movl $0x12,%eax")),
  (264, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (318)))))]),
  (269, 3, parse("movq (%r8),%rax")),
  (272, 4, parse("movq 0x10(%r8),%r10")),
  (276, 3, parse("movq %r10,%r11")),
  (279, 3, parse("addq %rax,%r11")),
  (282, 6, parse("jb delimited_u736")),
  (288, 4, parse("cmpq $0xfffffffffffffff8,%r11")),
  (292, 6, parse("ja delimited_u736")),
  (298, 4, parse("leaq 0x7(%r11),%r9")),
  (302, 4, parse("andq $0xfffffffffffffff8,%r9")),
  (306, 3, parse("subq %r11,%r9")),
  (309, 3, parse("addq %r10,%r9")),
  (312, 6, parse("jb delimited_u736")),
  (318, 4, parse("cmpq $0xffffffffffffffef,%r9")),
  (322, 6, parse("ja delimited_u736")),
  (328, 4, parse("leaq 0x10(%r9),%r10")),
  (332, 4, parse("cmpq 0x8(%r8),%r10")),
  (336, 6, parse("ja delimited_u736")),
  (342, 4, parse("movq %r10,0x10(%r8)")),
  (346, 4, parse("leaq (%rax,%r9,1),%r8")),
  (350, 4, parse("movq %r14,(%rax,%r9,1)")),
  (354, 5, parse("movq %rbp,0x8(%rax,%r9,1)")),
  (359, 6, parse("movl $0x2,%r15d")),
  (365, 3, parse("cmpl $0x1,(%rsi)")),
  (368, 6, parse("jne delimited_u523")),
  (374, 4, parse("movq 0x8(%rsi),%r9")),
  (378, 4, parse("movq 0x10(%rsi),%r10")),
  (382, 5, parse("movq %r14,0x20(%rsp)")),
  (387, 5, parse("movq %rdi,0x18(%rsp)")),
  (392, 3, parse("movq %r8,%rdi")),
  (395, 3, parse("movq %r15,%rsi")),
  (398, 5, parse("movq %rdx,0x10(%rsp)")),
  (403, 5, parse("movq %r9,0x8(%rsp)")),
  (408, 3, parse("movq %r9,%rdx")),
  (411, 3, parse("movq %rcx,%r12")),
  (414, 4, parse("movq %r10,(%rsp)")),
  (418, 3, parse("movq %r10,%rcx")),
  (421, 3, parse("movq %r8,%r14")),
  (424, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-59661)))))]),
  (429, 3, parse("movq %r14,%rsi")),
  (432, 5, parse("movq 0x10(%rsp),%rdx")),
  (437, 3, parse("movq %r12,%rcx")),
  (440, 5, parse("movq 0x18(%rsp),%rdi")),
  (445, 5, parse("movq 0x20(%rsp),%r14")),
  (450, 2, parse("testb %al,%al")),
  (452, 2, parse("jle delimited_u523")),
  (454, 8, parse("movq $0x0,0x40(%rdi)")),
  (462, 8, parse("movq $0x0,0x38(%rdi)")),
  (470, 8, parse("movq $0x1,0x8(%rdi)")),
  (478, 8, parse("movq $0x0,0x10(%rdi)")),
  (486, 5, parse("movq 0x8(%rsp),%rax")),
  (491, 4, parse("movq %rax,0x18(%rdi)")),
  (495, 4, parse("movq (%rsp),%rax")),
  (499, 4, parse("movq %rax,0x20(%rdi)")),
  (503, 5, parse("movl $0x2,%eax")),
  (508, 5, parse("movl $0x30,%ecx")),
  (513, 5, parse("movl $0x28,%edx")),
  (518, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (284)))))]),
  (523, 3, parse("xorl $0x7,%ebx")),
  (526, 2, parse("xorl %eax,%eax")),
  (528, 3, parse("cmpb $0x7,%bl")),
  (531, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rcx .W64) (.reg (.low .r13 .W64))))]),
  (535, 3, parse("setne %al")),
  (538, 2, parse("xorl %esi,%esi")),
  (540, 3, parse("addq %r13,%rax")),
  (543, 4, parse("setb %sil")),
  (547, 3, parse("xorq %rcx,%rax")),
  (550, 3, parse("orq %rsi,%rax")),
  (553, 2, parse("jne delimited_u663")),
  (555, 4, parse("movb $0x3,0x10(%rdi)")),
  (559, 4, parse("movq %rdx,0x20(%rdi)")),
  (563, 4, parse("movq %rcx,0x28(%rdi)")),
  (567, 4, parse("movq %r14,0x30(%rdi)")),
  (571, 4, parse("movq %rbp,0x38(%rdi)")),
  (575, 2, parse("xorl %eax,%eax")),
  (577, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (241)))))]),
  (582, 5, parse("movl $0x11,%eax")),
  (587, 8, parse("movq $0x1,0x8(%rdi)")),
  (595, 8, parse("movq $0x0,0x10(%rdi)")),
  (603, 8, parse("movq $0x0,0x18(%rdi)")),
  (611, 8, parse("movq $0x0,0x20(%rdi)")),
  (619, 8, parse("movq $0x0,0x28(%rdi)")),
  (627, 8, parse("movq $0x0,0x30(%rdi)")),
  (635, 8, parse("movq $0x0,0x38(%rdi)")),
  (643, 8, parse("movq $0x0,0x40(%rdi)")),
  (651, 3, parse("movl %eax,0x48(%rdi)")),
  (654, 5, parse("movl $0x1,%eax")),
  (659, 3, parse("movq %rax,(%rdi)")),
  (662, 1, parse("retq ")),
  (663, 8, parse("movq $0x1,0x8(%rdi)")),
  (671, 8, parse("movq $0x0,0x10(%rdi)")),
  (679, 8, parse("movq $0x0,0x18(%rdi)")),
  (687, 8, parse("movq $0x0,0x20(%rdi)")),
  (695, 8, parse("movq $0x0,0x28(%rdi)")),
  (703, 8, parse("movq $0x0,0x30(%rdi)")),
  (711, 8, parse("movq $0x0,0x38(%rdi)")),
  (719, 8, parse("movq $0x0,0x40(%rdi)")),
  (727, 7, parse("movl $0x8002,0x48(%rdi)")),
  (734, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (82)))))]),
  (736, 8, parse("movq $0x0,0x40(%rdi)")),
  (744, 8, parse("movq $0x0,0x38(%rdi)")),
  (752, 8, parse("movq $0x0,0x30(%rdi)")),
  (760, 8, parse("movq $0x0,0x28(%rdi)")),
  (768, 8, parse("movq $0x0,0x20(%rdi)")),
  (776, 8, parse("movq $0x0,0x18(%rdi)")),
  (784, 5, parse("movl $0x8000,%eax")),
  (789, 5, parse("movl $0x10,%ecx")),
  (794, 5, parse("movl $0x1,%esi")),
  (799, 5, parse("movl $0x8,%edx")),
  (804, 3, parse("xorl %r15d,%r15d")),
  (807, 4, parse("movq %rsi,(%rdi,%rdx,1)")),
  (811, 4, parse("movq %r15,(%rdi,%rcx,1)")),
  (815, 3, parse("movl %eax,0x48(%rdi)")),
  (818, 5, parse("movl $0x1,%eax")),
  (823, 4, parse("addq $0x28,%rsp")),
  (827, 1, parse("popq %rbx")),
  (828, 2, parse("popq %r12")),
  (830, 2, parse("popq %r13")),
  (832, 2, parse("popq %r14")),
  (834, 2, parse("popq %r15")),
  (836, 1, parse("popq %rbp")),
  (837, 3, parse("movq %rax,(%rdi)")),
  (840, 1, parse("retq "))]

def labels : List (String × Nat) := [
  ("delimited_u72", 72),
  ("delimited_u89", 89),
  ("delimited_u153", 153),
  ("delimited_u233", 233),
  ("delimited_u240", 240),
  ("delimited_u269", 269),
  ("delimited_u374", 374),
  ("delimited_u523", 523),
  ("delimited_u582", 582),
  ("delimited_u663", 663),
  ("delimited_u736", 736)]

/-- Every linked row is an actual executable instruction. -/
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

end SszX86.Delimited

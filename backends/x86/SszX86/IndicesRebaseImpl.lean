module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesRebase
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2166128
def machineSize : Nat := 911

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 4, parse("subq $0x20,%rsp")),
  (14, 3, parse("movq %rcx,%rax")),
  (17, 3, parse("andq %r8,%rax")),
  (20, 4, parse("cmpq $0xffffffffffffffff,%rax")),
  (24, 2, parse("je indices_rebase_u77")),
  (26, 3, parse("movq %rcx,%r10")),
  (29, 3, parse("movq %rdx,%r15")),
  (32, 3, parse("movq %rcx,%rax")),
  (35, 4, parse("addq $0x1,%rax")),
  (39, 3, parse("movq %r8,%r11")),
  (42, 4, parse("adcq $0x0,%r11")),
  (46, 3, parse("movq %r11,%rcx")),
  (49, 4, parse("shrq $0x6,%rcx")),
  (53, 3, parse("movq %r11,%rdx")),
  (56, 5, parse("shldq $0x3a,%rax,%rdx")),
  (61, 2, parse("xorl %ebx,%ebx")),
  (63, 2, parse("testb $0x3f,%al")),
  (65, 3, parse("setne %bl")),
  (68, 3, parse("addq %rdx,%rbx")),
  (71, 4, parse("adcq $0x0,%rcx")),
  (75, 2, parse("je indices_rebase_u152")),
  (77, 7, parse("movq $0x1,(%rdi)")),
  (84, 8, parse("movq $0x0,0x8(%rdi)")),
  (92, 8, parse("movq $0x0,0x10(%rdi)")),
  (100, 8, parse("movq $0x0,0x18(%rdi)")),
  (108, 8, parse("movq $0x0,0x20(%rdi)")),
  (116, 8, parse("movq $0x0,0x28(%rdi)")),
  (124, 8, parse("movq $0x0,0x30(%rdi)")),
  (132, 8, parse("movq $0x0,0x38(%rdi)")),
  (140, 7, parse("movl $0x8000,0x40(%rdi)")),
  (147, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (367)))))]),
  (152, 3, parse("testq %rbx,%rbx")),
  (155, 2, parse("je indices_rebase_u189")),
  (157, 4, parse("cmpq $0x1,%rbx")),
  (161, 2, parse("jne indices_rebase_u209")),
  (163, 3, parse("testq %rsi,%rsi")),
  (166, 6, parse("je indices_rebase_u397")),
  (172, 3, parse("testq %r15,%r15")),
  (175, 6, parse("je indices_rebase_u394")),
  (181, 3, parse("movq (%rsi),%r15")),
  (184, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (208)))))]),
  (189, 8, parse("movq $0x0,0x8(%rdi)")),
  (197, 7, parse("movq $0x0,(%rdi)")),
  (204, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (303)))))]),
  (209, 8, [.instr (.regular .W64 .W64 (.lea (.low .rcx .W64) { base := none, idx := some ⟨.rbx, .W64⟩, disp := .int64 (0) }))]),
  (217, 3, parse("movq %rbx,%rdx")),
  (220, 4, parse("shrq $0x3d,%rdx")),
  (224, 3, parse("setne %dl")),
  (227, 3, parse("testq %rcx,%rcx")),
  (230, 4, parse("setl %bpl")),
  (234, 3, parse("orb %dl,%bpl")),
  (237, 2, parse("je indices_rebase_u307")),
  (239, 8, parse("movq $0x0,0x38(%rdi)")),
  (247, 8, parse("movq $0x0,0x30(%rdi)")),
  (255, 8, parse("movq $0x0,0x28(%rdi)")),
  (263, 8, parse("movq $0x0,0x20(%rdi)")),
  (271, 8, parse("movq $0x0,0x18(%rdi)")),
  (279, 8, parse("movq $0x0,0x10(%rdi)"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (287, 7, parse("movq $0x1,(%rdi)")),
  (294, 8, parse("movq $0x0,0x8(%rdi)")),
  (302, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-167)))))]),
  (307, 3, parse("movq (%r9),%rdx")),
  (310, 4, parse("movq 0x10(%r9),%r12")),
  (314, 3, parse("movq %r12,%r14")),
  (317, 3, parse("addq %rdx,%r14")),
  (320, 2, parse("jb indices_rebase_u239")),
  (322, 4, parse("cmpq $0xfffffffffffffff8,%r14")),
  (326, 2, parse("ja indices_rebase_u239")),
  (328, 3, parse("movq %rdx,%rbp")),
  (331, 4, parse("leaq 0x7(%r14),%rdx")),
  (335, 4, parse("andq $0xfffffffffffffff8,%rdx")),
  (339, 3, parse("subq %r14,%rdx")),
  (342, 3, parse("addq %r12,%rdx")),
  (345, 2, parse("jb indices_rebase_u239")),
  (347, 3, parse("addq %rdx,%rcx")),
  (350, 2, parse("jb indices_rebase_u239")),
  (352, 4, parse("cmpq 0x8(%r9),%rcx")),
  (356, 2, parse("ja indices_rebase_u239")),
  (358, 4, parse("movq %rcx,0x10(%r9)")),
  (362, 3, parse("addq %rdx,%rbp")),
  (365, 3, parse("movq %r15,%r13")),
  (368, 3, parse("testq %rsi,%rsi")),
  (371, 6, parse("je indices_rebase_u537")),
  (377, 3, parse("testq %r15,%r15")),
  (380, 6, parse("je indices_rebase_u534")),
  (386, 3, parse("movq (%rsi),%r13")),
  (389, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (143)))))]),
  (394, 3, parse("xorl %r15d,%r15d")),
  (397, 4, parse("cmpq $0x40,%r10")),
  (401, 5, parse("movl $0x40,%esi")),
  (406, 4, parse("cmovae %rsi,%r10")),
  (410, 3, parse("testq %r8,%r8")),
  (413, 4, parse("cmovne %rsi,%r10")),
  (417, 7, parse("movq $0xffffffffffffffff,%rdx")),
  (424, 7, parse("movq $0xffffffffffffffff,%r9")),
  (431, 3, parse("movl %r10d,%ecx")),
  (434, 3, parse("shlq %cl,%r9")),
  (437, 3, parse("xorl %r8d,%r8d")),
  (440, 4, parse("cmpl $0x40,%r10d")),
  (444, 4, parse("cmovne %r9,%r8")),
  (448, 3, parse("notq %r9")),
  (451, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r9 .W64) (.reg (.low .rdx .W64))))]),
  (455, 3, parse("andq %r15,%r9")),
  (458, 4, parse("cmpq $0x40,%rax")),
  (462, 4, parse("cmovae %rsi,%rax")),
  (466, 3, parse("testq %r11,%r11")),
  (469, 4, parse("cmovne %rsi,%rax")),
  (473, 7, parse("movq $0xffffffffffffffff,%rsi")),
  (480, 2, parse("movl %eax,%ecx")),
  (482, 3, parse("shlq %cl,%rsi")),
  (485, 3, parse("cmpl $0x40,%eax")),
  (488, 3, parse("notq %rsi")),
  (491, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rsi .W64) (.reg (.low .rdx .W64))))]),
  (495, 3, parse("andq %r8,%rsi")),
  (498, 3, parse("orq %r9,%rsi")),
  (501, 7, parse("movq $0x0,(%rdi)")),
  (508, 4, parse("movq %rsi,0x8(%rdi)")),
  (512, 7, parse("movl $0x0,0x40(%rdi)")),
  (519, 4, parse("addq $0x20,%rsp")),
  (523, 1, parse("popq %rbx")),
  (524, 2, parse("popq %r12")),
  (526, 2, parse("popq %r13"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (528, 2, parse("popq %r14")),
  (530, 2, parse("popq %r15")),
  (532, 1, parse("popq %rbp")),
  (533, 1, parse("retq ")),
  (534, 3, parse("xorl %r13d,%r13d")),
  (537, 4, parse("cmpq $0x40,%r10")),
  (541, 6, parse("movl $0x40,%r14d")),
  (547, 5, parse("movl $0x40,%ecx")),
  (552, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rcx .W64) (.reg (.low .r10 .W64))))]),
  (556, 5, parse("movq %r8,0x8(%rsp)")),
  (561, 3, parse("testq %r8,%r8")),
  (564, 4, parse("cmovne %r14,%rcx")),
  (568, 7, parse("movq $0xffffffffffffffff,%rdx")),
  (575, 3, parse("shlq %cl,%rdx")),
  (578, 7, parse("movq $0xffffffffffffffff,%r8")),
  (585, 3, parse("xorl %r12d,%r12d")),
  (588, 3, parse("cmpl $0x40,%ecx")),
  (591, 6, parse("movl $0x0,%r9d")),
  (597, 4, parse("cmovne %rdx,%r9")),
  (601, 3, parse("notq %rdx")),
  (604, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rdx .W64) (.reg (.low .r8 .W64))))]),
  (608, 3, parse("andq %r13,%rdx")),
  (611, 4, parse("cmpq $0x40,%rax")),
  (615, 5, parse("movl $0x40,%ecx")),
  (620, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rcx .W64) (.reg (.low .rax .W64))))]),
  (624, 3, parse("testq %r11,%r11")),
  (627, 4, parse("cmovne %r14,%rcx")),
  (631, 7, parse("movq $0xffffffffffffffff,%r14")),
  (638, 3, parse("shlq %cl,%r14")),
  (641, 3, parse("cmpl $0x40,%ecx")),
  (644, 3, parse("notq %r14")),
  (647, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r14 .W64) (.reg (.low .r8 .W64))))]),
  (651, 3, parse("andq %r9,%r14")),
  (654, 3, parse("orq %rdx,%r14")),
  (657, 4, parse("movq %rbp,(%rsp)")),
  (661, 4, parse("movq %r14,0x0(%rbp)")),
  (665, 6, parse("movl $0x1,%r13d")),
  (671, 5, parse("movq %r15,0x18(%rsp)")),
  (676, 5, parse("movq %rsi,0x10(%rsp)")),
  (681, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (179)))))]),
  (686, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (688, 4, parse("movq (%rsi,%r13,8),%rbp")),
  (692, 3, parse("movq %r13,%r15")),
  (695, 4, parse("shrq $0x3a,%r15")),
  (699, 3, parse("movq %r13,%r9")),
  (702, 4, parse("shlq $0x6,%r9")),
  (706, 3, parse("movq %r10,%rcx")),
  (709, 3, parse("subq %r9,%rcx")),
  (712, 5, parse("movq 0x8(%rsp),%rdx")),
  (717, 3, parse("sbbq %r15,%rdx")),
  (720, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rdx .W64) (.reg (.low .r12 .W64))))]),
  (724, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rcx .W64) (.reg (.low .r12 .W64))))]),
  (728, 4, parse("cmpq $0x40,%rcx")),
  (732, 5, parse("movl $0x40,%esi")),
  (737, 4, parse("cmovae %rsi,%rcx")),
  (741, 3, parse("testq %rdx,%rdx")),
  (744, 4, parse("cmovne %rsi,%rcx")),
  (748, 7, parse("movq $0xffffffffffffffff,%rdx")),
  (755, 3, parse("shlq %cl,%rdx")),
  (758, 3, parse("cmpl $0x40,%ecx")),
  (761, 3, parse("movq %rdx,%r14")),
  (764, 3, parse("notq %r14")),
  (767, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r14 .W64) (.reg (.low .r8 .W64))))]),
  (771, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rdx .W64) (.reg (.low .r12 .W64))))])]

def programChunk3 : List (Nat × Nat × Program) := [
  (775, 3, parse("andq %rbp,%r14")),
  (778, 3, parse("movq %rax,%rcx")),
  (781, 3, parse("subq %r9,%rcx")),
  (784, 3, parse("movq %r11,%r9")),
  (787, 3, parse("sbbq %r15,%r9")),
  (790, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r9 .W64) (.reg (.low .r12 .W64))))]),
  (794, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rcx .W64) (.reg (.low .r12 .W64))))]),
  (798, 4, parse("cmpq $0x40,%rcx")),
  (802, 4, parse("cmovae %rsi,%rcx")),
  (806, 3, parse("testq %r9,%r9")),
  (809, 4, parse("cmovne %rsi,%rcx")),
  (813, 7, parse("movq $0xffffffffffffffff,%r9")),
  (820, 3, parse("shlq %cl,%r9")),
  (823, 3, parse("cmpl $0x40,%ecx")),
  (826, 3, parse("notq %r9")),
  (829, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r9 .W64) (.reg (.low .r8 .W64))))]),
  (833, 3, parse("andq %rdx,%r9")),
  (836, 3, parse("orq %r14,%r9")),
  (839, 4, parse("movq (%rsp),%rcx")),
  (843, 4, parse("movq %r9,(%rcx,%r13,8)")),
  (847, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r13 .W64))))]),
  (850, 3, parse("cmpq %r13,%rbx")),
  (853, 5, parse("movq 0x18(%rsp),%r15")),
  (858, 5, parse("movq 0x10(%rsp),%rsi")),
  (863, 2, parse("je indices_rebase_u895")),
  (865, 3, parse("testq %rsi,%rsi")),
  (868, 3, parse("setne %cl")),
  (871, 3, parse("cmpq %r15,%r13")),
  (874, 3, parse("setb %dl")),
  (877, 2, parse("andb %cl,%dl")),
  (879, 3, parse("cmpb $0x1,%dl")),
  (882, 6, parse("je indices_rebase_u688")),
  (888, 2, parse("xorl %ebp,%ebp")),
  (890, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-203)))))]),
  (895, 4, parse("movq (%rsp),%rax")),
  (899, 3, parse("movq %rax,(%rdi)")),
  (902, 4, parse("movq %rbx,0x8(%rdi)")),
  (906, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-399)))))])]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1 ++
  programChunk2 ++
  programChunk3

theorem program_length : program.length = 230 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 64 := by rfl
  have h3 : programChunk3.length = 38 := by rfl
  simp only [program, List.length_append, h0, h1, h2, h3]

def labels : List (String × Nat) := [
  ("indices_rebase_u77", 77),
  ("indices_rebase_u152", 152),
  ("indices_rebase_u189", 189),
  ("indices_rebase_u209", 209),
  ("indices_rebase_u239", 239),
  ("indices_rebase_u307", 307),
  ("indices_rebase_u394", 394),
  ("indices_rebase_u397", 397),
  ("indices_rebase_u534", 534),
  ("indices_rebase_u537", 537),
  ("indices_rebase_u688", 688),
  ("indices_rebase_u895", 895)]


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

end SszX86.IndicesRebase

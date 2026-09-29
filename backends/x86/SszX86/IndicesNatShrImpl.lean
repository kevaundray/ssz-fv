module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesNatShr
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2168736
def machineSize : Nat := 877

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 3, parse("testq %rsi,%rsi")),
  (3, 2, parse("je indices_nat_shr_u60")),
  (5, 4, parse("leaq 0x1(%rdx),%rax")),
  (9, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (16, 4, parse("cmpq $0x1,%rax")),
  (20, 6, parse("je indices_nat_shr_u236")),
  (26, 5, parse("movq -0x10(%rsi,%rax,8),%r11")),
  (31, 3, parse("decq %rax")),
  (34, 3, parse("testq %r11,%r11")),
  (37, 2, parse("je indices_nat_shr_u16")),
  (39, 3, parse("movq %rax,%r10")),
  (42, 4, parse("shrq $0x3a,%r10")),
  (46, 4, parse("shlq $0x6,%rax")),
  (50, 4, parse("addq $0xffffffffffffffc0,%rax")),
  (54, 4, parse("adcq $0xffffffffffffffff,%r10")),
  (58, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (20)))))]),
  (60, 2, parse("xorl %eax,%eax")),
  (62, 3, parse("movq %rdx,%r11")),
  (65, 6, parse("movl $0x0,%r10d")),
  (71, 3, parse("testq %rdx,%rdx")),
  (74, 6, parse("je indices_nat_shr_u236")),
  (80, 5, parse("leaq -0x10(%rsp),%rsp")),
  (85, 4, parse("movq %r10,(%rsp)")),
  (89, 5, parse("movq %r9,0x8(%rsp)")),
  (94, 3, parse("movq %r11,%r10")),
  (97, 3, parse("testq %r10,%r10")),
  (100, 2, parse("je indices_nat_shr_u126")),
  (102, 7, parse("movq $0xffffffffffffffff,%r9")),
  (109, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r9 .W64))))]),
  (112, 3, parse("shrq $1,%r10")),
  (115, 2, parse("jne indices_nat_shr_u109")),
  (117, 3, parse("movq %r9,%r11")),
  (120, 4, parse("cmpq $0xffffffffffffffff,%r9")),
  (124, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))]),
  (126, 4, parse("movq (%rsp),%r10")),
  (130, 5, parse("movq 0x8(%rsp),%r9")),
  (135, 5, parse("leaq 0x10(%rsp),%rsp")),
  (140, 3, [.instr (.regular .W64 .W32 (.inc (.reg (.low .r11 .W32))))]),
  (143, 3, parse("addq %rax,%r11")),
  (146, 4, parse("adcq $0x0,%r10")),
  (150, 3, parse("cmpq %r11,%rcx")),
  (153, 3, parse("movq %r8,%rax")),
  (156, 3, parse("sbbq %r10,%rax")),
  (159, 2, parse("jae indices_nat_shr_u236")),
  (161, 3, parse("movq %rcx,%rax")),
  (164, 3, parse("orq %r8,%rax")),
  (167, 2, parse("je indices_nat_shr_u257")),
  (169, 3, parse("subq %rcx,%r11")),
  (172, 3, parse("sbbq %r8,%r10")),
  (175, 4, parse("cmpq $0x41,%r11")),
  (179, 3, parse("movq %r10,%rax")),
  (182, 4, parse("sbbq $0x0,%rax")),
  (186, 6, parse("jae indices_nat_shr_u319")),
  (192, 3, parse("testq %rsi,%rsi")),
  (195, 6, parse("je indices_nat_shr_u488")),
  (201, 3, parse("testq %rdx,%rdx")),
  (204, 6, parse("je indices_nat_shr_u659")),
  (210, 3, parse("movq (%rsi),%rax")),
  (213, 3, parse("movq %rcx,%r8")),
  (216, 3, parse("shrq %cl,%rax")),
  (219, 4, parse("cmpq $0x1,%rdx")),
  (223, 6, parse("jne indices_nat_shr_u665")),
  (229, 2, parse("xorl %esi,%esi")),
  (231, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (433)))))])]

def programChunk1 : List (Nat × Nat × Program) := [
  (236, 8, parse("movq $0x0,0x8(%rdi)")),
  (244, 7, parse("movq $0x0,(%rdi)")),
  (251, 2, parse("xorl %eax,%eax")),
  (253, 3, parse("movl %eax,0x40(%rdi)")),
  (256, 1, parse("retq ")),
  (257, 2, parse("xorl %eax,%eax")),
  (259, 3, parse("testq %rsi,%rsi")),
  (262, 2, parse("je indices_nat_shr_u306")),
  (264, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rdx .W64))))]),
  (267, 3, parse("movq %rdx,%rcx")),
  (270, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (272, 4, parse("cmpq $0x1,%rcx")),
  (276, 6, parse("je indices_nat_shr_u473")),
  (282, 4, parse("leaq -0x1(%rcx),%rdx")),
  (286, 6, parse("cmpq $0x0,-0x10(%rsi,%rcx,8)")),
  (292, 3, parse("movq %rdx,%rcx")),
  (295, 2, parse("je indices_nat_shr_u272")),
  (297, 4, parse("cmpq $0x1,%rdx")),
  (301, 2, parse("jne indices_nat_shr_u308")),
  (303, 3, parse("movq (%rsi),%rdx")),
  (306, 2, parse("xorl %esi,%esi")),
  (308, 3, parse("movq %rsi,(%rdi)")),
  (311, 4, parse("movq %rdx,0x8(%rdi)")),
  (315, 3, parse("movl %eax,0x40(%rdi)")),
  (318, 1, parse("retq ")),
  (319, 2, parse("pushq %r15")),
  (321, 2, parse("pushq %r14")),
  (323, 2, parse("pushq %r12")),
  (325, 1, parse("pushq %rbx")),
  (326, 4, parse("addq $0xffffffffffffffff,%r11")),
  (330, 4, parse("adcq $0xffffffffffffffff,%r10")),
  (334, 5, parse("shldq $0x3a,%r11,%r10")),
  (339, 3, parse("movq %r10,%r8")),
  (342, 6, parse("movl $0x8,%r11d")),
  (348, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r8 .W64))))]),
  (351, 2, parse("jne indices_nat_shr_u364")),
  (353, 3, parse("movq %r11,(%rdi)")),
  (356, 4, parse("movq %r8,0x8(%rdi)")),
  (360, 2, parse("xorl %eax,%eax")),
  (362, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (98)))))]),
  (364, 8, [.instr (.regular .W64 .W64 (.lea (.low .rbx .W64) { base := none, idx := some ⟨.r8, .W64⟩, disp := .int64 (0) }))]),
  (372, 3, parse("movq %r8,%rax")),
  (375, 4, parse("shrq $0x3d,%rax")),
  (379, 3, parse("setne %al")),
  (382, 3, parse("testq %rbx,%rbx")),
  (385, 4, parse("setl %r11b")),
  (389, 3, parse("orb %al,%r11b")),
  (392, 2, parse("je indices_nat_shr_u501")),
  (394, 8, parse("movq $0x0,0x38(%rdi)")),
  (402, 8, parse("movq $0x0,0x30(%rdi)")),
  (410, 8, parse("movq $0x0,0x28(%rdi)")),
  (418, 8, parse("movq $0x0,0x20(%rdi)")),
  (426, 8, parse("movq $0x0,0x18(%rdi)")),
  (434, 8, parse("movq $0x0,0x10(%rdi)")),
  (442, 7, parse("movq $0x1,(%rdi)")),
  (449, 8, parse("movq $0x0,0x8(%rdi)")),
  (457, 5, parse("movl $0x8000,%eax")),
  (462, 1, parse("popq %rbx")),
  (463, 2, parse("popq %r12")),
  (465, 2, parse("popq %r14")),
  (467, 2, parse("popq %r15")),
  (469, 3, parse("movl %eax,0x40(%rdi)")),
  (472, 1, parse("retq ")),
  (473, 2, parse("xorl %esi,%esi"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (475, 2, parse("xorl %edx,%edx")),
  (477, 3, parse("movq %rsi,(%rdi)")),
  (480, 4, parse("movq %rdx,0x8(%rdi)")),
  (484, 3, parse("movl %eax,0x40(%rdi)")),
  (487, 1, parse("retq ")),
  (488, 3, parse("shrq %cl,%rdx")),
  (491, 2, parse("xorl %esi,%esi")),
  (493, 3, parse("movq %rdx,%rax")),
  (496, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (171)))))]),
  (501, 3, parse("movq (%r9),%r11")),
  (504, 4, parse("movq 0x10(%r9),%r15")),
  (508, 3, parse("movq %r15,%r12")),
  (511, 3, parse("addq %r11,%r12")),
  (514, 2, parse("jb indices_nat_shr_u394")),
  (516, 4, parse("cmpq $0xfffffffffffffff8,%r12")),
  (520, 2, parse("ja indices_nat_shr_u394")),
  (522, 5, parse("leaq 0x7(%r12),%rax")),
  (527, 4, parse("andq $0xfffffffffffffff8,%rax")),
  (531, 3, parse("movq %rax,%r14")),
  (534, 3, parse("subq %r12,%r14")),
  (537, 3, parse("addq %r15,%r14")),
  (540, 6, parse("jb indices_nat_shr_u394")),
  (546, 3, parse("addq %r14,%rbx")),
  (549, 6, parse("jb indices_nat_shr_u394")),
  (555, 4, parse("cmpq 0x8(%r9),%rbx")),
  (559, 6, parse("ja indices_nat_shr_u394")),
  (565, 3, parse("addq %r14,%r11")),
  (568, 4, parse("movq %rbx,0x10(%r9)")),
  (572, 3, parse("testq %rsi,%rsi")),
  (575, 2, parse("je indices_nat_shr_u697")),
  (577, 2, parse("movl %ecx,%eax")),
  (579, 2, parse("negl %eax")),
  (581, 3, parse("andl $0x3f,%eax")),
  (584, 3, parse("xorl %r9d,%r9d")),
  (587, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (36)))))]),
  (589, 5, parse("movq 0x8(%rsi,%r9,8),%r12")),
  (594, 2, parse("movl %eax,%ecx")),
  (596, 3, parse("shlq %cl,%r12")),
  (599, 3, parse("orq %r14,%r12")),
  (602, 4, parse("movq %r12,(%r11,%r9,8)")),
  (606, 4, parse("leaq -0x1(%r15),%rcx")),
  (610, 3, parse("movq %r15,%r9")),
  (613, 3, parse("cmpq %r10,%rcx")),
  (616, 3, parse("movq %rbx,%rcx")),
  (619, 6, parse("je indices_nat_shr_u353")),
  (625, 3, parse("cmpq %rdx,%r9")),
  (628, 2, parse("jae indices_nat_shr_u636")),
  (630, 4, parse("movq (%rsi,%r9,8),%r14")),
  (634, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3)))))]),
  (636, 3, parse("xorl %r14d,%r14d")),
  (639, 3, parse("movq %rcx,%rbx")),
  (642, 3, parse("shrq %cl,%r14")),
  (645, 4, parse("leaq 0x1(%r9),%r15")),
  (649, 3, parse("cmpq %rdx,%r15")),
  (652, 2, parse("jb indices_nat_shr_u589")),
  (654, 3, parse("xorl %r12d,%r12d")),
  (657, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-65)))))]),
  (659, 2, parse("xorl %esi,%esi")),
  (661, 2, parse("xorl %eax,%eax")),
  (663, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (7)))))]),
  (665, 4, parse("movq 0x8(%rsi),%rsi")),
  (669, 3, parse("movq %r8,%rcx")),
  (672, 2, parse("negb %cl")),
  (674, 3, parse("shlq %cl,%rsi"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (677, 3, parse("orq %rax,%rsi")),
  (680, 7, parse("movq $0x0,(%rdi)")),
  (687, 4, parse("movq %rsi,0x8(%rdi)")),
  (691, 2, parse("xorl %eax,%eax")),
  (693, 3, parse("movl %eax,0x40(%rdi)")),
  (696, 1, parse("retq ")),
  (697, 3, parse("shrq %cl,%rdx")),
  (700, 3, parse("movq %rdx,(%r11)")),
  (703, 3, parse("testq %r10,%r10")),
  (706, 6, parse("je indices_nat_shr_u353")),
  (712, 3, parse("movq %r10,%rcx")),
  (715, 4, parse("andq $0x7,%rcx")),
  (719, 2, parse("je indices_nat_shr_u759")),
  (721, 3, parse("negq %rcx")),
  (724, 5, parse("movl $0x1,%esi")),
  (729, 4, parse("leaq 0x1(%rsi),%rdx")),
  (733, 8, parse("movq $0x0,(%r11,%rsi,8)")),
  (741, 4, parse("leaq (%rcx,%rsi,1),%r9")),
  (745, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r9 .W64))))]),
  (748, 3, parse("movq %rdx,%rsi")),
  (751, 4, parse("cmpq $0x1,%r9")),
  (755, 2, parse("jne indices_nat_shr_u729")),
  (757, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (5)))))]),
  (759, 5, parse("movl $0x1,%edx")),
  (764, 4, parse("cmpq $0x8,%r10")),
  (768, 6, parse("jb indices_nat_shr_u353")),
  (774, 4, parse("leaq (%rax,%rdx,8),%rax")),
  (778, 4, parse("addq $0x38,%rax")),
  (782, 3, parse("subq %rdx,%r10")),
  (785, 7, parse("movq $0xffffffffffffffff,%rcx")),
  (792, 9, parse("movq $0x0,-0x30(%rax,%rcx,8)")),
  (801, 9, parse("movq $0x0,-0x28(%rax,%rcx,8)")),
  (810, 9, parse("movq $0x0,-0x20(%rax,%rcx,8)")),
  (819, 9, parse("movq $0x0,-0x18(%rax,%rcx,8)")),
  (828, 9, parse("movq $0x0,-0x10(%rax,%rcx,8)")),
  (837, 9, parse("movq $0x0,-0x8(%rax,%rcx,8)")),
  (846, 8, parse("movq $0x0,(%rax,%rcx,8)")),
  (854, 9, parse("movq $0x0,0x8(%rax,%rcx,8)")),
  (863, 4, parse("addq $0x8,%rcx")),
  (867, 3, parse("cmpq %rcx,%r10")),
  (870, 2, parse("jne indices_nat_shr_u792")),
  (872, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-524)))))])]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1 ++
  programChunk2 ++
  programChunk3

theorem program_length : program.length = 234 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 64 := by rfl
  have h3 : programChunk3.length = 42 := by rfl
  simp only [program, List.length_append, h0, h1, h2, h3]

def labels : List (String × Nat) := [
  ("indices_nat_shr_u16", 16),
  ("indices_nat_shr_u60", 60),
  ("indices_nat_shr_u109", 109),
  ("indices_nat_shr_u126", 126),
  ("indices_nat_shr_u236", 236),
  ("indices_nat_shr_u257", 257),
  ("indices_nat_shr_u272", 272),
  ("indices_nat_shr_u306", 306),
  ("indices_nat_shr_u308", 308),
  ("indices_nat_shr_u319", 319),
  ("indices_nat_shr_u353", 353),
  ("indices_nat_shr_u364", 364),
  ("indices_nat_shr_u394", 394),
  ("indices_nat_shr_u473", 473),
  ("indices_nat_shr_u488", 488),
  ("indices_nat_shr_u501", 501),
  ("indices_nat_shr_u589", 589),
  ("indices_nat_shr_u636", 636),
  ("indices_nat_shr_u659", 659),
  ("indices_nat_shr_u665", 665),
  ("indices_nat_shr_u697", 697),
  ("indices_nat_shr_u729", 729),
  ("indices_nat_shr_u759", 759),
  ("indices_nat_shr_u792", 792)]


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

end SszX86.IndicesNatShr

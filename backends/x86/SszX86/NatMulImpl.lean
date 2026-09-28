module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatMul
open Kraken.X64.Parser

def entry : Nat := 0

def wordOffset : Nat := 832
def memsetOffset : Nat := 148928
def panicFrontiers : List Nat := [814, 817]

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 4, parse("subq $0x28,%rsp")),
  (14, 3, parse("testq %rsi,%rsi")),
  (17, 2, parse("je natMul_u63")),
  (19, 4, parse("leaq 0x1(%rdx),%r12")),
  (23, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (32, 3, parse("movq %r12,%r10")),
  (35, 4, parse("cmpq $0x1,%r12")),
  (39, 2, parse("je natMul_u89")),
  (41, 4, parse("leaq -0x1(%r10),%r12")),
  (45, 6, parse("cmpq $0x0,-0x10(%rsi,%r10,8)")),
  (51, 2, parse("je natMul_u32")),
  (53, 3, parse("movq %rdx,%rax")),
  (56, 3, parse("testq %rcx,%rcx")),
  (59, 2, parse("jne natMul_u129")),
  (61, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (37)))))]),
  (63, 3, parse("testq %rdx,%rdx")),
  (66, 2, parse("je natMul_u119")),
  (68, 6, parse("movl $0x1,%r12d")),
  (74, 3, parse("movq %rdx,%rax")),
  (77, 3, parse("testq %rcx,%rcx")),
  (80, 2, parse("jne natMul_u129")),
  (82, 3, parse("testq %r8,%r8")),
  (85, 2, parse("jne natMul_u181")),
  (87, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (117)))))]),
  (89, 3, parse("xorl %r12d,%r12d")),
  (92, 3, parse("movq %rdx,%rax"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (95, 3, parse("testq %rcx,%rcx")),
  (98, 2, parse("jne natMul_u129")),
  (100, 4, parse("cmpq $0x1,%r10")),
  (104, 3, parse("sete %al")),
  (107, 3, parse("testq %r8,%r8")),
  (110, 3, parse("sete %cl")),
  (113, 2, parse("orb %al,%cl")),
  (115, 2, parse("je natMul_u181")),
  (117, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (87)))))]),
  (119, 3, parse("testq %rcx,%rcx")),
  (122, 2, parse("je natMul_u206")),
  (124, 2, parse("xorl %eax,%eax")),
  (126, 3, parse("xorl %r12d,%r12d")),
  (129, 3, parse("movq %r8,%r10")),
  (132, 3, parse("negq %r10")),
  (135, 4, parse("leaq 0x1(%r8),%r11")),
  (139, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (144, 3, parse("testq %r10,%r10")),
  (147, 2, parse("je natMul_u206")),
  (149, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (152, 4, parse("leaq -0x1(%r11),%r13")),
  (156, 6, parse("cmpq $0x0,-0x10(%rcx,%r11,8)")),
  (162, 3, parse("movq %r13,%r11")),
  (165, 2, parse("je natMul_u144")),
  (167, 3, parse("testq %r12,%r12")),
  (170, 2, parse("je natMul_u206")),
  (172, 4, parse("cmpq $0x1,%r13")),
  (176, 2, parse("jne natMul_u243")),
  (178, 3, parse("movq (%rcx),%r8")),
  (181, 3, parse("movq %r8,%rcx")),
  (184, 3, parse("movq %r9,%r8")),
  (187, 4, parse("addq $0x28,%rsp"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (191, 1, parse("popq %rbx")),
  (192, 2, parse("popq %r12")),
  (194, 2, parse("popq %r13")),
  (196, 2, parse("popq %r14")),
  (198, 2, parse("popq %r15")),
  (200, 1, parse("popq %rbp")),
  (201, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (626)))))]),
  (206, 8, parse("movq $0x0,0x8(%rdi)")),
  (214, 7, parse("movq $0x0,(%rdi)")),
  (221, 7, parse("movl $0x0,0x40(%rdi)")),
  (228, 4, parse("addq $0x28,%rsp")),
  (232, 1, parse("popq %rbx")),
  (233, 2, parse("popq %r12")),
  (235, 2, parse("popq %r13")),
  (237, 2, parse("popq %r14")),
  (239, 2, parse("popq %r15")),
  (241, 1, parse("popq %rbp")),
  (242, 1, parse("retq ")),
  (243, 4, parse("cmpq $0x1,%r12")),
  (247, 2, parse("jne natMul_u275")),
  (249, 3, parse("testq %rsi,%rsi")),
  (252, 6, parse("je natMul_u709")),
  (258, 3, parse("testq %rax,%rax")),
  (261, 6, parse("je natMul_u707")),
  (267, 3, parse("movq (%rsi),%rax")),
  (270, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (434)))))]),
  (275, 3, parse("movq %r13,%r14")),
  (278, 3, parse("addq %r12,%r14")),
  (281, 6, parse("jb natMul_u746")),
  (287, 8, [.instr (.regular .W64 .W64 (.lea (.low .rdx .W64) { base := none, idx := some ⟨.r14, .W64⟩, disp := .int64 (0) }))]),
  (295, 3, parse("movq %r14,%r8")),
  (298, 4, parse("shrq $0x3d,%r8"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (302, 4, parse("setne %r8b")),
  (306, 3, parse("testq %rdx,%rdx")),
  (309, 4, parse("setl %r11b")),
  (313, 3, parse("orb %r8b,%r11b")),
  (316, 2, parse("je natMul_u393")),
  (318, 8, parse("movq $0x0,0x38(%rdi)")),
  (326, 8, parse("movq $0x0,0x30(%rdi)")),
  (334, 8, parse("movq $0x0,0x28(%rdi)")),
  (342, 8, parse("movq $0x0,0x20(%rdi)")),
  (350, 8, parse("movq $0x0,0x18(%rdi)")),
  (358, 8, parse("movq $0x0,0x10(%rdi)")),
  (366, 7, parse("movq $0x1,(%rdi)")),
  (373, 8, parse("movq $0x0,0x8(%rdi)")),
  (381, 7, parse("movl $0x8000,0x40(%rdi)")),
  (388, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-165)))))]),
  (393, 3, parse("movq (%r9),%r15")),
  (396, 4, parse("movq 0x10(%r9),%r11")),
  (400, 3, parse("movq %r11,%rbx")),
  (403, 3, parse("addq %r15,%rbx")),
  (406, 2, parse("jb natMul_u318")),
  (408, 4, parse("cmpq $0xfffffffffffffff8,%rbx")),
  (412, 2, parse("ja natMul_u318")),
  (414, 4, parse("leaq 0x7(%rbx),%r8")),
  (418, 4, parse("andq $0xfffffffffffffff8,%r8")),
  (422, 3, parse("subq %rbx,%r8")),
  (425, 3, parse("addq %r11,%r8")),
  (428, 2, parse("jb natMul_u318")),
  (430, 3, parse("movq %r8,%r11")),
  (433, 3, parse("addq %rdx,%r11")),
  (436, 2, parse("jb natMul_u318")),
  (438, 4, parse("cmpq 0x8(%r9),%r11")),
  (442, 2, parse("ja natMul_u318"))]

def programChunk4 : List (Nat × Nat × Program) := [
  (444, 5, parse("movq %rdi,0x18(%rsp)")),
  (449, 3, parse("movq %r12,%rbp")),
  (452, 3, parse("subq %r10,%rbp")),
  (455, 4, parse("movq %r11,0x10(%r9)")),
  (459, 3, parse("addq %r8,%r15")),
  (462, 3, parse("movq %r15,%rbx")),
  (465, 3, parse("xorl %r15d,%r15d")),
  (468, 3, parse("movq %rbx,%rdi")),
  (471, 5, parse("movq %rsi,0x10(%rsp)")),
  (476, 2, parse("xorl %esi,%esi")),
  (478, 5, parse("movq %rcx,0x20(%rsp)")),
  (483, 4, parse("movq %rax,(%rsp)")),
  (487, 6, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (148435)))))]),
  (493, 5, parse("movq 0x20(%rsp),%rsi")),
  (498, 5, parse("movq %rbx,0x8(%rsp)")),
  (503, 3, parse("movq %rbx,%r10")),
  (506, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (512, 6, parse("cmpq $0x0,0x10(%rsp)")),
  (518, 2, parse("je natMul_u537")),
  (520, 4, parse("cmpq (%rsp),%r15")),
  (524, 2, parse("jae natMul_u552")),
  (526, 5, parse("movq 0x10(%rsp),%rax")),
  (531, 4, parse("movq (%rax,%r15,8),%rcx")),
  (535, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (17)))))]),
  (537, 3, parse("testq %r15,%r15")),
  (540, 5, parse("movl $0x0,%ecx")),
  (545, 5, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .rcx .W64) (.mem (w := .W64) { base := some (.reg .rsp), idx := none, disp := .int64 (0) })))]),
  (550, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2)))))]),
  (552, 2, parse("xorl %ecx,%ecx")),
  (554, 4, parse("leaq 0x1(%r15),%r11")),
  (558, 2, parse("xorl %ebx,%ebx")),
  (560, 3, parse("xorl %r9d,%r9d"))]

def programChunk5 : List (Nat × Nat × Program) := [
  (563, 3, parse("xorl %r8d,%r8d")),
  (566, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (576, 4, parse("leaq (%r15,%rbx,1),%rdi")),
  (580, 3, parse("cmpq %r14,%rdi")),
  (583, 6, parse("jae natMul_u817")),
  (589, 3, parse("movq %rcx,%rax")),
  (592, 4, parse("mulq (%rsi,%rbx,8)")),
  (596, 3, parse("addq %r9,%rax")),
  (599, 3, parse("movq %rdx,%r9")),
  (602, 3, parse("adcq %r8,%r9")),
  (605, 4, parse("addq %rax,(%r10,%rbx,8)")),
  (609, 4, parse("adcq $0x0,%r9")),
  (613, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rbx .W64))))]),
  (616, 6, parse("movl $0x0,%r8d")),
  (622, 3, parse("cmpq %rbx,%r13")),
  (625, 2, parse("jne natMul_u576")),
  (627, 3, parse("addq %r13,%r15")),
  (630, 3, parse("cmpq %r14,%r15")),
  (633, 6, parse("jae natMul_u814")),
  (639, 5, parse("movq 0x8(%rsp),%rax")),
  (644, 4, parse("movq %r9,(%rax,%r15,8)")),
  (648, 4, parse("addq $0x8,%r10")),
  (652, 3, parse("movq %r11,%r15")),
  (655, 3, parse("cmpq %r12,%r11")),
  (658, 6, parse("jne natMul_u512")),
  (664, 5, parse("movq 0x18(%rsp),%rax")),
  (669, 5, parse("movq 0x8(%rsp),%rdx")),
  (674, 4, parse("cmpq $0xffffffffffffffff,%rbp")),
  (678, 2, parse("je natMul_u723")),
  (680, 3, parse("movq %rbp,%rcx")),
  (683, 3, parse("decq %rbp")),
  (686, 5, parse("cmpq $0x0,(%rdx,%rcx,8)"))]

def programChunk6 : List (Nat × Nat × Program) := [
  (691, 2, parse("je natMul_u674")),
  (693, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rcx .W64))))]),
  (696, 4, parse("cmpq $0x1,%rcx")),
  (700, 2, parse("jne natMul_u727")),
  (702, 3, parse("movq (%rdx),%rcx")),
  (705, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (18)))))]),
  (707, 2, parse("xorl %eax,%eax")),
  (709, 3, parse("movq %rcx,%rsi")),
  (712, 3, parse("movq %r8,%rdx")),
  (715, 3, parse("movq %rax,%rcx")),
  (718, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-539)))))]),
  (723, 2, parse("xorl %ecx,%ecx")),
  (725, 2, parse("xorl %edx,%edx")),
  (727, 3, parse("movq %rdx,(%rax)")),
  (730, 4, parse("movq %rcx,0x8(%rax)")),
  (734, 7, parse("movl $0x0,0x40(%rax)")),
  (741, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-518)))))]),
  (746, 7, parse("movq $0x1,(%rdi)")),
  (753, 8, parse("movq $0x0,0x8(%rdi)")),
  (761, 8, parse("movq $0x0,0x10(%rdi)")),
  (769, 8, parse("movq $0x0,0x18(%rdi)")),
  (777, 8, parse("movq $0x0,0x20(%rdi)")),
  (785, 8, parse("movq $0x0,0x28(%rdi)")),
  (793, 8, parse("movq $0x0,0x30(%rdi)")),
  (801, 8, parse("movq $0x0,0x38(%rdi)")),
  (809, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-433)))))])]

def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2 ++ programChunk3 ++ programChunk4 ++ programChunk5 ++ programChunk6

def usedLabels : List (String × Nat) := [
  ("natMul_u32", 32),
  ("natMul_u63", 63),
  ("natMul_u89", 89),
  ("natMul_u119", 119),
  ("natMul_u129", 129),
  ("natMul_u144", 144),
  ("natMul_u181", 181),
  ("natMul_u206", 206),
  ("natMul_u243", 243),
  ("natMul_u275", 275),
  ("natMul_u318", 318),
  ("natMul_u393", 393),
  ("natMul_u512", 512),
  ("natMul_u537", 537),
  ("natMul_u552", 552),
  ("natMul_u576", 576),
  ("natMul_u674", 674),
  ("natMul_u707", 707),
  ("natMul_u709", 709),
  ("natMul_u723", 723),
  ("natMul_u727", 727),
  ("natMul_u746", 746),
  ("natMul_u814", 814),
  ("natMul_u817", 817)]

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((usedLabels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ usedLabels, e.labels.label item.1 = base + Int64.ofNat item.2

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

end SszX86.NatMul

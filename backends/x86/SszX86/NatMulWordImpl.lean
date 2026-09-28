module

public import SszX86.UintImpl

@[expose] public section

namespace SszX86.NatMulWord
open Kraken.X64.Parser

def entry : Nat := 0

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 3, parse("movq %rdx,%r9")),
  (3, 4, parse("cmpq $0x1,%rcx")),
  (7, 2, parse("je natMulWord_u37")),
  (9, 3, parse("testq %rcx,%rcx")),
  (12, 2, parse("jne natMulWord_u99")),
  (14, 8, parse("movq $0x0,0x8(%rdi)")),
  (22, 7, parse("movq $0x0,(%rdi)")),
  (29, 7, parse("movl $0x0,0x40(%rdi)")),
  (36, 1, parse("retq ")),
  (37, 3, parse("testq %rsi,%rsi")),
  (40, 2, parse("je natMulWord_u82")),
  (42, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r9 .W64))))]),
  (45, 3, parse("movq %r9,%rax")),
  (48, 4, parse("cmpq $0x1,%rax")),
  (52, 6, parse("je natMulWord_u368")),
  (58, 4, parse("leaq -0x1(%rax),%r9")),
  (62, 6, parse("cmpq $0x0,-0x10(%rsi,%rax,8)")),
  (68, 3, parse("movq %r9,%rax")),
  (71, 2, parse("je natMulWord_u48")),
  (73, 4, parse("cmpq $0x1,%r9")),
  (77, 2, parse("jne natMulWord_u84")),
  (79, 3, parse("movq (%rsi),%r9")),
  (82, 2, parse("xorl %esi,%esi")),
  (84, 3, parse("movq %rsi,(%rdi)")),
  (87, 4, parse("movq %r9,0x8(%rdi)")),
  (91, 7, parse("movl $0x0,0x40(%rdi)")),
  (98, 1, parse("retq ")),
  (99, 1, parse("pushq %rbp")),
  (100, 2, parse("pushq %r15")),
  (102, 2, parse("pushq %r14")),
  (104, 2, parse("pushq %r13")),
  (106, 2, parse("pushq %r12"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (108, 1, parse("pushq %rbx")),
  (109, 4, parse("subq $0x10,%rsp")),
  (113, 3, parse("testq %rsi,%rsi")),
  (116, 6, parse("je natMulWord_u396")),
  (122, 4, parse("leaq 0x3(%r9),%rbx")),
  (126, 7, parse("movq $0xffffffffffffffff,%r11")),
  (133, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (143, 1, [.instr (.regular .W64 .W64 (.nop 1))]),
  (144, 4, parse("cmpq $0x3,%rbx")),
  (148, 6, parse("je natMulWord_u388")),
  (154, 3, parse("movq %rbx,%r15")),
  (157, 3, parse("decq %rbx")),
  (160, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r11 .W64))))]),
  (163, 6, parse("cmpq $0x0,-0x20(%rsi,%r15,8)")),
  (169, 2, parse("je natMulWord_u144")),
  (171, 4, parse("addq $0xfffffffffffffffd,%r15")),
  (175, 4, parse("cmpq $0x1,%r15")),
  (179, 6, parse("je natMulWord_u393")),
  (185, 4, parse("cmpq $0xffffffffffffffff,%r15")),
  (189, 6, parse("je natMulWord_u807")),
  (195, 10, parse("movabsq $0x1ffffffffffffffe,%r12")),
  (205, 3, parse("cmpq %r12,%r15")),
  (208, 3, parse("seta %dl")),
  (211, 8, [.instr (.regular .W64 .W64 (.lea (.low .rax .W64) { base := none, idx := some ⟨.r15, .W64⟩, disp := .int64 (0) }))]),
  (219, 4, parse("addq $0x8,%rax")),
  (223, 3, parse("testq %rax,%rax")),
  (226, 4, parse("setl %r10b")),
  (230, 3, parse("orb %dl,%r10b")),
  (233, 6, parse("jne natMulWord_u617")),
  (239, 3, parse("movq (%r8),%r14")),
  (242, 4, parse("movq 0x10(%r8),%rdx")),
  (246, 3, parse("movq %rdx,%r10"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (249, 3, parse("addq %r14,%r10")),
  (252, 6, parse("jb natMulWord_u617")),
  (258, 4, parse("cmpq $0xfffffffffffffff8,%r10")),
  (262, 6, parse("ja natMulWord_u617")),
  (268, 4, parse("leaq 0x7(%r10),%rbp")),
  (272, 4, parse("andq $0xfffffffffffffff8,%rbp")),
  (276, 3, parse("movq %rbp,%r13")),
  (279, 3, parse("subq %r10,%r13")),
  (282, 3, parse("addq %rdx,%r13")),
  (285, 6, parse("jb natMulWord_u617")),
  (291, 3, parse("addq %r13,%rax")),
  (294, 6, parse("jb natMulWord_u617")),
  (300, 4, parse("cmpq 0x8(%r8),%rax")),
  (304, 6, parse("ja natMulWord_u617")),
  (310, 4, parse("movq %rax,0x10(%r8)")),
  (314, 3, parse("movq %rcx,%rax")),
  (317, 3, parse("mulq (%rsi)")),
  (320, 3, parse("movq %rdx,%r10")),
  (323, 4, parse("movq %rax,(%rsp)")),
  (327, 5, parse("movq %r13,0x8(%rsp)")),
  (332, 4, parse("movq %rax,(%r14,%r13,1)")),
  (336, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r11 .W64))))]),
  (339, 6, parse("movl $0x1,%r8d")),
  (345, 3, parse("cmpq %r11,%r9")),
  (348, 6, parse("je natMulWord_u706")),
  (354, 3, parse("andq %r15,%r12")),
  (357, 4, parse("addq $0x8,%rbp")),
  (361, 5, parse("movl $0x1,%eax")),
  (366, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (98)))))]),
  (368, 2, parse("xorl %esi,%esi")),
  (370, 3, parse("xorl %r9d,%r9d")),
  (373, 3, parse("movq %rsi,(%rdi)"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (376, 4, parse("movq %r9,0x8(%rdi)")),
  (380, 7, parse("movl $0x0,0x40(%rdi)")),
  (387, 1, parse("retq ")),
  (388, 3, parse("testq %r9,%r9")),
  (391, 2, parse("je natMulWord_u513")),
  (393, 3, parse("movq (%rsi),%r9")),
  (396, 3, parse("movq %r9,%rax")),
  (399, 3, parse("mulq %rcx")),
  (402, 3, parse("testq %rdx,%rdx")),
  (405, 2, parse("jne natMulWord_u527")),
  (407, 7, parse("movq $0x0,(%rdi)")),
  (414, 4, parse("movq %rax,0x8(%rdi)")),
  (418, 7, parse("movl $0x0,0x40(%rdi)")),
  (425, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (257)))))]),
  (430, 5, parse("movq 0x8(%rsi,%r8,8),%rax")),
  (435, 3, parse("mulq %rcx")),
  (438, 3, parse("movq %rdx,%r10")),
  (441, 3, parse("addq %r11,%rax")),
  (444, 4, parse("adcq $0x0,%r10")),
  (448, 5, parse("movq %rax,0x0(%rbp,%r8,8)")),
  (453, 4, parse("leaq 0x1(%r13),%rax")),
  (457, 3, parse("cmpq %r12,%r13")),
  (460, 6, parse("je natMulWord_u702")),
  (466, 3, parse("movq %rax,%r8")),
  (469, 3, parse("cmpq %r9,%rax")),
  (472, 2, parse("jae natMulWord_u480")),
  (474, 4, parse("movq (%rsi,%r8,8),%rax")),
  (478, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2)))))]),
  (480, 2, parse("xorl %eax,%eax")),
  (482, 3, parse("mulq %rcx")),
  (485, 3, parse("movq %rdx,%r11")),
  (488, 3, parse("addq %r10,%rax"))]

def programChunk4 : List (Nat × Nat × Program) := [
  (491, 4, parse("adcq $0x0,%r11")),
  (495, 5, parse("movq %rax,-0x8(%rbp,%r8,8)")),
  (500, 4, parse("leaq 0x1(%r8),%r13")),
  (504, 3, parse("cmpq %r9,%r13")),
  (507, 2, parse("jb natMulWord_u430")),
  (509, 2, parse("xorl %eax,%eax")),
  (511, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-78)))))]),
  (513, 3, parse("xorl %r9d,%r9d")),
  (516, 3, parse("movq %r9,%rax")),
  (519, 3, parse("mulq %rcx")),
  (522, 3, parse("testq %rdx,%rdx")),
  (525, 2, parse("je natMulWord_u407")),
  (527, 3, parse("movq (%r8),%rcx")),
  (530, 4, parse("movq 0x10(%r8),%r9")),
  (534, 3, parse("movq %r9,%r10")),
  (537, 3, parse("addq %rcx,%r10")),
  (540, 2, parse("jb natMulWord_u617")),
  (542, 4, parse("cmpq $0xfffffffffffffff8,%r10")),
  (546, 2, parse("ja natMulWord_u617")),
  (548, 4, parse("leaq 0x7(%r10),%rsi")),
  (552, 4, parse("andq $0xfffffffffffffff8,%rsi")),
  (556, 3, parse("subq %r10,%rsi")),
  (559, 3, parse("addq %r9,%rsi")),
  (562, 2, parse("jb natMulWord_u617")),
  (564, 4, parse("cmpq $0xffffffffffffffef,%rsi")),
  (568, 2, parse("ja natMulWord_u617")),
  (570, 4, parse("leaq 0x10(%rsi),%r9")),
  (574, 4, parse("cmpq 0x8(%r8),%r9")),
  (578, 2, parse("ja natMulWord_u617")),
  (580, 4, parse("movq %r9,0x10(%r8)")),
  (584, 4, parse("leaq (%rcx,%rsi,1),%r8")),
  (588, 4, parse("movq %rax,(%rcx,%rsi,1)"))]

def programChunk5 : List (Nat × Nat × Program) := [
  (592, 5, parse("movq %rdx,0x8(%rcx,%rsi,1)")),
  (597, 3, parse("movq %r8,(%rdi)")),
  (600, 8, parse("movq $0x2,0x8(%rdi)")),
  (608, 7, parse("movl $0x0,0x40(%rdi)")),
  (615, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (70)))))]),
  (617, 8, parse("movq $0x0,0x38(%rdi)")),
  (625, 8, parse("movq $0x0,0x30(%rdi)")),
  (633, 8, parse("movq $0x0,0x28(%rdi)")),
  (641, 8, parse("movq $0x0,0x20(%rdi)")),
  (649, 8, parse("movq $0x0,0x18(%rdi)")),
  (657, 8, parse("movq $0x0,0x10(%rdi)")),
  (665, 7, parse("movq $0x1,(%rdi)")),
  (672, 8, parse("movq $0x0,0x8(%rdi)")),
  (680, 7, parse("movl $0x8000,0x40(%rdi)")),
  (687, 4, parse("addq $0x10,%rsp")),
  (691, 1, parse("popq %rbx")),
  (692, 2, parse("popq %r12")),
  (694, 2, parse("popq %r13")),
  (696, 2, parse("popq %r14")),
  (698, 2, parse("popq %r15")),
  (700, 1, parse("popq %rbp")),
  (701, 1, parse("retq ")),
  (702, 4, parse("addq $0x2,%r8")),
  (706, 5, parse("addq 0x8(%rsp),%r14")),
  (711, 4, parse("testb $0x1,%r15b")),
  (715, 2, parse("je natMulWord_u741")),
  (717, 3, parse("cmpq %r9,%r8")),
  (720, 2, parse("jae natMulWord_u728")),
  (722, 4, parse("movq (%rsi,%r8,8),%rax")),
  (726, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2)))))]),
  (728, 2, parse("xorl %eax,%eax")),
  (730, 4, parse("imulq %rcx,%rax"))]

def programChunk6 : List (Nat × Nat × Program) := [
  (734, 3, parse("addq %r10,%rax")),
  (737, 4, parse("movq %rax,(%r14,%r8,8)")),
  (741, 2, parse("xorl %eax,%eax")),
  (743, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (752, 4, parse("cmpq $0x1,%rbx")),
  (756, 2, parse("je natMulWord_u796")),
  (758, 4, parse("leaq -0x1(%rbx),%rcx")),
  (762, 6, parse("cmpq $0x0,-0x10(%r14,%rbx,8)")),
  (768, 3, parse("movq %rcx,%rbx")),
  (771, 2, parse("je natMulWord_u752")),
  (773, 2, parse("xorl %eax,%eax")),
  (775, 4, parse("cmpq $0x1,%rcx")),
  (779, 4, parse("movq (%rsp),%rdx")),
  (783, 4, parse("cmovne %rcx,%rdx")),
  (787, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r14 .W64) (.reg (.low .rax .W64))))]),
  (791, 3, parse("movq %rdx,%rax")),
  (794, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (3)))))]),
  (796, 3, parse("xorl %r14d,%r14d")),
  (799, 3, parse("movq %r14,(%rdi)")),
  (802, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-393)))))]),
  (807, 7, parse("movq $0x1,(%rdi)")),
  (814, 8, parse("movq $0x0,0x8(%rdi)")),
  (822, 8, parse("movq $0x0,0x10(%rdi)")),
  (830, 8, parse("movq $0x0,0x18(%rdi)")),
  (838, 8, parse("movq $0x0,0x20(%rdi)")),
  (846, 8, parse("movq $0x0,0x28(%rdi)")),
  (854, 8, parse("movq $0x0,0x30(%rdi)")),
  (862, 8, parse("movq $0x0,0x38(%rdi)")),
  (870, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-195)))))])]

def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2 ++ programChunk3 ++ programChunk4 ++ programChunk5 ++ programChunk6

def usedLabels : List (String × Nat) := [
  ("natMulWord_u37", 37),
  ("natMulWord_u48", 48),
  ("natMulWord_u82", 82),
  ("natMulWord_u84", 84),
  ("natMulWord_u99", 99),
  ("natMulWord_u144", 144),
  ("natMulWord_u368", 368),
  ("natMulWord_u388", 388),
  ("natMulWord_u393", 393),
  ("natMulWord_u396", 396),
  ("natMulWord_u407", 407),
  ("natMulWord_u430", 430),
  ("natMulWord_u480", 480),
  ("natMulWord_u513", 513),
  ("natMulWord_u527", 527),
  ("natMulWord_u617", 617),
  ("natMulWord_u702", 702),
  ("natMulWord_u706", 706),
  ("natMulWord_u728", 728),
  ("natMulWord_u741", 741),
  ("natMulWord_u752", 752),
  ("natMulWord_u796", 796),
  ("natMulWord_u807", 807)]

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

end SszX86.NatMulWord

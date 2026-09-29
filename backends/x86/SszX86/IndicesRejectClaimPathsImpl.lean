module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesRejectClaimPaths
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2276336
def machineSize : Nat := 879

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 4, parse("subq $0x78,%rsp")),
  (14, 3, parse("movq %rdx,%r13")),
  (17, 3, parse("movq %rsi,%rbx")),
  (20, 4, parse("shlq $0x4,%r8")),
  (24, 3, parse("addq %rcx,%r8")),
  (27, 4, parse("shlq $0x4,%r13")),
  (31, 3, parse("addq %rsi,%r13")),
  (34, 6, parse("movl $0x1,%r10d")),
  (40, 3, parse("movq (%rcx),%rbp")),
  (43, 4, parse("movq 0x8(%rcx),%r14")),
  (47, 3, parse("movq %r14,%rax")),
  (50, 3, parse("testq %rbp,%rbp")),
  (53, 2, parse("je indices_reject_claim_paths_u144")),
  (55, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (64, 4, parse("subq $0x1,%rax")),
  (68, 6, parse("jb indices_reject_claim_paths_u763")),
  (74, 6, parse("cmpq $0x0,0x0(%rbp,%rax,8)")),
  (80, 2, parse("je indices_reject_claim_paths_u64")),
  (82, 4, parse("leaq 0x1(%r14),%rax")),
  (86, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (96, 4, parse("cmpq $0x1,%rax")),
  (100, 6, parse("je indices_reject_claim_paths_u639")),
  (106, 5, parse("movq -0x10(%rbp,%rax,8),%rdx")),
  (111, 3, parse("decq %rax")),
  (114, 3, parse("testq %rdx,%rdx")),
  (117, 2, parse("je indices_reject_claim_paths_u96")),
  (119, 3, parse("movq %rax,%r15")),
  (122, 4, parse("shrq $0x3a,%r15")),
  (126, 4, parse("shlq $0x6,%rax")),
  (130, 4, parse("addq $0xffffffffffffffc0,%rax")),
  (134, 4, parse("adcq $0xffffffffffffffff,%r15")),
  (138, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (21)))))]),
  (140, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (144, 3, parse("testq %r14,%r14")),
  (147, 6, parse("je indices_reject_claim_paths_u758")),
  (153, 3, parse("movq %r14,%rdx")),
  (156, 2, parse("xorl %eax,%eax")),
  (158, 3, parse("xorl %r15d,%r15d")),
  (161, 5, parse("leaq -0x10(%rsp),%rsp")),
  (166, 4, parse("movq %r11,(%rsp)")),
  (170, 5, parse("movq %r10,0x8(%rsp)")),
  (175, 3, parse("movq %rdx,%r11")),
  (178, 3, parse("testq %r11,%r11")),
  (181, 2, parse("je indices_reject_claim_paths_u207")),
  (183, 7, parse("movq $0xffffffffffffffff,%r10")),
  (190, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (193, 3, parse("shrq $1,%r11")),
  (196, 2, parse("jne indices_reject_claim_paths_u190")),
  (198, 3, parse("movq %r10,%r12")),
  (201, 4, parse("cmpq $0xffffffffffffffff,%r10")),
  (205, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))]),
  (207, 4, parse("movq (%rsp),%r11")),
  (211, 5, parse("movq 0x8(%rsp),%r10")),
  (216, 5, parse("leaq 0x10(%rsp),%rsp")),
  (221, 3, [.instr (.regular .W64 .W32 (.inc (.reg (.low .r12 .W32))))]),
  (224, 3, parse("addq %rax,%r12")),
  (227, 4, parse("adcq $0x0,%r15")),
  (231, 3, parse("cmpq %r12,%r10"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (234, 5, parse("movl $0x0,%eax")),
  (239, 3, parse("sbbq %r15,%rax")),
  (242, 6, parse("jae indices_reject_claim_paths_u639")),
  (248, 5, parse("movq %r8,0x60(%rsp)")),
  (253, 5, parse("movq %rdi,0x28(%rsp)")),
  (258, 4, parse("addq $0x10,%rcx")),
  (262, 5, parse("movq %rcx,0x58(%rsp)")),
  (267, 3, parse("movq %r12,%rax")),
  (270, 4, parse("addq $0xffffffffffffffff,%rax")),
  (274, 5, parse("movq %rax,0x70(%rsp)")),
  (279, 3, parse("movq %r15,%rax")),
  (282, 4, parse("adcq $0xffffffffffffffff,%rax")),
  (286, 5, parse("movq %rax,0x68(%rsp)")),
  (291, 5, parse("movq %rbx,0x50(%rsp)")),
  (296, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (19)))))]),
  (298, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (304, 4, parse("addq $0x10,%rbx")),
  (308, 3, parse("cmpq %r13,%rbx")),
  (311, 6, parse("je indices_reject_claim_paths_u592")),
  (317, 3, parse("movq (%rbx),%r9")),
  (320, 4, parse("movq 0x8(%rbx),%rax")),
  (324, 3, parse("testq %r9,%r9")),
  (327, 2, parse("je indices_reject_claim_paths_u384")),
  (329, 4, parse("leaq 0x1(%rax),%rcx")),
  (333, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (336, 4, parse("cmpq $0x1,%rcx")),
  (340, 2, parse("je indices_reject_claim_paths_u304")),
  (342, 5, parse("movq -0x10(%r9,%rcx,8),%rdx")),
  (347, 3, parse("decq %rcx")),
  (350, 3, parse("testq %rdx,%rdx")),
  (353, 2, parse("je indices_reject_claim_paths_u336")),
  (355, 3, parse("movq %rcx,%r10")),
  (358, 4, parse("shrq $0x3a,%r10")),
  (362, 4, parse("shlq $0x6,%rcx")),
  (366, 4, parse("addq $0xffffffffffffffc0,%rcx")),
  (370, 4, parse("adcq $0xffffffffffffffff,%r10")),
  (374, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (27)))))]),
  (376, 8, [.instr (.regular .W64 .W64 (.nop 8))]),
  (384, 3, parse("movq %rax,%rdx")),
  (387, 5, parse("movl $0x0,%ecx")),
  (392, 6, parse("movl $0x0,%r10d")),
  (398, 3, parse("testq %rax,%rax")),
  (401, 2, parse("je indices_reject_claim_paths_u304")),
  (403, 5, parse("leaq -0x10(%rsp),%rsp")),
  (408, 4, parse("movq %r11,(%rsp)")),
  (412, 5, parse("movq %r10,0x8(%rsp)")),
  (417, 3, parse("movq %rdx,%r11")),
  (420, 3, parse("testq %r11,%r11")),
  (423, 2, parse("je indices_reject_claim_paths_u449")),
  (425, 7, parse("movq $0xffffffffffffffff,%r10")),
  (432, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (435, 3, parse("shrq $1,%r11")),
  (438, 2, parse("jne indices_reject_claim_paths_u432")),
  (440, 3, parse("movq %r10,%rdi")),
  (443, 4, parse("cmpq $0xffffffffffffffff,%r10")),
  (447, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))]),
  (449, 4, parse("movq (%rsp),%r11")),
  (453, 5, parse("movq 0x8(%rsp),%r10")),
  (458, 5, parse("leaq 0x10(%rsp),%rsp")),
  (463, 2, [.instr (.regular .W64 .W32 (.inc (.reg (.low .rdi .W32))))]),
  (465, 3, parse("addq %rcx,%rdi")),
  (468, 4, parse("adcq $0x0,%r10")),
  (472, 3, parse("movq %rdi,%rdx")),
  (475, 4, parse("addq $0xffffffffffffffff,%rdx"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (479, 3, parse("movq %r10,%rcx")),
  (482, 4, parse("adcq $0xffffffffffffffff,%rcx")),
  (486, 4, parse("cmpq $0x2,%rdi")),
  (490, 3, parse("movq %r10,%r8")),
  (493, 4, parse("sbbq $0x0,%r8")),
  (497, 6, parse("jb indices_reject_claim_paths_u304")),
  (503, 5, parse("cmpq 0x70(%rsp),%rdx")),
  (508, 5, parse("sbbq 0x68(%rsp),%rcx")),
  (513, 6, parse("jae indices_reject_claim_paths_u304")),
  (519, 3, parse("movq %r12,%rdx")),
  (522, 3, parse("subq %rdi,%rdx")),
  (525, 3, parse("movq %r15,%rcx")),
  (528, 3, parse("sbbq %r10,%rcx")),
  (531, 4, parse("movq %rax,(%rsp)")),
  (535, 9, parse("movq $0x0,0x18(%rsp)")),
  (544, 9, parse("movq $0x0,0x10(%rsp)")),
  (553, 3, parse("movq %rbp,%rdi")),
  (556, 3, parse("movq %r14,%rsi")),
  (559, 3, parse("xorl %r8d,%r8d")),
  (562, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-11447)))))]),
  (567, 2, parse("testb %al,%al")),
  (569, 6, parse("je indices_reject_claim_paths_u304")),
  (575, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (112)))))]),
  (577, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (587, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (592, 5, parse("movq 0x60(%rsp),%r8")),
  (597, 5, parse("movq 0x58(%rsp),%rcx")),
  (602, 3, parse("cmpq %r8,%rcx")),
  (605, 5, parse("movq 0x28(%rsp),%rdi")),
  (610, 5, parse("movq 0x50(%rsp),%rbx")),
  (615, 6, parse("movl $0x1,%r10d")),
  (621, 6, parse("jne indices_reject_claim_paths_u40")),
  (627, 7, parse("movl $0x0,0x40(%rdi)")),
  (634, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (225)))))]),
  (639, 9, parse("movq $0x0,0x48(%rsp)")),
  (648, 9, parse("movq $0x0,0x40(%rsp)")),
  (657, 9, parse("movq $0x0,0x38(%rsp)")),
  (666, 9, parse("movq $0x0,0x30(%rsp)")),
  (675, 5, parse("movl $0x28,%eax")),
  (680, 3, parse("xorl %r14d,%r14d")),
  (683, 2, parse("xorl %ecx,%ecx")),
  (685, 2, parse("xorl %ebp,%ebp")),
  (687, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (117)))))]),
  (689, 5, parse("movq 0x28(%rsp),%rax")),
  (694, 7, parse("movq $0x1,(%rax)")),
  (701, 8, parse("movq $0x0,0x8(%rax)")),
  (709, 4, parse("movq %rbp,0x10(%rax)")),
  (713, 4, parse("movq %r14,0x18(%rax)")),
  (717, 8, parse("movq $0x0,0x20(%rax)")),
  (725, 8, parse("movq $0x0,0x28(%rax)")),
  (733, 8, parse("movq $0x0,0x30(%rax)")),
  (741, 8, parse("movq $0x0,0x38(%rax)")),
  (749, 7, parse("movl $0x2b,0x40(%rax)")),
  (756, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (106)))))]),
  (758, 3, parse("xorl %r14d,%r14d")),
  (761, 2, parse("xorl %ebp,%ebp")),
  (763, 9, parse("movq $0x0,0x48(%rsp)")),
  (772, 9, parse("movq $0x0,0x40(%rsp)")),
  (781, 9, parse("movq $0x0,0x38(%rsp)")),
  (790, 9, parse("movq $0x0,0x30(%rsp)")),
  (799, 5, parse("movl $0x27,%eax")),
  (804, 2, parse("xorl %ecx,%ecx")),
  (806, 7, parse("movq $0x1,(%rdi)")),
  (813, 4, parse("movq %rcx,0x8(%rdi)"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (817, 4, parse("movq %rbp,0x10(%rdi)")),
  (821, 4, parse("movq %r14,0x18(%rdi)")),
  (825, 5, parse("movq 0x30(%rsp),%rcx")),
  (830, 5, parse("movq 0x38(%rsp),%rdx")),
  (835, 4, parse("movq %rcx,0x20(%rdi)")),
  (839, 4, parse("movq %rdx,0x28(%rdi)")),
  (843, 5, parse("movq 0x40(%rsp),%rcx")),
  (848, 4, parse("movq %rcx,0x30(%rdi)")),
  (852, 5, parse("movq 0x48(%rsp),%rcx")),
  (857, 4, parse("movq %rcx,0x38(%rdi)")),
  (861, 3, parse("movl %eax,0x40(%rdi)")),
  (864, 4, parse("addq $0x78,%rsp")),
  (868, 1, parse("popq %rbx")),
  (869, 2, parse("popq %r12")),
  (871, 2, parse("popq %r13")),
  (873, 2, parse("popq %r14")),
  (875, 2, parse("popq %r15")),
  (877, 1, parse("popq %rbp")),
  (878, 1, parse("retq "))]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1 ++
  programChunk2 ++
  programChunk3

theorem program_length : program.length = 211 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 64 := by rfl
  have h3 : programChunk3.length = 19 := by rfl
  simp only [program, List.length_append, h0, h1, h2, h3]

def labels : List (String × Nat) := [
  ("indices_reject_claim_paths_u40", 40),
  ("indices_reject_claim_paths_u64", 64),
  ("indices_reject_claim_paths_u96", 96),
  ("indices_reject_claim_paths_u144", 144),
  ("indices_reject_claim_paths_u190", 190),
  ("indices_reject_claim_paths_u207", 207),
  ("indices_reject_claim_paths_u304", 304),
  ("indices_reject_claim_paths_u336", 336),
  ("indices_reject_claim_paths_u384", 384),
  ("indices_reject_claim_paths_u432", 432),
  ("indices_reject_claim_paths_u449", 449),
  ("indices_reject_claim_paths_u592", 592),
  ("indices_reject_claim_paths_u639", 639),
  ("indices_reject_claim_paths_u758", 758),
  ("indices_reject_claim_paths_u763", 763)]

def indicesPrefixEqualOffset : Int := -10880

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

end SszX86.IndicesRejectClaimPaths

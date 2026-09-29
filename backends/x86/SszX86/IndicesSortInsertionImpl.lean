module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesSortInsertion
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2267088
def machineSize : Nat := 624

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 1, parse("pushq %rax")),
  (11, 3, parse("movq %rsi,%rbx")),
  (14, 3, parse("movq %rdi,%r14")),
  (17, 4, parse("shlq $0x4,%rbx")),
  (21, 3, parse("addq %rdi,%rbx")),
  (24, 4, parse("leaq 0x10(%rdi),%rax")),
  (28, 3, parse("movq %rdi,%rbp")),
  (31, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (38)))))]),
  (33, 3, parse("movq %r14,%rax")),
  (36, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (46, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (48, 3, parse("movq %r15,(%rax)")),
  (51, 4, parse("movq %r12,0x8(%rax)")),
  (55, 4, parse("leaq 0x10(%r13),%rax")),
  (59, 3, parse("movq %r13,%rbp")),
  (62, 3, parse("cmpq %rbx,%rax")),
  (65, 6, parse("je indices_sort_insertion_u609")),
  (71, 3, parse("movq %rax,%r13")),
  (74, 4, parse("movq 0x10(%rbp),%r15")),
  (78, 4, parse("movq 0x18(%rbp),%r12")),
  (82, 4, parse("movq 0x0(%rbp),%rdi")),
  (86, 4, parse("movq 0x8(%rbp),%rsi")),
  (90, 3, parse("movq %r15,%rdx")),
  (93, 3, parse("movq %r12,%rcx")),
  (96, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-112741)))))]),
  (101, 2, parse("cmpb $0xff,%al")),
  (103, 2, parse("jne indices_sort_insertion_u55")),
  (105, 2, parse("xorl %ecx,%ecx")),
  (107, 3, parse("testq %r12,%r12")),
  (110, 3, parse("setne %cl")),
  (113, 5, parse("leaq 0x1(%r12),%rdx")),
  (118, 3, parse("movq %r13,%rsi")),
  (121, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (10)))))]),
  (123, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (128, 3, parse("movq %rax,%rsi")),
  (131, 2, parse("jae indices_sort_insertion_u48")),
  (133, 4, parse("movq 0x0(%rbp),%rdi")),
  (137, 4, parse("movq 0x8(%rbp),%r8")),
  (141, 4, parse("movq %r8,0x8(%rsi)")),
  (145, 3, parse("movq %rdi,(%rsi)")),
  (148, 3, parse("cmpq %r14,%rbp")),
  (151, 2, parse("je indices_sort_insertion_u33")),
  (153, 3, parse("movq %rbp,%rax")),
  (156, 4, parse("movq -0x10(%rbp),%r8")),
  (160, 4, parse("movq -0x8(%rbp),%rsi")),
  (164, 3, parse("testq %r8,%r8")),
  (167, 2, parse("je indices_sort_insertion_u208")),
  (169, 4, parse("leaq 0x1(%rsi),%r9")),
  (173, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (176, 4, parse("cmpq $0x1,%r9")),
  (180, 2, parse("je indices_sort_insertion_u240")),
  (182, 4, parse("leaq -0x1(%r9),%rdi")),
  (186, 6, parse("cmpq $0x0,-0x10(%r8,%r9,8)")),
  (192, 3, parse("movq %rdi,%r9")),
  (195, 2, parse("je indices_sort_insertion_u176")),
  (197, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (18)))))]),
  (199, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (208, 2, parse("xorl %edi,%edi"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (210, 3, parse("testq %rsi,%rsi")),
  (213, 4, parse("setne %dil")),
  (217, 3, parse("movq %rcx,%r9")),
  (220, 3, parse("movq %rdx,%r10")),
  (223, 3, parse("testq %r15,%r15")),
  (226, 2, parse("jne indices_sort_insertion_u256")),
  (228, 4, parse("leaq -0x10(%rax),%rbp")),
  (232, 3, parse("cmpq %r9,%rdi")),
  (235, 2, parse("jne indices_sort_insertion_u128")),
  (237, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (65)))))]),
  (239, 1, [.instr (.regular .W64 .W64 (.nop 1))]),
  (240, 2, parse("xorl %edi,%edi")),
  (242, 3, parse("movq %rcx,%r9")),
  (245, 3, parse("movq %rdx,%r10")),
  (248, 3, parse("testq %r15,%r15")),
  (251, 2, parse("je indices_sort_insertion_u228")),
  (253, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (256, 4, parse("cmpq $0x1,%r10")),
  (260, 2, parse("je indices_sort_insertion_u288")),
  (262, 4, parse("leaq -0x1(%r10),%r9")),
  (266, 6, parse("cmpq $0x0,-0x10(%r15,%r10,8)")),
  (272, 3, parse("movq %r9,%r10")),
  (275, 2, parse("je indices_sort_insertion_u256")),
  (277, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-51)))))]),
  (279, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (288, 3, parse("xorl %r9d,%r9d")),
  (291, 4, parse("leaq -0x10(%rax),%rbp")),
  (295, 3, parse("cmpq %r9,%rdi")),
  (298, 6, parse("jne indices_sort_insertion_u128")),
  (304, 3, parse("testq %r8,%r8")),
  (307, 6, parse("je indices_sort_insertion_u463")),
  (313, 3, parse("decq %rdi")),
  (316, 3, parse("testq %r15,%r15")),
  (319, 2, parse("jne indices_sort_insertion_u352")),
  (321, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (120)))))]),
  (323, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (333, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (336, 4, parse("movq (%r15,%rdi,8),%r10")),
  (340, 3, parse("decq %rdi")),
  (343, 3, parse("cmpq %r10,%r9")),
  (346, 6, parse("jne indices_sort_insertion_u592")),
  (352, 4, parse("cmpq $0xffffffffffffffff,%rdi")),
  (356, 6, parse("je indices_sort_insertion_u48")),
  (362, 3, parse("cmpq %rsi,%rdi")),
  (365, 2, parse("jae indices_sort_insertion_u384")),
  (367, 4, parse("movq (%r8,%rdi,8),%r9")),
  (371, 3, parse("cmpq %r12,%rdi")),
  (374, 2, parse("jb indices_sort_insertion_u336")),
  (376, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (14)))))]),
  (378, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (384, 3, parse("xorl %r9d,%r9d")),
  (387, 3, parse("cmpq %r12,%rdi")),
  (390, 2, parse("jb indices_sort_insertion_u336")),
  (392, 3, parse("xorl %r10d,%r10d")),
  (395, 3, parse("decq %rdi")),
  (398, 3, parse("cmpq %r10,%r9")),
  (401, 2, parse("je indices_sort_insertion_u352")),
  (403, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (184)))))]),
  (408, 8, [.instr (.regular .W64 .W64 (.nop 8))]),
  (416, 4, parse("movq (%r8,%rdi,8),%r9")),
  (420, 4, parse("subq $0x1,%rdi")),
  (424, 6, parse("movl $0x0,%r10d")),
  (430, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r10 .W64) (.reg (.low .r12 .W64))))]),
  (434, 3, parse("cmpq %r10,%r9"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (437, 6, parse("jne indices_sort_insertion_u592")),
  (443, 4, parse("cmpq $0xffffffffffffffff,%rdi")),
  (447, 6, parse("je indices_sort_insertion_u48")),
  (453, 3, parse("cmpq %rsi,%rdi")),
  (456, 2, parse("jb indices_sort_insertion_u416")),
  (458, 3, parse("xorl %r9d,%r9d")),
  (461, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-43)))))]),
  (463, 3, parse("testq %r15,%r15")),
  (466, 2, parse("je indices_sort_insertion_u544")),
  (468, 3, parse("decq %rdi")),
  (471, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (15)))))]),
  (473, 7, [.instr (.regular .W64 .W64 (.nop 7))]),
  (480, 3, parse("movq %r8,%rdi")),
  (483, 3, parse("cmpq %r10,%r9")),
  (486, 2, parse("jne indices_sort_insertion_u592")),
  (488, 4, parse("cmpq $0xffffffffffffffff,%rdi")),
  (492, 6, parse("je indices_sort_insertion_u48")),
  (498, 3, parse("movq %rdi,%r8")),
  (501, 4, parse("subq $0x1,%r8")),
  (505, 6, parse("movl $0x0,%r9d")),
  (511, 4, [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r9 .W64) (.reg (.low .rsi .W64))))]),
  (515, 6, parse("movl $0x0,%r10d")),
  (521, 3, parse("cmpq %r12,%rdi")),
  (524, 2, parse("jae indices_sort_insertion_u480")),
  (526, 4, parse("movq (%r15,%rdi,8),%r10")),
  (530, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-52)))))]),
  (532, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (542, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (544, 4, parse("subq $0x1,%rdi")),
  (548, 6, parse("jb indices_sort_insertion_u48")),
  (554, 6, parse("movl $0x0,%r9d")),
  (560, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r9 .W64) (.reg (.low .rsi .W64))))]),
  (564, 6, parse("movl $0x0,%r10d")),
  (570, 4, [.instr (.regular .W64 .W64 (.cmovcc .z (.low .r10 .W64) (.reg (.low .r12 .W64))))]),
  (574, 3, parse("cmpq %r10,%r9")),
  (577, 2, parse("je indices_sort_insertion_u544")),
  (579, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (589, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (592, 3, parse("movq %rax,%rsi")),
  (595, 3, parse("cmpq %r10,%r9")),
  (598, 6, parse("jb indices_sort_insertion_u133")),
  (604, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-561)))))]),
  (609, 4, parse("addq $0x8,%rsp")),
  (613, 1, parse("popq %rbx")),
  (614, 2, parse("popq %r12")),
  (616, 2, parse("popq %r13")),
  (618, 2, parse("popq %r14")),
  (620, 2, parse("popq %r15")),
  (622, 1, parse("popq %rbp")),
  (623, 1, parse("retq "))]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1 ++
  programChunk2

theorem program_length : program.length = 178 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 50 := by rfl
  simp only [program, List.length_append, h0, h1, h2]

def labels : List (String × Nat) := [
  ("indices_sort_insertion_u33", 33),
  ("indices_sort_insertion_u48", 48),
  ("indices_sort_insertion_u55", 55),
  ("indices_sort_insertion_u128", 128),
  ("indices_sort_insertion_u133", 133),
  ("indices_sort_insertion_u176", 176),
  ("indices_sort_insertion_u208", 208),
  ("indices_sort_insertion_u228", 228),
  ("indices_sort_insertion_u240", 240),
  ("indices_sort_insertion_u256", 256),
  ("indices_sort_insertion_u288", 288),
  ("indices_sort_insertion_u336", 336),
  ("indices_sort_insertion_u352", 352),
  ("indices_sort_insertion_u384", 384),
  ("indices_sort_insertion_u416", 416),
  ("indices_sort_insertion_u463", 463),
  ("indices_sort_insertion_u480", 480),
  ("indices_sort_insertion_u544", 544),
  ("indices_sort_insertion_u592", 592),
  ("indices_sort_insertion_u609", 609)]

def natCompareOffset : Int := -112640

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

end SszX86.IndicesSortInsertion

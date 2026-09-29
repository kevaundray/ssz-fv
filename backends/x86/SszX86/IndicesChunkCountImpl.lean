module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesChunkCount
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2165376
def machineSize : Nat := 614

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 2, parse("pushq %r14")),
  (2, 1, parse("pushq %rbx")),
  (3, 4, parse("subq $0x48,%rsp")),
  (7, 3, parse("movq (%rsi),%rax")),
  (10, 4, parse("cmpq $0xc,%rax")),
  (14, 2, parse("ja indices_chunk_count_u141")),
  (16, 3, parse("movq %rdx,%rbx")),
  (19, 7, [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-67550)}))]),
  (26, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))]),
  (30, 3, parse("addq %rcx,%rax")),
  (33, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))]),
  (35, 8, parse("movq $0x1,0x8(%rdi)")),
  (43, 7, parse("movq $0x0,(%rdi)")),
  (50, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (179)))))]),
  (55, 4, parse("movq 0x8(%rsi),%rax")),
  (59, 4, parse("movq 0x10(%rsi),%rdx")),
  (63, 3, parse("movq %rax,%rsi")),
  (66, 5, parse("movl $0x8,%ecx")),
  (71, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (392)))))]),
  (76, 4, parse("movq 0x8(%rsi),%rax")),
  (80, 4, parse("movq 0x10(%rsi),%rdx")),
  (84, 3, parse("movq %rax,%rsi")),
  (87, 5, parse("movl $0x5,%ecx")),
  (92, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (371)))))]),
  (97, 4, parse("movq 0x18(%rsi),%rax")),
  (101, 3, parse("movq (%rax),%rcx")),
  (104, 4, parse("cmpq $0x1,%rcx")),
  (108, 6, parse("je indices_chunk_count_u249")),
  (114, 3, parse("testq %rcx,%rcx")),
  (117, 6, parse("jne indices_chunk_count_u304")),
  (123, 6, parse("movl $0x1,%r8d")),
  (129, 2, parse("xorl %ecx,%ecx")),
  (131, 5, parse("movl $0x1,%eax")),
  (136, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (200)))))]),
  (141, 7, parse("movq $0x1,(%rdi)")),
  (148, 8, parse("movq $0x0,0x8(%rdi)")),
  (156, 8, parse("movq $0x0,0x10(%rdi)")),
  (164, 8, parse("movq $0x0,0x18(%rdi)")),
  (172, 8, parse("movq $0x0,0x20(%rdi)")),
  (180, 8, parse("movq $0x0,0x28(%rdi)")),
  (188, 8, parse("movq $0x0,0x30(%rdi)")),
  (196, 8, parse("movq $0x0,0x38(%rdi)")),
  (204, 7, parse("movl $0x37,0x40(%rdi)")),
  (211, 4, parse("addq $0x48,%rsp")),
  (215, 1, parse("popq %rbx")),
  (216, 2, parse("popq %r14")),
  (218, 1, parse("retq ")),
  (219, 4, parse("movq 0x10(%rsi),%rax")),
  (223, 7, parse("movq $0x0,(%rdi)")),
  (230, 4, parse("movq %rax,0x8(%rdi)")),
  (234, 7, parse("movl $0x0,0x40(%rdi)")),
  (241, 4, parse("addq $0x48,%rsp")),
  (245, 1, parse("popq %rbx")),
  (246, 2, parse("popq %r14")),
  (248, 1, parse("retq ")),
  (249, 4, parse("movq 0x8(%rax),%rcx")),
  (253, 4, parse("movq 0x10(%rax),%r8")),
  (257, 3, parse("testq %rcx,%rcx")),
  (260, 2, parse("je indices_chunk_count_u319")),
  (262, 4, parse("leaq 0x1(%r8),%rax")),
  (266, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (272, 4, parse("cmpq $0x1,%rax")),
  (276, 2, parse("je indices_chunk_count_u326")),
  (278, 4, parse("leaq -0x1(%rax),%rdx"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (282, 6, parse("cmpq $0x0,-0x10(%rcx,%rax,8)")),
  (288, 3, parse("movq %rdx,%rax")),
  (291, 2, parse("je indices_chunk_count_u272")),
  (293, 4, parse("cmpq $0x1,%rdx")),
  (297, 2, parse("je indices_chunk_count_u331")),
  (299, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (179)))))]),
  (304, 6, parse("movl $0x20,%r8d")),
  (310, 2, parse("xorl %ecx,%ecx")),
  (312, 5, parse("movl $0x20,%eax")),
  (317, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (22)))))]),
  (319, 2, parse("xorl %ecx,%ecx")),
  (321, 3, parse("movq %r8,%rax")),
  (324, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (15)))))]),
  (326, 3, parse("testq %r8,%r8")),
  (329, 2, parse("je indices_chunk_count_u336")),
  (331, 3, parse("movq (%rcx),%rax")),
  (334, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (5)))))]),
  (336, 3, parse("xorl %r8d,%r8d")),
  (339, 2, parse("xorl %eax,%eax")),
  (341, 4, parse("cmpq $0x20,%rax")),
  (345, 6, parse("ja indices_chunk_count_u483")),
  (351, 4, parse("leaq -0x1(%rax),%rdx")),
  (355, 3, parse("movq %rax,%r9")),
  (358, 3, parse("xorq %rdx,%r9")),
  (361, 3, parse("cmpq %rdx,%r9")),
  (364, 2, parse("jbe indices_chunk_count_u483")),
  (366, 5, parse("movl $0x40,%edx")),
  (371, 5, parse("leaq -0x10(%rsp),%rsp")),
  (376, 4, parse("movq %r11,(%rsp)")),
  (380, 5, parse("movq %r10,0x8(%rsp)")),
  (385, 3, parse("movq %rax,%r11")),
  (388, 3, parse("testq %r11,%r11")),
  (391, 2, parse("je indices_chunk_count_u425")),
  (393, 7, parse("movq $0x0,%r10")),
  (400, 7, parse("testq $0x1,%r11")),
  (407, 2, parse("jne indices_chunk_count_u417")),
  (409, 3, parse("shrq $1,%r11")),
  (412, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (415, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-17)))))]),
  (417, 3, parse("movq %r10,%rdx")),
  (420, 3, parse("testq %r10,%r10")),
  (423, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (11)))))]),
  (425, 7, parse("movq $0x40,%rdx")),
  (432, 4, parse("cmpq $0x1,%r11")),
  (436, 4, parse("movq (%rsp),%r11")),
  (440, 5, parse("movq 0x8(%rsp),%r10")),
  (445, 5, parse("leaq 0x10(%rsp),%rsp")),
  (450, 5, parse("movl $0x5,%ecx")),
  (455, 2, parse("subl %edx,%ecx")),
  (457, 4, parse("movq 0x8(%rsi),%rax")),
  (461, 4, parse("movq 0x10(%rsi),%rdx")),
  (465, 3, parse("movq %rax,%rsi")),
  (468, 3, parse("movq %rbx,%r8")),
  (471, 4, parse("addq $0x48,%rsp")),
  (475, 1, parse("popq %rbx")),
  (476, 2, parse("popq %r14")),
  (478, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1597)))))]),
  (483, 3, parse("movq %rdi,%r14")),
  (486, 4, parse("movq 0x8(%rsi),%rax")),
  (490, 4, parse("movq 0x10(%rsi),%rdx")),
  (494, 3, parse("movq %rsp,%rdi")),
  (497, 3, parse("movq %rax,%rsi")),
  (500, 3, parse("movq %rbx,%r9")),
  (503, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-13148)))))])]

def programChunk2 : List (Nat × Nat × Program) := [
  (508, 4, parse("movl 0x40(%rsp),%eax")),
  (512, 4, parse("movq (%rsp),%rsi")),
  (516, 5, parse("movq 0x8(%rsp),%rdx")),
  (521, 2, parse("testl %eax,%eax")),
  (523, 2, parse("je indices_chunk_count_u606")),
  (525, 5, parse("movq 0x38(%rsp),%rcx")),
  (530, 4, parse("movq %rcx,0x38(%r14)")),
  (534, 5, parse("movq 0x30(%rsp),%rcx")),
  (539, 4, parse("movq %rcx,0x30(%r14)")),
  (543, 5, parse("movq 0x28(%rsp),%rcx")),
  (548, 4, parse("movq %rcx,0x28(%r14)")),
  (552, 5, parse("movq 0x20(%rsp),%rcx")),
  (557, 4, parse("movq %rcx,0x20(%r14)")),
  (561, 5, parse("movq 0x10(%rsp),%rcx")),
  (566, 5, parse("movq 0x18(%rsp),%rdi")),
  (571, 4, parse("movq %rdi,0x18(%r14)")),
  (575, 4, parse("movq %rcx,0x10(%r14)")),
  (579, 4, parse("movl 0x44(%rsp),%ecx")),
  (583, 3, parse("movq %rsi,(%r14)")),
  (586, 4, parse("movq %rdx,0x8(%r14)")),
  (590, 4, parse("movl %eax,0x40(%r14)")),
  (594, 4, parse("movl %ecx,0x44(%r14)")),
  (598, 4, parse("addq $0x48,%rsp")),
  (602, 1, parse("popq %rbx")),
  (603, 2, parse("popq %r14")),
  (605, 1, parse("retq ")),
  (606, 3, parse("movq %r14,%rdi")),
  (609, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-527)))))])]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1 ++
  programChunk2

theorem program_length : program.length = 156 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 28 := by rfl
  simp only [program, List.length_append, h0, h1, h2]

def labels : List (String × Nat) := [
  ("indices_chunk_count_u141", 141),
  ("indices_chunk_count_u249", 249),
  ("indices_chunk_count_u272", 272),
  ("indices_chunk_count_u304", 304),
  ("indices_chunk_count_u319", 319),
  ("indices_chunk_count_u326", 326),
  ("indices_chunk_count_u331", 331),
  ("indices_chunk_count_u336", 336),
  ("indices_chunk_count_u417", 417),
  ("indices_chunk_count_u425", 425),
  ("indices_chunk_count_u483", 483),
  ("indices_chunk_count_u606", 606)]

def indicesCeilShiftOffset : Int := 2080
def natMulOffset : Int := -12640

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

end SszX86.IndicesChunkCount

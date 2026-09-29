module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesElementType
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2167040
def machineSize : Nat := 415

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 4, parse("cmpq $0x0,(%rdx)")),
  (4, 3, parse("movq (%rsi),%rax")),
  (7, 2, parse("je indices_element_type_u35")),
  (9, 4, parse("addq $0xfffffffffffffffe,%rax")),
  (13, 4, parse("cmpq $0x7,%rax")),
  (17, 2, parse("ja indices_element_type_u135")),
  (19, 7, [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-69162)}))]),
  (26, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))]),
  (30, 3, parse("addq %rcx,%rax")),
  (33, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))]),
  (35, 4, parse("addq $0xfffffffffffffffe,%rax")),
  (39, 4, parse("cmpq $0x9,%rax")),
  (43, 2, parse("ja indices_element_type_u135")),
  (45, 7, [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-69156)}))]),
  (52, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))]),
  (56, 3, parse("addq %rcx,%rax")),
  (59, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))]),
  (61, 7, parse("movq $0x0,(%rdi)")),
  (68, 7, parse("movl $0x0,0x40(%rdi)")),
  (75, 1, parse("retq ")),
  (76, 5, parse("movl $0x18,%eax")),
  (81, 4, parse("movq (%rsi,%rax,1),%rax")),
  (85, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (207)))))]),
  (90, 7, parse("movq $0x1,(%rdi)")),
  (97, 8, parse("movq $0x0,0x8(%rdi)")),
  (105, 8, parse("movq $0x1,0x10(%rdi)")),
  (113, 7, parse("movl $0x0,0x40(%rdi)")),
  (120, 1, parse("retq ")),
  (121, 5, parse("movl $0x8,%eax")),
  (126, 4, parse("movq (%rsi,%rax,1),%rax")),
  (130, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (162)))))]),
  (135, 7, parse("movq $0x1,(%rdi)")),
  (142, 8, parse("movq $0x0,0x8(%rdi)")),
  (150, 8, parse("movq $0x0,0x10(%rdi)")),
  (158, 8, parse("movq $0x0,0x18(%rdi)")),
  (166, 8, parse("movq $0x0,0x20(%rdi)")),
  (174, 8, parse("movq $0x0,0x28(%rdi)")),
  (182, 8, parse("movq $0x0,0x30(%rdi)")),
  (190, 8, parse("movq $0x0,0x38(%rdi)")),
  (198, 7, parse("movl $0x38,0x40(%rdi)")),
  (205, 1, parse("retq ")),
  (206, 5, parse("movl $0x18,%eax")),
  (211, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (5)))))]),
  (213, 5, parse("movl $0x8,%eax")),
  (218, 4, parse("movq 0x8(%rdx),%r8")),
  (222, 4, parse("movq 0x10(%rdx),%rcx")),
  (226, 3, parse("movq %rcx,%rdx")),
  (229, 3, parse("testq %r8,%r8")),
  (232, 2, parse("je indices_element_type_u277")),
  (234, 4, parse("leaq 0x1(%rcx),%rdx")),
  (238, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (240, 4, parse("cmpq $0x1,%rdx")),
  (244, 2, parse("je indices_element_type_u269")),
  (246, 4, parse("leaq -0x1(%rdx),%r9")),
  (250, 6, parse("cmpq $0x0,-0x10(%r8,%rdx,8)")),
  (256, 3, parse("movq %r9,%rdx")),
  (259, 2, parse("je indices_element_type_u240")),
  (261, 4, parse("cmpq $0x1,%r9")),
  (265, 2, parse("je indices_element_type_u274")),
  (267, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (83)))))]),
  (269, 3, parse("testq %rcx,%rcx")),
  (272, 2, parse("je indices_element_type_u343")),
  (274, 3, parse("movq (%r8),%rdx")),
  (277, 5, parse("cmpq 0x8(%rsi,%rax,1),%rdx"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (282, 2, parse("jae indices_element_type_u352")),
  (284, 4, parse("movq (%rsi,%rax,1),%rax")),
  (288, 4, parse("leaq (%rdx,%rdx,2),%rcx")),
  (292, 5, parse("movq 0x10(%rax,%rcx,8),%rax")),
  (297, 4, parse("movq 0x20(%rax),%rcx")),
  (301, 4, parse("movq %rcx,0x20(%rdi)")),
  (305, 4, parse("movq 0x18(%rax),%rcx")),
  (309, 4, parse("movq %rcx,0x18(%rdi)")),
  (313, 4, parse("movq 0x10(%rax),%rcx")),
  (317, 4, parse("movq %rcx,0x10(%rdi)")),
  (321, 3, parse("movq (%rax),%rcx")),
  (324, 4, parse("movq 0x8(%rax),%rax")),
  (328, 4, parse("movq %rax,0x8(%rdi)")),
  (332, 3, parse("movq %rcx,(%rdi)")),
  (335, 7, parse("movl $0x0,0x40(%rdi)")),
  (342, 1, parse("retq ")),
  (343, 2, parse("xorl %edx,%edx")),
  (345, 5, parse("cmpq 0x8(%rsi,%rax,1),%rdx")),
  (350, 2, parse("jb indices_element_type_u284")),
  (352, 7, parse("movq $0x1,(%rdi)")),
  (359, 8, parse("movq $0x0,0x8(%rdi)")),
  (367, 4, parse("movq %r8,0x10(%rdi)")),
  (371, 4, parse("movq %rcx,0x18(%rdi)")),
  (375, 8, parse("movq $0x0,0x20(%rdi)")),
  (383, 8, parse("movq $0x0,0x28(%rdi)")),
  (391, 8, parse("movq $0x0,0x30(%rdi)")),
  (399, 8, parse("movq $0x0,0x38(%rdi)")),
  (407, 7, parse("movl $0x39,0x40(%rdi)")),
  (414, 1, parse("retq "))]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1

theorem program_length : program.length = 93 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 29 := by rfl
  simp only [program, List.length_append, h0, h1]

def labels : List (String × Nat) := [
  ("indices_element_type_u35", 35),
  ("indices_element_type_u135", 135),
  ("indices_element_type_u240", 240),
  ("indices_element_type_u269", 269),
  ("indices_element_type_u274", 274),
  ("indices_element_type_u277", 277),
  ("indices_element_type_u284", 284),
  ("indices_element_type_u343", 343),
  ("indices_element_type_u352", 352)]


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

end SszX86.IndicesElementType

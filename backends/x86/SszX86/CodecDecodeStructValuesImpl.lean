module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecDecodeStructValues
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2219824
def machineSize : Nat := 855

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 7, parse("subq $0x128,%rsp")),
  (17, 3, parse("testq %rdx,%rdx")),
  (20, 6, parse("je codec_decode_struct_values_u649")),
  (26, 3, parse("movq %rdx,%rax")),
  (29, 4, parse("shlq $0x4,%rax")),
  (33, 4, parse("leaq (%rax,%rax,2),%rax")),
  (37, 3, parse("testq %rax,%rax")),
  (40, 6, parse("jl codec_decode_struct_values_u514")),
  (46, 3, parse("movq %rsi,%r15")),
  (49, 3, parse("movq (%rsi),%r10")),
  (52, 4, parse("movq 0x10(%rsi),%rsi")),
  (56, 3, parse("movq %rsi,%r8")),
  (59, 3, parse("addq %r10,%r8")),
  (62, 6, parse("jb codec_decode_struct_values_u514")),
  (68, 4, parse("cmpq $0xfffffffffffffff0,%r8")),
  (72, 6, parse("ja codec_decode_struct_values_u514")),
  (78, 4, parse("leaq 0xf(%r8),%r14")),
  (82, 4, parse("andq $0xfffffffffffffff0,%r14")),
  (86, 3, parse("movq %r14,%r9")),
  (89, 3, parse("subq %r8,%r9")),
  (92, 3, parse("addq %rsi,%r9")),
  (95, 6, parse("jb codec_decode_struct_values_u514")),
  (101, 3, parse("addq %r9,%rax")),
  (104, 6, parse("jb codec_decode_struct_values_u514")),
  (110, 4, parse("cmpq 0x8(%r15),%rax")),
  (114, 6, parse("ja codec_decode_struct_values_u514")),
  (120, 4, parse("movq %rdi,(%rsp)")),
  (124, 4, parse("movq %rax,0x10(%r15)")),
  (128, 3, parse("addq %r9,%r10")),
  (131, 5, parse("movq %r10,0x50(%rsp)")),
  (136, 3, parse("movq (%rcx),%r13")),
  (139, 4, parse("movq 0x8(%rcx),%rax")),
  (143, 5, parse("movq %rax,0x10(%rsp)")),
  (148, 4, parse("movq 0x18(%rcx),%rax")),
  (152, 5, parse("movq %rax,0x8(%rsp)")),
  (157, 4, parse("movq 0x28(%rcx),%rax")),
  (161, 5, parse("movq %rax,0x18(%rsp)")),
  (166, 4, parse("movq 0x20(%rcx),%rax")),
  (170, 5, parse("movq %rax,0x70(%rsp)")),
  (175, 4, parse("movq 0x10(%rcx),%rax")),
  (179, 5, parse("movq %rax,0x68(%rsp)")),
  (184, 8, parse("leaq 0xb8(%rsp),%r12")),
  (192, 4, parse("addq $0x8,%r14")),
  (196, 5, parse("movq %rdx,0x58(%rsp)")),
  (201, 8, [.instr (.regular .W64 .W64 (.lea (.low .rax .W64) { base := none, idx := some ⟨.rdx, .W64⟩, disp := .int64 (0) }))]),
  (209, 4, parse("leaq (%rax,%rax,2),%rax")),
  (213, 5, parse("movq %rax,0x60(%rsp)")),
  (218, 4, parse("addq $0x20,%r13")),
  (222, 2, parse("xorl %ebp,%ebp")),
  (224, 2, parse("xorl %ebx,%ebx")),
  (226, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (236, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (240, 5, parse("cmpq %rbx,0x10(%rsp)")),
  (245, 6, parse("je codec_decode_struct_values_u829")),
  (251, 5, parse("cmpq %rbx,0x8(%rsp)")),
  (256, 6, parse("je codec_decode_struct_values_u842")),
  (262, 4, parse("movq -0x8(%r13),%rdx")),
  (266, 4, parse("movq 0x0(%r13),%rsi"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (270, 3, parse("movq %rsi,%rcx")),
  (273, 3, parse("subq %rdx,%rcx")),
  (276, 6, parse("jb codec_decode_struct_values_u816")),
  (282, 5, parse("cmpq 0x18(%rsp),%rsi")),
  (287, 6, parse("ja codec_decode_struct_values_u816")),
  (293, 5, parse("movq 0x68(%rsp),%rax")),
  (298, 5, parse("movq 0x10(%rax,%rbp,1),%rsi")),
  (303, 5, parse("addq 0x70(%rsp),%rdx")),
  (308, 8, parse("leaq 0xa0(%rsp),%rdi")),
  (316, 3, parse("movq %r15,%r8")),
  (319, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-15428)))))]),
  (324, 8, parse("cmpb $0x0,0xa0(%rsp)")),
  (332, 6, parse("jne codec_decode_struct_values_u686")),
  (338, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rbx .W64))))]),
  (341, 8, parse("movq 0xb0(%rsp),%rax")),
  (349, 4, parse("movq (%r12),%rcx")),
  (353, 5, parse("movq 0x8(%r12),%rdx")),
  (358, 5, parse("movq 0x10(%r12),%rsi")),
  (363, 5, parse("movq 0x18(%r12),%rdi")),
  (368, 5, parse("movq 0x20(%r12),%r8")),
  (373, 8, parse("movq %r8,0x98(%rsp)")),
  (381, 8, parse("movq %rdi,0x90(%rsp)")),
  (389, 8, parse("movq %rsi,0x88(%rsp)")),
  (397, 8, parse("movq %rdx,0x80(%rsp)")),
  (405, 5, parse("movq %rcx,0x78(%rsp)")),
  (410, 5, parse("movq %rax,-0x8(%r14,%rbp,2)")),
  (415, 5, parse("movq 0x78(%rsp),%rax")),
  (420, 8, parse("movq 0x80(%rsp),%rcx")),
  (428, 4, parse("movq %rax,(%r14,%rbp,2)")),
  (432, 5, parse("movq %rcx,0x8(%r14,%rbp,2)")),
  (437, 8, parse("movq 0x88(%rsp),%rax")),
  (445, 5, parse("movq %rax,0x10(%r14,%rbp,2)")),
  (450, 8, parse("movq 0x90(%rsp),%rax")),
  (458, 5, parse("movq %rax,0x18(%r14,%rbp,2)")),
  (463, 8, parse("movq 0x98(%rsp),%rax")),
  (471, 5, parse("movq %rax,0x20(%r14,%rbp,2)")),
  (476, 4, parse("addq $0x18,%rbp")),
  (480, 4, parse("addq $0x28,%r13")),
  (484, 5, parse("cmpq %rbp,0x60(%rsp)")),
  (489, 6, parse("jne codec_decode_struct_values_u240")),
  (495, 4, parse("movq (%rsp),%rdi")),
  (499, 5, parse("movq 0x58(%rsp),%rdx")),
  (504, 5, parse("movq 0x50(%rsp),%rbx")),
  (509, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (140)))))]),
  (514, 9, parse("movq $0x0,0x48(%rsp)")),
  (523, 9, parse("movq $0x0,0x40(%rsp)")),
  (532, 9, parse("movq $0x0,0x38(%rsp)")),
  (541, 9, parse("movq $0x0,0x30(%rsp)")),
  (550, 9, parse("movq $0x0,0x28(%rsp)")),
  (559, 9, parse("movq $0x0,0x20(%rsp)")),
  (568, 5, parse("movl $0x8000,%eax")),
  (573, 5, parse("movl $0x1,%ebx")),
  (578, 2, parse("xorl %edx,%edx")),
  (580, 5, parse("movq 0x48(%rsp),%rsi")),
  (585, 4, parse("movq %rsi,0x38(%rdi)")),
  (589, 5, parse("movq 0x40(%rsp),%rsi")),
  (594, 4, parse("movq %rsi,0x30(%rdi)")),
  (598, 5, parse("movq 0x38(%rsp),%rsi")),
  (603, 4, parse("movq %rsi,0x28(%rdi)")),
  (607, 5, parse("movq 0x30(%rsp),%rsi")),
  (612, 4, parse("movq %rsi,0x20(%rdi)")),
  (616, 5, parse("movq 0x20(%rsp),%r8")),
  (621, 5, parse("movq 0x28(%rsp),%rsi")),
  (626, 4, parse("movq %rsi,0x18(%rdi)"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (630, 4, parse("movq %r8,0x10(%rdi)")),
  (634, 3, parse("movq %rbx,(%rdi)")),
  (637, 4, parse("movq %rdx,0x8(%rdi)")),
  (641, 3, parse("movl %eax,0x40(%rdi)")),
  (644, 3, parse("movl %ecx,0x44(%rdi)")),
  (647, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (19)))))]),
  (649, 5, parse("movl $0x10,%ebx")),
  (654, 3, parse("movq %rbx,(%rdi)")),
  (657, 4, parse("movq %rdx,0x8(%rdi)")),
  (661, 7, parse("movl $0x0,0x40(%rdi)")),
  (668, 7, parse("addq $0x128,%rsp")),
  (675, 1, parse("popq %rbx")),
  (676, 2, parse("popq %r12")),
  (678, 2, parse("popq %r13")),
  (680, 2, parse("popq %r14")),
  (682, 2, parse("popq %r15")),
  (684, 1, parse("popq %rbp")),
  (685, 1, parse("retq ")),
  (686, 8, parse("movq 0xa8(%rsp),%rbx")),
  (694, 8, parse("movq 0xb0(%rsp),%rdx")),
  (702, 4, parse("movq (%r12),%r11")),
  (706, 5, parse("movq 0x8(%r12),%rsi")),
  (711, 8, parse("movq %r11,0xf8(%rsp)")),
  (719, 8, parse("movq %rsi,0x100(%rsp)")),
  (727, 5, parse("movq 0x10(%r12),%rdi")),
  (732, 8, parse("movq %rdi,0x108(%rsp)")),
  (740, 5, parse("movq 0x18(%r12),%r8")),
  (745, 5, parse("movq 0x20(%r12),%r9")),
  (750, 5, parse("movq 0x28(%r12),%r10")),
  (755, 7, parse("movl 0xe8(%rsp),%eax")),
  (762, 7, parse("movl 0xec(%rsp),%ecx")),
  (769, 5, parse("movq %r10,0x48(%rsp)")),
  (774, 5, parse("movq %r9,0x40(%rsp)")),
  (779, 5, parse("movq %r8,0x38(%rsp)")),
  (784, 5, parse("movq %rdi,0x30(%rsp)")),
  (789, 5, parse("movq %rsi,0x28(%rsp)")),
  (794, 5, parse("movq %r11,0x20(%rsp)")),
  (799, 2, parse("testl %eax,%eax")),
  (801, 4, parse("movq (%rsp),%rdi")),
  (805, 6, parse("jne codec_decode_struct_values_u580")),
  (811, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-162)))))]),
  (816, 3, parse("movq %rdx,%rdi")),
  (819, 5, parse("movq 0x18(%rsp),%rdx")),
  (824, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-88717)))))]),
  (829, 5, parse("movq 0x10(%rsp),%rdi")),
  (834, 3, parse("movq %rdi,%rsi")),
  (837, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-88678)))))]),
  (842, 5, parse("movq 0x8(%rsp),%rdi")),
  (847, 3, parse("movq %rdi,%rsi")),
  (850, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-88691)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2

theorem program_length : program.length = 178 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 50 := by rfl
  simp only [program, List.length_append, h0, h1, h2]

def labels : List (String × Nat) := [
  ("codec_decode_struct_values_u240", 240),
  ("codec_decode_struct_values_u514", 514),
  ("codec_decode_struct_values_u580", 580),
  ("codec_decode_struct_values_u649", 649),
  ("codec_decode_struct_values_u686", 686),
  ("codec_decode_struct_values_u816", 816),
  ("codec_decode_struct_values_u829", 829),
  ("codec_decode_struct_values_u842", 842)]

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

def deserializeOffset : Int := -15104

def sliceIndexFailOffset : Int := -87888

def panicBoundsCheckOffset : Int := -87836

end SszX86.CodecDecodeStructValues

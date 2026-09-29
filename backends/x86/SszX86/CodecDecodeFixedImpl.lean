module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecDecodeFixed
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2215312
def machineSize : Nat := 731

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 7, parse("subq $0x108,%rsp")),
  (17, 4, parse("movq %r9,(%rsp)")),
  (21, 5, parse("movq %r8,0x50(%rsp)")),
  (26, 3, parse("movq %rdx,%rbp")),
  (29, 5, parse("movq %rsi,0x48(%rsp)")),
  (34, 3, parse("movq %rdi,%rbx")),
  (37, 3, parse("testq %rdx,%rdx")),
  (40, 6, parse("je codec_decode_fixed_u219")),
  (46, 3, parse("movq %rcx,%r14")),
  (49, 5, parse("movl $0x30,%ecx")),
  (54, 3, parse("movq %rbp,%rax")),
  (57, 3, parse("mulq %rcx")),
  (60, 3, parse("setb %cl")),
  (63, 3, parse("testq %rax,%rax")),
  (66, 3, parse("setl %dl")),
  (69, 2, parse("orb %cl,%dl")),
  (71, 6, parse("je codec_decode_fixed_u260")),
  (77, 9, parse("movq $0x0,0x30(%rsp)")),
  (86, 9, parse("movq $0x0,0x28(%rsp)")),
  (95, 9, parse("movq $0x0,0x20(%rsp)")),
  (104, 9, parse("movq $0x0,0x18(%rsp)")),
  (113, 9, parse("movq $0x0,0x10(%rsp)")),
  (122, 9, parse("movq $0x0,0x8(%rsp)")),
  (131, 5, parse("movl $0x8000,%eax")),
  (136, 6, parse("movl $0x1,%r14d")),
  (142, 2, parse("xorl %ebp,%ebp")),
  (144, 5, parse("movq 0x30(%rsp),%rdx")),
  (149, 4, parse("movq %rdx,0x40(%rbx)")),
  (153, 5, parse("movq 0x28(%rsp),%rdx")),
  (158, 4, parse("movq %rdx,0x38(%rbx)")),
  (162, 5, parse("movq 0x20(%rsp),%rdx")),
  (167, 4, parse("movq %rdx,0x30(%rbx)")),
  (171, 5, parse("movq 0x18(%rsp),%rdx")),
  (176, 4, parse("movq %rdx,0x28(%rbx)")),
  (180, 5, parse("movq 0x8(%rsp),%rdx")),
  (185, 5, parse("movq 0x10(%rsp),%rsi")),
  (190, 4, parse("movq %rsi,0x20(%rbx)")),
  (194, 4, parse("movq %rdx,0x18(%rbx)")),
  (198, 4, parse("movq %r14,0x8(%rbx)")),
  (202, 4, parse("movq %rbp,0x10(%rbx)")),
  (206, 3, parse("movl %eax,0x48(%rbx)")),
  (209, 3, parse("movl %ecx,0x4c(%rbx)")),
  (212, 5, parse("movl $0x1,%eax")),
  (217, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (20)))))]),
  (219, 6, parse("movl $0x10,%r14d")),
  (225, 4, parse("movb $0x4,0x10(%rbx)")),
  (229, 4, parse("movq %r14,0x18(%rbx)")),
  (233, 4, parse("movq %rbp,0x20(%rbx)")),
  (237, 2, parse("xorl %eax,%eax")),
  (239, 3, parse("movq %rax,(%rbx)")),
  (242, 7, parse("addq $0x108,%rsp")),
  (249, 1, parse("popq %rbx")),
  (250, 2, parse("popq %r12")),
  (252, 2, parse("popq %r13")),
  (254, 2, parse("popq %r14")),
  (256, 2, parse("popq %r15")),
  (258, 1, parse("popq %rbp")),
  (259, 1, parse("retq "))]

def programChunk1 : List (Nat × Nat × Program) := [
  (260, 8, parse("movq 0x140(%rsp),%rcx")),
  (268, 3, parse("movq (%rcx),%rdi")),
  (271, 4, parse("movq 0x10(%rcx),%rdx")),
  (275, 3, parse("movq %rdx,%rsi")),
  (278, 3, parse("addq %rdi,%rsi")),
  (281, 6, parse("jb codec_decode_fixed_u77")),
  (287, 4, parse("cmpq $0xfffffffffffffff0,%rsi")),
  (291, 6, parse("ja codec_decode_fixed_u77")),
  (297, 4, parse("leaq 0xf(%rsi),%r15")),
  (301, 4, parse("andq $0xfffffffffffffff0,%r15")),
  (305, 3, parse("movq %r15,%rcx")),
  (308, 3, parse("subq %rsi,%rcx")),
  (311, 3, parse("addq %rdx,%rcx")),
  (314, 6, parse("jb codec_decode_fixed_u77")),
  (320, 3, parse("addq %rcx,%rax")),
  (323, 6, parse("jb codec_decode_fixed_u77")),
  (329, 8, parse("movq 0x140(%rsp),%rdx")),
  (337, 4, parse("cmpq 0x8(%rdx),%rax")),
  (341, 6, parse("ja codec_decode_fixed_u77")),
  (347, 4, parse("movq %rax,0x10(%rdx)")),
  (351, 3, parse("addq %rcx,%rdi")),
  (354, 5, parse("movq %rdi,0x38(%rsp)")),
  (359, 8, parse("leaq 0x98(%rsp),%r12")),
  (367, 4, parse("addq $0x8,%r15")),
  (371, 2, parse("xorl %edx,%edx")),
  (373, 5, parse("movq %rbp,0x40(%rsp)")),
  (378, 6, [.instr (.regular .W64 .W64 (.nop 6))]),
  (384, 3, parse("movq %r14,%r13")),
  (387, 3, parse("addq %rdx,%r13")),
  (390, 6, parse("jb codec_decode_fixed_u716")),
  (396, 4, parse("cmpq (%rsp),%r13")),
  (400, 6, parse("ja codec_decode_fixed_u716")),
  (406, 5, parse("addq 0x50(%rsp),%rdx")),
  (411, 8, parse("leaq 0x80(%rsp),%rdi")),
  (419, 5, parse("movq 0x48(%rsp),%rsi")),
  (424, 3, parse("movq %r14,%rcx")),
  (427, 8, parse("movq 0x140(%rsp),%r8")),
  (435, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-11032)))))]),
  (440, 8, parse("cmpb $0x0,0x80(%rsp)")),
  (448, 6, parse("jne codec_decode_fixed_u590")),
  (454, 8, parse("movq 0x90(%rsp),%rax")),
  (462, 4, parse("movq (%r12),%rcx")),
  (466, 5, parse("movq 0x8(%r12),%rdx")),
  (471, 5, parse("movq 0x10(%r12),%rsi")),
  (476, 5, parse("movq 0x18(%r12),%rdi")),
  (481, 5, parse("movq 0x20(%r12),%r8")),
  (486, 5, parse("movq %r8,0x78(%rsp)")),
  (491, 5, parse("movq %rdi,0x70(%rsp)")),
  (496, 5, parse("movq %rsi,0x68(%rsp)")),
  (501, 5, parse("movq %rdx,0x60(%rsp)")),
  (506, 5, parse("movq %rcx,0x58(%rsp)")),
  (511, 4, parse("movq %rax,-0x8(%r15)")),
  (515, 5, parse("movq 0x58(%rsp),%rax")),
  (520, 5, parse("movq 0x60(%rsp),%rcx")),
  (525, 3, parse("movq %rax,(%r15)")),
  (528, 4, parse("movq %rcx,0x8(%r15)")),
  (532, 5, parse("movq 0x68(%rsp),%rax")),
  (537, 4, parse("movq %rax,0x10(%r15)")),
  (541, 5, parse("movq 0x70(%rsp),%rax")),
  (546, 4, parse("movq %rax,0x18(%r15)")),
  (550, 5, parse("movq 0x78(%rsp),%rax")),
  (555, 4, parse("movq %rax,0x20(%r15)")),
  (559, 4, parse("addq $0x30,%r15")),
  (563, 3, parse("movq %r13,%rdx"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (566, 3, parse("decq %rbp")),
  (569, 6, parse("jne codec_decode_fixed_u384")),
  (575, 5, parse("movq 0x40(%rsp),%rbp")),
  (580, 5, parse("movq 0x38(%rsp),%r14")),
  (585, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-365)))))]),
  (590, 8, parse("movq 0x88(%rsp),%r14")),
  (598, 8, parse("movq 0x90(%rsp),%rbp")),
  (606, 4, parse("movq (%r12),%rdx")),
  (610, 5, parse("movq 0x8(%r12),%rsi")),
  (615, 8, parse("movq %rdx,0xd8(%rsp)")),
  (623, 8, parse("movq %rsi,0xe0(%rsp)")),
  (631, 5, parse("movq 0x10(%r12),%rdi")),
  (636, 8, parse("movq %rdi,0xe8(%rsp)")),
  (644, 5, parse("movq 0x18(%r12),%r8")),
  (649, 5, parse("movq 0x20(%r12),%r9")),
  (654, 5, parse("movq 0x28(%r12),%r10")),
  (659, 7, parse("movl 0xc8(%rsp),%eax")),
  (666, 7, parse("movl 0xcc(%rsp),%ecx")),
  (673, 5, parse("movq %r10,0x30(%rsp)")),
  (678, 5, parse("movq %r9,0x28(%rsp)")),
  (683, 5, parse("movq %r8,0x20(%rsp)")),
  (688, 5, parse("movq %rdi,0x18(%rsp)")),
  (693, 5, parse("movq %rsi,0x10(%rsp)")),
  (698, 5, parse("movq %rdx,0x8(%rsp)")),
  (703, 2, parse("testl %eax,%eax")),
  (705, 6, parse("jne codec_decode_fixed_u144")),
  (711, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-491)))))]),
  (716, 3, parse("movq %rdx,%rdi")),
  (719, 3, parse("movq %r13,%rsi")),
  (722, 4, parse("movq (%rsp),%rdx")),
  (726, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-84107)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2

theorem program_length : program.length = 159 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 31 := by rfl
  simp only [program, List.length_append, h0, h1, h2]

def labels : List (String × Nat) := [
  ("codec_decode_fixed_u77", 77),
  ("codec_decode_fixed_u144", 144),
  ("codec_decode_fixed_u219", 219),
  ("codec_decode_fixed_u260", 260),
  ("codec_decode_fixed_u384", 384),
  ("codec_decode_fixed_u590", 590),
  ("codec_decode_fixed_u716", 716)]

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

def deserializeOffset : Int := -10592

def sliceIndexFailOffset : Int := -83376

end SszX86.CodecDecodeFixed

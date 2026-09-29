module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecEmitParts
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2192576
def machineSize : Nat := 1080

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 7, parse("subq $0x98,%rsp")),
  (17, 5, parse("movq %r9,0x10(%rsp)")),
  (22, 3, parse("movq %rdx,%r12")),
  (25, 3, parse("testq %r8,%r8")),
  (28, 5, parse("movq %rdi,0x8(%rsp)")),
  (33, 6, parse("je codec_emit_parts_u558")),
  (39, 4, parse("movq 0x8(%r8),%r14")),
  (43, 3, parse("testq %r14,%r14")),
  (46, 6, parse("je codec_emit_parts_u558")),
  (52, 4, parse("movq 0x20(%r8),%rbp")),
  (56, 3, parse("cmpq %rcx,%r14")),
  (59, 4, parse("cmovae %rcx,%r14")),
  (63, 3, parse("testq %rcx,%rcx")),
  (66, 6, parse("je codec_emit_parts_u701")),
  (72, 3, parse("movq (%r8),%rax")),
  (75, 8, parse("movq %rax,0x88(%rsp)")),
  (83, 3, parse("movq (%rsi),%rdi")),
  (86, 4, parse("movq 0x8(%rsi),%rax")),
  (90, 5, parse("movq %rax,0x60(%rsp)")),
  (95, 4, parse("addq $0x8,%rsi")),
  (99, 8, parse("movq %rsi,0x90(%rsp)")),
  (107, 3, parse("xorl %r10d,%r10d")),
  (110, 2, parse("xorl %ebx,%ebx")),
  (112, 3, parse("movq %rbp,%r8")),
  (115, 8, parse("movq %r14,0x80(%rsp)")),
  (123, 5, parse("movq %rdi,0x78(%rsp)")),
  (128, 5, parse("movq %r12,0x70(%rsp)")),
  (133, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (37)))))]),
  (135, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (144, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .rbx .W64))))]),
  (147, 3, parse("movq %r14,%r10")),
  (150, 8, parse("movq 0x80(%rsp),%r14")),
  (158, 3, parse("cmpq %r14,%rbx")),
  (161, 5, parse("movq 0x78(%rsp),%rdi")),
  (166, 6, parse("je codec_emit_parts_u701")),
  (172, 4, parse("leaq (%rbx,%rbx,2),%r13")),
  (176, 8, parse("movq 0x90(%rsp),%rax")),
  (184, 3, parse("testq %rdi,%rdi")),
  (187, 2, parse("je codec_emit_parts_u208")),
  (189, 5, parse("cmpq 0x60(%rsp),%rbx")),
  (194, 6, parse("jae codec_emit_parts_u1067")),
  (200, 4, parse("leaq (%rdi,%r13,8),%rax")),
  (204, 4, parse("addq $0x10,%rax")),
  (208, 4, parse("leaq (%rbx,%rbx,4),%rcx")),
  (212, 8, parse("movq 0x88(%rsp),%rdx")),
  (220, 4, parse("leaq (%rdx,%rcx,8),%rcx")),
  (224, 3, parse("movq (%rax),%r15")),
  (227, 4, parse("movq 0x10(%rcx),%rax")),
  (231, 4, parse("movq 0x18(%rcx),%r9")),
  (235, 3, parse("testq %rax,%rax")),
  (238, 2, parse("je codec_emit_parts_u300")),
  (240, 4, parse("leaq 0x1(%r9),%r11")),
  (244, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (254, 2, [.instr (.regular .W64 .W64 (.nop 2))]),
  (256, 4, parse("cmpq $0x1,%r11")),
  (260, 2, parse("je codec_emit_parts_u288")),
  (262, 4, parse("leaq -0x1(%r11),%rdx")),
  (266, 6, parse("cmpq $0x0,-0x10(%rax,%r11,8)"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (272, 3, parse("movq %rdx,%r11")),
  (275, 2, parse("je codec_emit_parts_u256")),
  (277, 4, parse("cmpq $0x1,%rdx")),
  (281, 2, parse("je codec_emit_parts_u297")),
  (283, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (634)))))]),
  (288, 3, parse("testq %r9,%r9")),
  (291, 6, parse("je codec_emit_parts_u436")),
  (297, 3, parse("movq (%rax),%r9")),
  (300, 4, parse("shlq $0x4,%r13")),
  (304, 3, parse("addq %r12,%r13")),
  (307, 3, parse("testq %rdi,%rdi")),
  (310, 6, parse("je codec_emit_parts_u464")),
  (316, 3, parse("movq %r15,%rdi")),
  (319, 5, parse("movq %r8,0x68(%rsp)")),
  (324, 3, parse("movq %r10,%r14")),
  (327, 3, parse("movq %rcx,%rbp")),
  (330, 3, parse("movq %r9,%r12")),
  (333, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (750)))))]),
  (338, 3, parse("movq %r12,%r9")),
  (341, 5, parse("movq 0x70(%rsp),%r12")),
  (346, 3, parse("movq %rbp,%rcx")),
  (349, 3, parse("movq %r14,%r10")),
  (352, 5, parse("movq 0x68(%rsp),%r8")),
  (357, 2, parse("testb %al,%al")),
  (359, 2, parse("je codec_emit_parts_u464")),
  (361, 3, parse("movq %r9,%r14")),
  (364, 3, parse("addq %r10,%r14")),
  (367, 6, parse("jb codec_emit_parts_u1037")),
  (373, 8, parse("cmpq 0xd0(%rsp),%r14")),
  (381, 6, parse("ja codec_emit_parts_u1037")),
  (387, 5, parse("addq 0x10(%rsp),%r10")),
  (392, 5, parse("leaq 0x18(%rsp),%rdi")),
  (397, 3, parse("movq %r15,%rsi")),
  (400, 3, parse("movq %r13,%rdx")),
  (403, 3, parse("movq %r10,%r8")),
  (406, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-2123)))))]),
  (411, 4, parse("movl 0x58(%rsp),%eax")),
  (415, 2, parse("testl %eax,%eax")),
  (417, 6, parse("jne codec_emit_parts_u818")),
  (423, 5, parse("movq 0x68(%rsp),%r8")),
  (428, 3, parse("movq %r8,%rbp")),
  (431, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-292)))))]),
  (436, 3, parse("xorl %r9d,%r9d")),
  (439, 4, parse("shlq $0x4,%r13")),
  (443, 3, parse("addq %r12,%r13")),
  (446, 3, parse("testq %rdi,%rdi")),
  (449, 6, parse("jne codec_emit_parts_u316")),
  (455, 9, [.instr (.regular .W64 .W64 (.nop 9))]),
  (464, 4, parse("leaq 0x4(%r10),%r14")),
  (468, 8, parse("cmpq 0xd0(%rsp),%r14")),
  (476, 6, parse("ja codec_emit_parts_u1037")),
  (482, 5, parse("movq 0x10(%rsp),%rax")),
  (487, 4, parse("movl %r8d,(%rax,%r10,1)")),
  (491, 3, parse("movq %r9,%rbp")),
  (494, 3, parse("addq %r8,%rbp")),
  (497, 6, parse("jb codec_emit_parts_u1018")),
  (503, 8, parse("cmpq 0xd0(%rsp),%rbp")),
  (511, 6, parse("ja codec_emit_parts_u1018")),
  (517, 5, parse("addq 0x10(%rsp),%r8")),
  (522, 5, parse("leaq 0x18(%rsp),%rdi")),
  (527, 3, parse("movq %r15,%rsi")),
  (530, 3, parse("movq %r13,%rdx")),
  (533, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-2250)))))]),
  (538, 4, parse("movl 0x58(%rsp),%eax"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (542, 2, parse("testl %eax,%eax")),
  (544, 6, parse("jne codec_emit_parts_u818")),
  (550, 3, parse("movq %rbp,%r8")),
  (553, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-414)))))]),
  (558, 3, parse("testq %rcx,%rcx")),
  (561, 6, parse("je codec_emit_parts_u711")),
  (567, 4, parse("shlq $0x4,%rcx")),
  (571, 4, parse("leaq (%rcx,%rcx,2),%r13")),
  (575, 3, parse("movq (%rsi),%rbp")),
  (578, 4, parse("movq 0x8(%rsi),%r14")),
  (582, 3, parse("testq %rbp,%rbp")),
  (585, 6, parse("je codec_emit_parts_u715")),
  (591, 4, parse("addq $0x10,%rbp")),
  (595, 7, parse("movq $0xffffffffffffffff,%r15")),
  (602, 2, parse("xorl %ebx,%ebx")),
  (604, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (608, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r15 .W64))))]),
  (611, 3, parse("cmpq %r15,%r14")),
  (614, 6, parse("je codec_emit_parts_u1056")),
  (620, 8, parse("movq 0xd0(%rsp),%r9")),
  (628, 3, parse("subq %rbx,%r9")),
  (631, 6, parse("jb codec_emit_parts_u999")),
  (637, 4, parse("movq 0x0(%rbp),%rsi")),
  (641, 5, parse("movq 0x10(%rsp),%rax")),
  (646, 4, parse("leaq (%rax,%rbx,1),%r8")),
  (650, 5, parse("leaq 0x18(%rsp),%rdi")),
  (655, 3, parse("movq %r12,%rdx")),
  (658, 2, parse("xorl %ecx,%ecx")),
  (660, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-2377)))))]),
  (665, 4, parse("movl 0x58(%rsp),%eax")),
  (669, 2, parse("testl %eax,%eax")),
  (671, 6, parse("jne codec_emit_parts_u818")),
  (677, 4, parse("addq $0x30,%r12")),
  (681, 4, parse("addq $0xffffffffffffffd0,%r13")),
  (685, 4, parse("addq $0x18,%rbp")),
  (689, 5, parse("addq 0x18(%rsp),%rbx")),
  (694, 3, parse("testq %r13,%r13")),
  (697, 2, parse("jne codec_emit_parts_u608")),
  (699, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (100)))))]),
  (701, 5, parse("movq 0x8(%rsp),%rax")),
  (706, 3, parse("movq %rbp,(%rax)")),
  (709, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (98)))))]),
  (711, 2, parse("xorl %ebx,%ebx")),
  (713, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (86)))))]),
  (715, 2, parse("xorl %ebx,%ebx")),
  (717, 5, parse("leaq 0x18(%rsp),%r15")),
  (722, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (732, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (736, 8, parse("movq 0xd0(%rsp),%r9")),
  (744, 3, parse("subq %rbx,%r9")),
  (747, 6, parse("jb codec_emit_parts_u999")),
  (753, 5, parse("movq 0x10(%rsp),%rax")),
  (758, 4, parse("leaq (%rax,%rbx,1),%r8")),
  (762, 3, parse("movq %r15,%rdi")),
  (765, 3, parse("movq %r14,%rsi")),
  (768, 3, parse("movq %r12,%rdx")),
  (771, 2, parse("xorl %ecx,%ecx")),
  (773, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-2490)))))]),
  (778, 4, parse("movl 0x58(%rsp),%eax")),
  (782, 2, parse("testl %eax,%eax")),
  (784, 2, parse("jne codec_emit_parts_u818")),
  (786, 4, parse("addq $0x30,%r12")),
  (790, 5, parse("addq 0x18(%rsp),%rbx")),
  (795, 4, parse("addq $0xffffffffffffffd0,%r13"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (799, 2, parse("jne codec_emit_parts_u736")),
  (801, 5, parse("movq 0x8(%rsp),%rax")),
  (806, 3, parse("movq %rbx,(%rax)")),
  (809, 7, parse("movl $0x0,0x40(%rax)")),
  (816, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (86)))))]),
  (818, 5, parse("movq 0x18(%rsp),%rcx")),
  (823, 5, parse("movq 0x20(%rsp),%rdx")),
  (828, 5, parse("movq 0x50(%rsp),%rsi")),
  (833, 5, parse("movq 0x8(%rsp),%rdi")),
  (838, 4, parse("movq %rsi,0x38(%rdi)")),
  (842, 5, parse("movq 0x48(%rsp),%rsi")),
  (847, 4, parse("movq %rsi,0x30(%rdi)")),
  (851, 5, parse("movq 0x40(%rsp),%rsi")),
  (856, 4, parse("movq %rsi,0x28(%rdi)")),
  (860, 5, parse("movq 0x38(%rsp),%rsi")),
  (865, 4, parse("movq %rsi,0x20(%rdi)")),
  (869, 5, parse("movq 0x30(%rsp),%rsi")),
  (874, 4, parse("movq %rsi,0x18(%rdi)")),
  (878, 5, parse("movq 0x28(%rsp),%rsi")),
  (883, 4, parse("movq %rsi,0x10(%rdi)")),
  (887, 4, parse("movq %rdx,0x8(%rdi)")),
  (891, 4, parse("movl 0x5c(%rsp),%edx")),
  (895, 3, parse("movq %rcx,(%rdi)")),
  (898, 3, parse("movl %eax,0x40(%rdi)")),
  (901, 3, parse("movl %edx,0x44(%rdi)")),
  (904, 7, parse("addq $0x98,%rsp")),
  (911, 1, parse("popq %rbx")),
  (912, 2, parse("popq %r12")),
  (914, 2, parse("popq %r13")),
  (916, 2, parse("popq %r14")),
  (918, 2, parse("popq %r15")),
  (920, 1, parse("popq %rbp")),
  (921, 1, parse("retq ")),
  (922, 5, parse("movq 0x8(%rsp),%rax")),
  (927, 8, parse("movq $0x0,0x38(%rax)")),
  (935, 8, parse("movq $0x0,0x30(%rax)")),
  (943, 8, parse("movq $0x0,0x28(%rax)")),
  (951, 8, parse("movq $0x0,0x20(%rax)")),
  (959, 8, parse("movq $0x0,0x18(%rax)")),
  (967, 8, parse("movq $0x0,0x10(%rax)")),
  (975, 8, parse("movq $0x0,0x8(%rax)")),
  (983, 7, parse("movq $0x1,(%rax)")),
  (990, 7, parse("movl $0x8001,0x40(%rax)")),
  (997, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-95)))))]),
  (999, 3, parse("movq %rbx,%rdi")),
  (1002, 8, parse("movq 0xd0(%rsp),%rdx")),
  (1010, 3, parse("movq %rdx,%rsi")),
  (1013, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-61658)))))]),
  (1018, 3, parse("movq %r8,%rdi")),
  (1021, 3, parse("movq %rbp,%rsi")),
  (1024, 8, parse("movq 0xd0(%rsp),%rdx")),
  (1032, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-61677)))))]),
  (1037, 3, parse("movq %r10,%rdi")),
  (1040, 3, parse("movq %r14,%rsi")),
  (1043, 8, parse("movq 0xd0(%rsp),%rdx")),
  (1051, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-61696)))))]),
  (1056, 3, parse("movq %r14,%rdi")),
  (1059, 3, parse("movq %r14,%rsi")),
  (1062, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-61655)))))]),
  (1067, 3, parse("movq %rbx,%rdi")),
  (1070, 5, parse("movq 0x60(%rsp),%rsi")),
  (1075, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-61668)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2 ++ programChunk3

theorem program_length : program.length = 254 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 64 := by rfl
  have h3 : programChunk3.length = 62 := by rfl
  simp only [program, List.length_append, h0, h1, h2, h3]

def labels : List (String × Nat) := [
  ("codec_emit_parts_u208", 208),
  ("codec_emit_parts_u256", 256),
  ("codec_emit_parts_u288", 288),
  ("codec_emit_parts_u297", 297),
  ("codec_emit_parts_u300", 300),
  ("codec_emit_parts_u316", 316),
  ("codec_emit_parts_u436", 436),
  ("codec_emit_parts_u464", 464),
  ("codec_emit_parts_u558", 558),
  ("codec_emit_parts_u608", 608),
  ("codec_emit_parts_u701", 701),
  ("codec_emit_parts_u711", 711),
  ("codec_emit_parts_u715", 715),
  ("codec_emit_parts_u736", 736),
  ("codec_emit_parts_u818", 818),
  ("codec_emit_parts_u999", 999),
  ("codec_emit_parts_u1018", 1018),
  ("codec_emit_parts_u1037", 1037),
  ("codec_emit_parts_u1056", 1056),
  ("codec_emit_parts_u1067", 1067)]

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

def isFixedOffset : Int := 1088

def emitOffset : Int := -1712

def sliceIndexFailOffset : Int := -60640

def panicBoundsCheckOffset : Int := -60588

end SszX86.CodecEmitParts

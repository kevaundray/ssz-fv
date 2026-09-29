module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecMeasureChild
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2195680
def machineSize : Nat := 659

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 7, parse("subq $0xa8,%rsp")),
  (17, 3, parse("movq %rcx,%r14")),
  (20, 3, parse("movq %rsi,%r13")),
  (23, 3, parse("movq %rdi,%rbx")),
  (26, 3, parse("movq (%rsi),%r15")),
  (29, 3, parse("movq (%r15),%rax")),
  (32, 4, parse("movq 0x8(%r15),%rbp")),
  (36, 3, parse("testq %rax,%rax")),
  (39, 2, parse("je codec_measure_child_u59")),
  (41, 3, parse("cmpq %rbp,%rdx")),
  (44, 6, parse("jae codec_measure_child_u648")),
  (50, 4, parse("leaq (%rdx,%rdx,2),%rcx")),
  (54, 5, parse("movq 0x10(%rax,%rcx,8),%rbp")),
  (59, 4, parse("movq 0x10(%r13),%rsi")),
  (63, 3, parse("cmpq %rsi,%rdx")),
  (66, 6, parse("jae codec_measure_child_u640")),
  (72, 4, parse("leaq (%rdx,%rdx,2),%rdx")),
  (76, 4, parse("shlq $0x4,%rdx")),
  (80, 4, parse("addq 0x8(%r13),%rdx")),
  (84, 4, parse("movq 0x18(%r13),%rax")),
  (88, 4, [.instr (.regular .W64 .W32 (.movzx (.reg (.low .r8 .W32)) (.mem (w := .W8) { base := some (.reg .rax), idx := none, disp := .int64 (0) })))]),
  (92, 3, parse("movq %rsp,%rdi")),
  (95, 3, parse("movq %rbp,%rsi")),
  (98, 3, parse("movq %r14,%rcx")),
  (101, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-8458)))))]),
  (106, 4, parse("movl 0x40(%rsp),%eax")),
  (110, 4, parse("movq (%rsp),%rcx")),
  (114, 5, parse("movq 0x8(%rsp),%rdx")),
  (119, 5, parse("movq %rcx,0x48(%rsp)")),
  (124, 5, parse("movq %rdx,0x50(%rsp)")),
  (129, 5, parse("movq 0x10(%rsp),%r12")),
  (134, 5, parse("movq 0x18(%rsp),%r8")),
  (139, 5, parse("movq 0x20(%rsp),%rdi")),
  (144, 2, parse("testl %eax,%eax")),
  (146, 2, parse("je codec_measure_child_u219")),
  (148, 5, parse("movq 0x38(%rsp),%rcx")),
  (153, 4, parse("movq %rcx,0x38(%rbx)")),
  (157, 5, parse("movq 0x28(%rsp),%rcx")),
  (162, 5, parse("movq 0x30(%rsp),%rdx")),
  (167, 4, parse("movq %rdx,0x30(%rbx)")),
  (171, 4, parse("movq %rcx,0x28(%rbx)")),
  (175, 4, parse("movl 0x44(%rsp),%ecx")),
  (179, 5, parse("movq 0x48(%rsp),%rdx")),
  (184, 5, parse("movq 0x50(%rsp),%rsi")),
  (189, 4, parse("movq %rsi,0x8(%rbx)")),
  (193, 3, parse("movq %rdx,(%rbx)")),
  (196, 4, parse("movq %r12,0x10(%rbx)")),
  (200, 4, parse("movq %r8,0x18(%rbx)")),
  (204, 4, parse("movq %rdi,0x20(%rbx)")),
  (208, 3, parse("movl %eax,0x40(%rbx)")),
  (211, 3, parse("movl %ecx,0x44(%rbx)")),
  (214, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (403)))))]),
  (219, 8, parse("movq %r8,0x88(%rsp)")),
  (227, 5, parse("movq 0x48(%rsp),%rax")),
  (232, 5, parse("movq 0x50(%rsp),%rcx")),
  (237, 8, parse("movq %rax,0x98(%rsp)")),
  (245, 8, parse("movq %rcx,0xa0(%rsp)")),
  (253, 4, parse("cmpq $0x0,(%r15)"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (257, 8, parse("movq %rdi,0x90(%rsp)")),
  (265, 2, parse("je codec_measure_child_u285")),
  (267, 3, parse("movq %rbp,%rdi")),
  (270, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-2291)))))]),
  (275, 2, parse("testb %al,%al")),
  (277, 2, parse("je codec_measure_child_u294")),
  (279, 4, parse("movq 0x28(%r13),%r15")),
  (283, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (77)))))]),
  (285, 4, parse("movq 0x20(%r13),%rax")),
  (289, 3, parse("cmpb $0x0,(%rax)")),
  (292, 2, parse("jne codec_measure_child_u279")),
  (294, 4, parse("movq 0x28(%r13),%r15")),
  (298, 3, parse("movq (%r15),%rsi")),
  (301, 4, parse("movq 0x8(%r15),%rdx")),
  (305, 3, parse("movq %rsp,%rdi")),
  (308, 6, parse("movl $0x4,%r8d")),
  (314, 2, parse("xorl %ecx,%ecx")),
  (316, 3, parse("movq %r14,%r9")),
  (319, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-46148)))))]),
  (324, 4, parse("movl 0x40(%rsp),%eax")),
  (328, 2, parse("testl %eax,%eax")),
  (330, 2, parse("jne codec_measure_child_u403")),
  (332, 4, parse("movq (%rsp),%rax")),
  (336, 5, parse("movq 0x8(%rsp),%rcx")),
  (341, 5, parse("movq %rcx,0x50(%rsp)")),
  (346, 5, parse("movq %rax,0x48(%rsp)")),
  (351, 4, parse("movq %rcx,0x8(%r15)")),
  (355, 3, parse("movq %rax,(%r15)")),
  (358, 4, parse("movq 0x30(%r13),%r15")),
  (362, 3, parse("movq (%r15),%rsi")),
  (365, 4, parse("movq 0x8(%r15),%rdx")),
  (369, 3, parse("movq %rsp,%rdi")),
  (372, 3, parse("movq %r12,%rcx")),
  (375, 8, parse("movq 0x88(%rsp),%r8")),
  (383, 3, parse("movq %r14,%r9")),
  (386, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-46215)))))]),
  (391, 4, parse("movl 0x40(%rsp),%eax")),
  (395, 2, parse("testl %eax,%eax")),
  (397, 6, parse("je codec_measure_child_u538")),
  (403, 5, parse("movq 0x38(%rsp),%rcx")),
  (408, 8, parse("movq %rcx,0x80(%rsp)")),
  (416, 5, parse("movq 0x30(%rsp),%rcx")),
  (421, 5, parse("movq %rcx,0x78(%rsp)")),
  (426, 5, parse("movq 0x28(%rsp),%rdx")),
  (431, 5, parse("movq %rdx,0x70(%rsp)")),
  (436, 5, parse("movq 0x20(%rsp),%rsi")),
  (441, 5, parse("movq %rsi,0x68(%rsp)")),
  (446, 5, parse("movq 0x18(%rsp),%rdi")),
  (451, 5, parse("movq %rdi,0x60(%rsp)")),
  (456, 5, parse("movq 0x10(%rsp),%r8")),
  (461, 5, parse("movq %r8,0x58(%rsp)")),
  (466, 4, parse("movq (%rsp),%r9")),
  (470, 5, parse("movq 0x8(%rsp),%r10")),
  (475, 5, parse("movq %r10,0x50(%rsp)")),
  (480, 5, parse("movq %r9,0x48(%rsp)")),
  (485, 5, parse("movl 0x44(%rsp),%r11d")),
  (490, 8, parse("movq 0x80(%rsp),%r14")),
  (498, 4, parse("movq %r14,0x38(%rbx)")),
  (502, 4, parse("movq %rcx,0x30(%rbx)")),
  (506, 4, parse("movq %rdx,0x28(%rbx)")),
  (510, 4, parse("movq %rsi,0x20(%rbx)")),
  (514, 4, parse("movq %rdi,0x18(%rbx)")),
  (518, 4, parse("movq %r8,0x10(%rbx)")),
  (522, 4, parse("movq %r10,0x8(%rbx)"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (526, 3, parse("movq %r9,(%rbx)")),
  (529, 3, parse("movl %eax,0x40(%rbx)")),
  (532, 4, parse("movl %r11d,0x44(%rbx)")),
  (536, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (84)))))]),
  (538, 4, parse("movq (%rsp),%rax")),
  (542, 5, parse("movq 0x8(%rsp),%rcx")),
  (547, 5, parse("movq %rcx,0x50(%rsp)")),
  (552, 5, parse("movq %rax,0x48(%rsp)")),
  (557, 4, parse("movq %rcx,0x8(%r15)")),
  (561, 3, parse("movq %rax,(%r15)")),
  (564, 8, parse("movq 0x98(%rsp),%rax")),
  (572, 8, parse("movq 0xa0(%rsp),%rcx")),
  (580, 4, parse("movq %rcx,0x8(%rbx)")),
  (584, 3, parse("movq %rax,(%rbx)")),
  (587, 4, parse("movq %r12,0x10(%rbx)")),
  (591, 8, parse("movq 0x88(%rsp),%rax")),
  (599, 4, parse("movq %rax,0x18(%rbx)")),
  (603, 8, parse("movq 0x90(%rsp),%rax")),
  (611, 4, parse("movq %rax,0x20(%rbx)")),
  (615, 7, parse("movl $0x0,0x40(%rbx)")),
  (622, 7, parse("addq $0xa8,%rsp")),
  (629, 1, parse("popq %rbx")),
  (630, 2, parse("popq %r12")),
  (632, 2, parse("popq %r13")),
  (634, 2, parse("popq %r14")),
  (636, 2, parse("popq %r15")),
  (638, 1, parse("popq %rbp")),
  (639, 1, parse("retq ")),
  (640, 3, parse("movq %rdx,%rdi")),
  (643, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-64340)))))]),
  (648, 3, parse("movq %rdx,%rdi")),
  (651, 3, parse("movq %rbp,%rsi")),
  (654, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-64351)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2

theorem program_length : program.length = 161 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 33 := by rfl
  simp only [program, List.length_append, h0, h1, h2]

def labels : List (String × Nat) := [
  ("codec_measure_child_u59", 59),
  ("codec_measure_child_u219", 219),
  ("codec_measure_child_u279", 279),
  ("codec_measure_child_u285", 285),
  ("codec_measure_child_u294", 294),
  ("codec_measure_child_u403", 403),
  ("codec_measure_child_u538", 538),
  ("codec_measure_child_u640", 640),
  ("codec_measure_child_u648", 648)]

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

def measureOffset : Int := -8352

def isFixedOffset : Int := -2016

def natAddOffset : Int := -45824

def panicBoundsCheckOffset : Int := -63692

end SszX86.CodecMeasureChild

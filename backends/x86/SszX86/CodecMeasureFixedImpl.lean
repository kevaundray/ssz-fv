module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.CodecMeasureFixed
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2214528
def machineSize : Nat := 777

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 1, parse("pushq %rbp")),
  (1, 2, parse("pushq %r15")),
  (3, 2, parse("pushq %r14")),
  (5, 2, parse("pushq %r13")),
  (7, 2, parse("pushq %r12")),
  (9, 1, parse("pushq %rbx")),
  (10, 4, parse("subq $0x58,%rsp")),
  (14, 3, parse("movq %rdi,%rbx")),
  (17, 3, parse("movq (%rsi),%rax")),
  (20, 4, parse("cmpq $0xb,%rax")),
  (24, 6, parse("ja codec_measure_fixed_u680")),
  (30, 3, parse("movq %rdx,%r12")),
  (33, 7, [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-116248)}))]),
  (40, 4, [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))]),
  (44, 3, parse("addq %rcx,%rax")),
  (47, 2, [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))]),
  (49, 4, parse("movq 0x8(%rsi),%r14")),
  (53, 4, parse("movq 0x10(%rsi),%r15")),
  (57, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (209)))))]),
  (62, 5, parse("movl $0x8,%eax")),
  (67, 5, parse("movq 0x8(%rsi,%rax,1),%rcx")),
  (72, 3, parse("testq %rcx,%rcx")),
  (75, 6, parse("je codec_measure_fixed_u254")),
  (81, 4, parse("movq (%rsi,%rax,1),%rax")),
  (85, 5, parse("movq %rax,0x50(%rsp)")),
  (90, 4, parse("shlq $0x3,%rcx")),
  (94, 4, parse("leaq (%rcx,%rcx,2),%rax")),
  (98, 5, parse("movq %rax,0x48(%rsp)")),
  (103, 2, parse("xorl %ebp,%ebp")),
  (105, 3, parse("movq %rsp,%r13")),
  (108, 3, parse("xorl %r14d,%r14d")),
  (111, 3, parse("xorl %r15d,%r15d")),
  (114, 10, [.instr (.regular .W64 .W64 (.nop 10))]),
  (124, 4, [.instr (.regular .W64 .W64 (.nop 4))]),
  (128, 5, parse("movq 0x50(%rsp),%rax")),
  (133, 5, parse("movq 0x10(%rax,%rbp,1),%rsi")),
  (138, 3, parse("movq %r13,%rdi")),
  (141, 3, parse("movq %r12,%rdx")),
  (144, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-149)))))]),
  (149, 4, parse("movl 0x40(%rsp),%eax")),
  (153, 4, parse("movq (%rsp),%rdx")),
  (157, 5, parse("movq 0x8(%rsp),%rcx")),
  (162, 5, parse("movq 0x10(%rsp),%r8")),
  (167, 2, parse("testl %eax,%eax")),
  (169, 6, parse("jne codec_measure_fixed_u709")),
  (175, 3, parse("testb $0x1,%dl")),
  (178, 6, parse("je codec_measure_fixed_u680")),
  (184, 3, parse("movq %r13,%rdi")),
  (187, 3, parse("movq %r14,%rsi")),
  (190, 3, parse("movq %r15,%rdx")),
  (193, 3, parse("movq %r12,%r9")),
  (196, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-64873)))))]),
  (201, 4, parse("movl 0x40(%rsp),%eax")),
  (205, 4, parse("movq (%rsp),%r14")),
  (209, 5, parse("movq 0x8(%rsp),%r15")),
  (214, 2, parse("testl %eax,%eax")),
  (216, 6, parse("jne codec_measure_fixed_u607")),
  (222, 4, parse("addq $0x18,%rbp")),
  (226, 5, parse("cmpq %rbp,0x48(%rsp)")),
  (231, 2, parse("jne codec_measure_fixed_u128")),
  (233, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (36)))))]),
  (235, 5, parse("movl $0x18,%eax")),
  (240, 5, parse("movq 0x8(%rsi,%rax,1),%rcx")),
  (245, 3, parse("testq %rcx,%rcx"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (248, 6, parse("jne codec_measure_fixed_u81")),
  (254, 3, parse("xorl %r14d,%r14d")),
  (257, 3, parse("xorl %r15d,%r15d")),
  (260, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (9)))))]),
  (262, 6, parse("movl $0x1,%r15d")),
  (268, 3, parse("xorl %r14d,%r14d")),
  (271, 4, parse("movq %r14,0x8(%rbx)")),
  (275, 4, parse("movq %r15,0x10(%rbx)")),
  (279, 7, parse("movq $0x1,(%rbx)")),
  (286, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (396)))))]),
  (291, 4, parse("movq 0x8(%rsi),%rax")),
  (295, 4, parse("movq 0x10(%rsi),%rdx")),
  (299, 3, parse("movq %rsp,%rdi")),
  (302, 5, parse("movl $0x8,%ecx")),
  (307, 3, parse("movq %rax,%rsi")),
  (310, 3, parse("movq %r12,%r8")),
  (313, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-73294)))))]),
  (318, 4, parse("movl 0x40(%rsp),%eax")),
  (322, 4, parse("movq (%rsp),%r14")),
  (326, 5, parse("movq 0x8(%rsp),%r15")),
  (331, 5, parse("movq 0x10(%rsp),%rcx")),
  (336, 2, parse("testl %eax,%eax")),
  (338, 6, parse("je codec_measure_fixed_u526")),
  (344, 5, parse("movq 0x38(%rsp),%rdx")),
  (349, 4, parse("movq %rdx,0x38(%rbx)")),
  (353, 5, parse("movq 0x30(%rsp),%rdx")),
  (358, 4, parse("movq %rdx,0x30(%rbx)")),
  (362, 5, parse("movq 0x28(%rsp),%rdx")),
  (367, 4, parse("movq %rdx,0x28(%rbx)")),
  (371, 5, parse("movq 0x18(%rsp),%rdx")),
  (376, 5, parse("movq 0x20(%rsp),%rsi")),
  (381, 4, parse("movq %rsi,0x20(%rbx)")),
  (385, 4, parse("movq %rdx,0x18(%rbx)")),
  (389, 4, parse("movl 0x44(%rsp),%edx")),
  (393, 3, parse("movq %r14,(%rbx)")),
  (396, 4, parse("movq %r15,0x8(%rbx)")),
  (400, 4, parse("movq %rcx,0x10(%rbx)")),
  (404, 3, parse("movl %eax,0x40(%rbx)")),
  (407, 3, parse("movl %edx,0x44(%rbx)")),
  (410, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (279)))))]),
  (415, 3, parse("movq %rsi,%r14")),
  (418, 4, parse("movq 0x18(%rsi),%rsi")),
  (422, 3, parse("movq %rsp,%rdi")),
  (425, 3, parse("movq %r12,%rdx")),
  (428, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-433)))))]),
  (433, 4, parse("movl 0x40(%rsp),%eax")),
  (437, 4, parse("movq (%rsp),%rcx")),
  (441, 5, parse("movq 0x8(%rsp),%rsi")),
  (446, 5, parse("movq 0x10(%rsp),%rdx")),
  (451, 2, parse("testl %eax,%eax")),
  (453, 2, parse("je codec_measure_fixed_u562")),
  (455, 5, parse("movq 0x38(%rsp),%rdi")),
  (460, 4, parse("movq %rdi,0x38(%rbx)")),
  (464, 5, parse("movq 0x30(%rsp),%rdi")),
  (469, 4, parse("movq %rdi,0x30(%rbx)")),
  (473, 5, parse("movq 0x28(%rsp),%rdi")),
  (478, 4, parse("movq %rdi,0x28(%rbx)")),
  (482, 5, parse("movq 0x18(%rsp),%rdi")),
  (487, 5, parse("movq 0x20(%rsp),%r8")),
  (492, 4, parse("movq %r8,0x20(%rbx)")),
  (496, 4, parse("movq %rdi,0x18(%rbx)")),
  (500, 4, parse("movl 0x44(%rsp),%edi")),
  (504, 4, parse("movq %rsi,0x8(%rbx)")),
  (508, 4, parse("movq %rdx,0x10(%rbx)"))]

def programChunk2 : List (Nat × Nat × Program) := [
  (512, 3, parse("movq %rcx,(%rbx)")),
  (515, 3, parse("movl %eax,0x40(%rbx)")),
  (518, 3, parse("movl %edi,0x44(%rbx)")),
  (521, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (168)))))]),
  (526, 3, parse("testq %rcx,%rcx")),
  (529, 6, parse("je codec_measure_fixed_u271")),
  (535, 3, parse("movq %rsp,%rdi")),
  (538, 6, parse("movl $0x1,%r8d")),
  (544, 3, parse("movq %r14,%rsi")),
  (547, 3, parse("movq %r15,%rdx")),
  (550, 2, parse("xorl %ecx,%ecx")),
  (552, 3, parse("movq %r12,%r9")),
  (555, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-65232)))))]),
  (560, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (24)))))]),
  (562, 3, parse("testb $0x1,%cl")),
  (565, 2, parse("je codec_measure_fixed_u680")),
  (567, 4, parse("movq 0x8(%r14),%rcx")),
  (571, 4, parse("movq 0x10(%r14),%r8")),
  (575, 3, parse("movq %rsp,%rdi")),
  (578, 3, parse("movq %r12,%r9")),
  (581, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-62378)))))]),
  (586, 4, parse("movl 0x40(%rsp),%eax")),
  (590, 4, parse("movq (%rsp),%r14")),
  (594, 5, parse("movq 0x8(%rsp),%r15")),
  (599, 2, parse("testl %eax,%eax")),
  (601, 6, parse("je codec_measure_fixed_u271")),
  (607, 5, parse("movq 0x38(%rsp),%rcx")),
  (612, 4, parse("movq %rcx,0x38(%rbx)")),
  (616, 5, parse("movq 0x30(%rsp),%rcx")),
  (621, 4, parse("movq %rcx,0x30(%rbx)")),
  (625, 5, parse("movq 0x28(%rsp),%rcx")),
  (630, 4, parse("movq %rcx,0x28(%rbx)")),
  (634, 5, parse("movq 0x20(%rsp),%rcx")),
  (639, 4, parse("movq %rcx,0x20(%rbx)")),
  (643, 5, parse("movq 0x10(%rsp),%rcx")),
  (648, 5, parse("movq 0x18(%rsp),%rdx")),
  (653, 4, parse("movq %rdx,0x18(%rbx)")),
  (657, 4, parse("movq %rcx,0x10(%rbx)")),
  (661, 4, parse("movl 0x44(%rsp),%ecx")),
  (665, 3, parse("movq %r14,(%rbx)")),
  (668, 4, parse("movq %r15,0x8(%rbx)")),
  (672, 3, parse("movl %eax,0x40(%rbx)")),
  (675, 3, parse("movl %ecx,0x44(%rbx)")),
  (678, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (14)))))]),
  (680, 7, parse("movq $0x0,(%rbx)")),
  (687, 7, parse("movl $0x0,0x40(%rbx)")),
  (694, 4, parse("addq $0x58,%rsp")),
  (698, 1, parse("popq %rbx")),
  (699, 2, parse("popq %r12")),
  (701, 2, parse("popq %r13")),
  (703, 2, parse("popq %r14")),
  (705, 2, parse("popq %r15")),
  (707, 1, parse("popq %rbp")),
  (708, 1, parse("retq ")),
  (709, 5, parse("movq 0x38(%rsp),%rsi")),
  (714, 4, parse("movq %rsi,0x38(%rbx)")),
  (718, 5, parse("movq 0x30(%rsp),%rsi")),
  (723, 4, parse("movq %rsi,0x30(%rbx)")),
  (727, 5, parse("movq 0x28(%rsp),%rsi")),
  (732, 4, parse("movq %rsi,0x28(%rbx)")),
  (736, 5, parse("movq 0x18(%rsp),%rsi")),
  (741, 5, parse("movq 0x20(%rsp),%rdi")),
  (746, 4, parse("movq %rdi,0x20(%rbx)")),
  (750, 4, parse("movq %rsi,0x18(%rbx)"))]

def programChunk3 : List (Nat × Nat × Program) := [
  (754, 4, parse("movl 0x44(%rsp),%esi")),
  (758, 4, parse("movq %rcx,0x8(%rbx)")),
  (762, 4, parse("movq %r8,0x10(%rbx)")),
  (766, 3, parse("movq %rdx,(%rbx)")),
  (769, 3, parse("movl %eax,0x40(%rbx)")),
  (772, 3, parse("movl %esi,0x44(%rbx)")),
  (775, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-83)))))])]

/-- Complete native function, including recursive calls and panic blocks. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++ programChunk1 ++ programChunk2 ++ programChunk3

theorem program_length : program.length = 199 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 64 := by rfl
  have h2 : programChunk2.length = 64 := by rfl
  have h3 : programChunk3.length = 7 := by rfl
  simp only [program, List.length_append, h0, h1, h2, h3]

def labels : List (String × Nat) := [
  ("codec_measure_fixed_u81", 81),
  ("codec_measure_fixed_u128", 128),
  ("codec_measure_fixed_u254", 254),
  ("codec_measure_fixed_u271", 271),
  ("codec_measure_fixed_u526", 526),
  ("codec_measure_fixed_u562", 562),
  ("codec_measure_fixed_u607", 607),
  ("codec_measure_fixed_u680", 680),
  ("codec_measure_fixed_u709", 709)]

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

def tableOffset : Int := -116208
def tableAddress (base : Int64) : BitVec 64 :=
  (base + Int64.ofInt tableOffset).toBitVec

def tableBytes : List UInt8 :=
  [0xf6, 0xc6, 0x01, 0x00, 0x21, 0xc6, 0x01, 0x00, 0x21, 0xc6, 0x01, 0x00, 0x98, 0xc8, 0x01, 0x00, 0x13, 0xc7, 0x01, 0x00, 0x98, 0xc8, 0x01, 0x00, 0x98, 0xc8, 0x01, 0x00, 0x8f, 0xc7, 0x01, 0x00, 0x98, 0xc8, 0x01, 0x00, 0x98, 0xc8, 0x01, 0x00, 0x2e, 0xc6, 0x01, 0x00, 0xdb, 0xc6, 0x01, 0x00]

def tableDestinations : List Nat := [262, 49, 49, 680, 291, 680, 680, 415, 680, 680, 62, 235]

def TableAt (m : DataMem) (base : Int64) : Prop :=
  ∀ i (hi : i < tableBytes.length),
    m.get? (tableAddress base + BitVec.ofNat 64 i) = some tableBytes[i]

def measureFixedOffset : Int := 0

def natAddOffset : Int := -64672

def natDivRemSmallOffset : Int := -72976

def natMulOffset : Int := -61792

end SszX86.CodecMeasureFixed

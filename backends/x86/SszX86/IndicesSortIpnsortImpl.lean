module

public import SszX86.BoolImpl

@[expose] public section

namespace SszX86.IndicesSortIpnsort
open Kraken.X64.Parser

abbrev step := BoolCodec.step

def entry : Nat := 0
def linkedAddress : Nat := 2266720
def machineSize : Nat := 358

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
  (17, 4, parse("movq 0x10(%rdi),%r15")),
  (21, 4, parse("movq 0x18(%rdi),%r12")),
  (25, 3, parse("movq (%rdi),%rdi")),
  (28, 4, parse("movq 0x8(%r14),%rsi")),
  (32, 3, parse("movq %r15,%rdx")),
  (35, 3, parse("movq %r12,%rcx")),
  (38, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-112315)))))]),
  (43, 4, parse("movb %al,0x7(%rsp)")),
  (47, 4, parse("leaq 0x28(%r14),%rbp")),
  (51, 6, parse("movl $0x2,%r13d")),
  (57, 2, parse("cmpb $0xff,%al")),
  (59, 2, parse("je indices_sort_ipnsort_u124")),
  (61, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (64, 3, parse("movq %r15,%rdi")),
  (67, 3, parse("movq %r12,%rsi")),
  (70, 4, parse("movq -0x8(%rbp),%r15")),
  (74, 4, parse("movq 0x0(%rbp),%r12")),
  (78, 3, parse("movq %r15,%rdx")),
  (81, 3, parse("movq %r12,%rcx")),
  (84, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-112361)))))]),
  (89, 2, parse("cmpb $0xff,%al")),
  (91, 2, parse("je indices_sort_ipnsort_u153")),
  (93, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r13 .W64))))]),
  (96, 4, parse("addq $0x10,%rbp")),
  (100, 3, parse("cmpq %r13,%rbx")),
  (103, 2, parse("jne indices_sort_ipnsort_u64")),
  (105, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (51)))))]),
  (107, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (112, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r13 .W64))))]),
  (115, 4, parse("addq $0x10,%rbp")),
  (119, 3, parse("cmpq %r13,%rbx")),
  (122, 2, parse("je indices_sort_ipnsort_u158")),
  (124, 3, parse("movq %r15,%rdi")),
  (127, 3, parse("movq %r12,%rsi")),
  (130, 4, parse("movq -0x8(%rbp),%r15")),
  (134, 4, parse("movq 0x0(%rbp),%r12")),
  (138, 3, parse("movq %r15,%rdx")),
  (141, 3, parse("movq %r12,%rcx")),
  (144, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-112421)))))]),
  (149, 2, parse("cmpb $0xff,%al")),
  (151, 2, parse("je indices_sort_ipnsort_u112")),
  (153, 3, parse("cmpq %rbx,%r13")),
  (156, 2, parse("jne indices_sort_ipnsort_u256")),
  (158, 5, parse("cmpb $0xff,0x7(%rsp)")),
  (163, 2, parse("jne indices_sort_ipnsort_u241")),
  (165, 8, [.instr (.regular .W64 .W64 (.lea (.low .rax .W64) { base := none, idx := some ⟨.rbx, .W64⟩, disp := .int64 (0) }))]),
  (173, 4, parse("andq $0xfffffffffffffff0,%rax")),
  (177, 4, parse("shlq $0x4,%rbx")),
  (181, 4, parse("addq $0xfffffffffffffff8,%rbx")),
  (185, 2, parse("xorl %ecx,%ecx")),
  (187, 5, [.instr (.regular .W64 .W64 (.nop 5))]),
  (192, 4, parse("movq (%r14,%rcx,1),%rdx")),
  (196, 5, parse("movq -0x8(%r14,%rbx,1),%rsi")),
  (201, 4, parse("movq %rsi,(%r14,%rcx,1)")),
  (205, 5, parse("movq %rdx,-0x8(%r14,%rbx,1)"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (210, 5, parse("movq 0x8(%r14,%rcx,1),%rdx")),
  (215, 4, parse("movq (%r14,%rbx,1),%rsi")),
  (219, 5, parse("movq %rsi,0x8(%r14,%rcx,1)")),
  (224, 4, parse("movq %rdx,(%r14,%rbx,1)")),
  (228, 4, parse("addq $0x10,%rcx")),
  (232, 4, parse("addq $0xfffffffffffffff0,%rbx")),
  (236, 3, parse("cmpq %rcx,%rax")),
  (239, 2, parse("jne indices_sort_ipnsort_u192")),
  (241, 4, parse("addq $0x8,%rsp")),
  (245, 1, parse("popq %rbx")),
  (246, 2, parse("popq %r12")),
  (248, 2, parse("popq %r13")),
  (250, 2, parse("popq %r14")),
  (252, 2, parse("popq %r15")),
  (254, 1, parse("popq %rbp")),
  (255, 1, parse("retq ")),
  (256, 3, parse("movq %rbx,%rax")),
  (259, 4, parse("orq $0x1,%rax")),
  (263, 5, parse("leaq -0x10(%rsp),%rsp")),
  (268, 4, parse("movq %r11,(%rsp)")),
  (272, 5, parse("movq %r10,0x8(%rsp)")),
  (277, 3, parse("movq %rax,%r11")),
  (280, 3, parse("testq %r11,%r11")),
  (283, 2, parse("je indices_sort_ipnsort_u309")),
  (285, 7, parse("movq $0xffffffffffffffff,%r10")),
  (292, 3, [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))]),
  (295, 3, parse("shrq $1,%r11")),
  (298, 2, parse("jne indices_sort_ipnsort_u292")),
  (300, 3, parse("movq %r10,%rcx")),
  (303, 4, parse("cmpq $0xffffffffffffffff,%r10")),
  (307, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))]),
  (309, 4, parse("movq (%rsp),%r11")),
  (313, 5, parse("movq 0x8(%rsp),%r10")),
  (318, 5, parse("leaq 0x10(%rsp),%rsp")),
  (323, 3, parse("xorl $0x3f,%ecx")),
  (326, 2, parse("addl %ecx,%ecx")),
  (328, 3, parse("xorl $0x7e,%ecx")),
  (331, 3, parse("movq %r14,%rdi")),
  (334, 3, parse("movq %rbx,%rsi")),
  (337, 2, parse("xorl %edx,%edx")),
  (339, 4, parse("addq $0x8,%rsp")),
  (343, 1, parse("popq %rbx")),
  (344, 2, parse("popq %r12")),
  (346, 2, parse("popq %r13")),
  (348, 2, parse("popq %r14")),
  (350, 2, parse("popq %r15")),
  (352, 1, parse("popq %rbp")),
  (353, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (634)))))])]

/-- The complete actual linked function; no branch or panic boundary is removed. -/
def program : List (Nat × Nat × Program) :=
  programChunk0 ++
  programChunk1

theorem program_length : program.length = 112 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 48 := by rfl
  simp only [program, List.length_append, h0, h1]

def labels : List (String × Nat) := [
  ("indices_sort_ipnsort_u64", 64),
  ("indices_sort_ipnsort_u112", 112),
  ("indices_sort_ipnsort_u124", 124),
  ("indices_sort_ipnsort_u153", 153),
  ("indices_sort_ipnsort_u158", 158),
  ("indices_sort_ipnsort_u192", 192),
  ("indices_sort_ipnsort_u241", 241),
  ("indices_sort_ipnsort_u256", 256),
  ("indices_sort_ipnsort_u292", 292),
  ("indices_sort_ipnsort_u309", 309)]

def natCompareOffset : Int := -112272

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

end SszX86.IndicesSortIpnsort

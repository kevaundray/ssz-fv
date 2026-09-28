import SszX86.MeasureImpl
import SszX86.EmitMemcpyEmbedded
import SszX86.NatCompareImpl
import SszX86.NatFromU128Impl

namespace SszX86.Serialize
open Kraken.X64.Parser

/-- Entry of the actual standalone codec::serialize wrapper, not serialize_alloc. -/
def entry : Nat := 0
def measureOffset : Int := -33488
def emitOffset : Int := -29952
def compareOffset : Int := -66368
def fromU128Offset : Int := -48192
def memcpyOffset : Int := 80784
def measureTableOffset : Int := -122804
def emitTableOffset : Int := -122752

def programChunk0 : List (Nat × Nat × Program) := [
  (0, 2, parse("pushq %r15")),
  (2, 2, parse("pushq %r14")),
  (4, 2, parse("pushq %r13")),
  (6, 2, parse("pushq %r12")),
  (8, 1, parse("pushq %rbx")),
  (9, 4, parse("subq $0x60,%rsp")),
  (13, 3, parse("movq %r8,%r13")),
  (16, 3, parse("movq %rcx,%r14")),
  (19, 3, parse("movq %rdx,%r15")),
  (22, 3, parse("movq %rsi,%r12")),
  (25, 3, parse("movq %rdi,%rbx")),
  (28, 5, parse("leaq 0x18(%rsp),%rdi")),
  (33, 3, parse("movq %r9,%rcx")),
  (36, 6, parse("movl $0x1,%r8d")),
  (42, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-33535)))))]),
  (47, 4, parse("movl 0x58(%rsp),%ecx")),
  (51, 5, parse("movq 0x18(%rsp),%rax")),
  (56, 5, parse("movq 0x20(%rsp),%rdx")),
  (61, 5, parse("movq %rax,0x8(%rsp)")),
  (66, 5, parse("movq %rdx,0x10(%rsp)")),
  (71, 5, parse("movq 0x28(%rsp),%rax")),
  (76, 5, parse("movq 0x30(%rsp),%r9")),
  (81, 5, parse("movq 0x38(%rsp),%rdx")),
  (86, 2, parse("testl %ecx,%ecx")),
  (88, 2, parse("je serialize_u161")),
  (90, 5, parse("movq 0x50(%rsp),%rsi")),
  (95, 4, parse("movq %rsi,0x38(%rbx)")),
  (99, 5, parse("movq 0x40(%rsp),%rsi")),
  (104, 5, parse("movq 0x48(%rsp),%rdi")),
  (109, 4, parse("movq %rdi,0x30(%rbx)")),
  (113, 4, parse("movq %rsi,0x28(%rbx)")),
  (117, 4, parse("movl 0x5c(%rsp),%esi")),
  (121, 5, parse("movq 0x8(%rsp),%rdi")),
  (126, 5, parse("movq 0x10(%rsp),%r8")),
  (131, 4, parse("movq %r8,0x8(%rbx)")),
  (135, 3, parse("movq %rdi,(%rbx)")),
  (138, 4, parse("movq %rax,0x10(%rbx)")),
  (142, 4, parse("movq %r9,0x18(%rbx)")),
  (146, 4, parse("movq %rdx,0x20(%rbx)")),
  (150, 3, parse("movl %ecx,0x40(%rbx)")),
  (153, 3, parse("movl %esi,0x44(%rbx)")),
  (156, 5, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (249)))))]),
  (161, 5, parse("movq 0x8(%rsp),%rcx")),
  (166, 5, parse("movq 0x10(%rsp),%rsi")),
  (171, 5, parse("movq %rcx,0x18(%rsp)")),
  (176, 5, parse("movq %rsi,0x20(%rsp)")),
  (181, 5, parse("movq %rax,0x28(%rsp)")),
  (186, 5, parse("movq %r9,0x30(%rsp)")),
  (191, 5, parse("movq %rdx,0x38(%rsp)")),
  (196, 3, parse("testq %rax,%rax")),
  (199, 2, parse("je serialize_u308")),
  (201, 4, parse("leaq 0x1(%r9),%rcx")),
  (205, 3, [.instr (.regular .W64 .W64 (.nop 3))]),
  (208, 4, parse("cmpq $0x1,%rcx")),
  (212, 2, parse("je serialize_u300")),
  (214, 4, parse("leaq -0x1(%rcx),%rdx")),
  (218, 6, parse("cmpq $0x0,-0x10(%rax,%rcx,8)")),
  (224, 3, parse("movq %rdx,%rcx")),
  (227, 2, parse("je serialize_u208")),
  (229, 4, parse("cmpq $0x1,%rdx")),
  (233, 2, parse("je serialize_u305")),
  (235, 8, parse("movq $0x0,0x38(%rbx)")),
  (243, 8, parse("movq $0x0,0x30(%rbx)")),
  (251, 8, parse("movq $0x0,0x28(%rbx)"))]

def programChunk1 : List (Nat × Nat × Program) := [
  (259, 8, parse("movq $0x0,0x20(%rbx)")),
  (267, 8, parse("movq $0x0,0x18(%rbx)")),
  (275, 8, parse("movq $0x0,0x10(%rbx)")),
  (283, 8, parse("movq $0x0,0x8(%rbx)")),
  (291, 7, parse("movq $0x1,(%rbx)")),
  (298, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (76)))))]),
  (300, 3, parse("testq %r9,%r9")),
  (303, 2, parse("je serialize_u385")),
  (305, 3, parse("movq (%rax),%r9")),
  (308, 3, parse("cmpq %r9,%r13")),
  (311, 2, parse("jae serialize_u388")),
  (313, 7, parse("movq $0x1,(%rbx)")),
  (320, 8, parse("movq $0x0,0x8(%rbx)")),
  (328, 8, parse("movq $0x0,0x10(%rbx)")),
  (336, 8, parse("movq $0x0,0x18(%rbx)")),
  (344, 8, parse("movq $0x0,0x20(%rbx)")),
  (352, 8, parse("movq $0x0,0x28(%rbx)")),
  (360, 8, parse("movq $0x0,0x30(%rbx)")),
  (368, 8, parse("movq $0x0,0x38(%rbx)")),
  (376, 7, parse("movl $0x8001,0x40(%rbx)")),
  (383, 2, [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (25)))))]),
  (385, 3, parse("xorl %r9d,%r9d")),
  (388, 5, parse("leaq 0x18(%rsp),%rcx")),
  (393, 3, parse("movq %rbx,%rdi")),
  (396, 3, parse("movq %r12,%rsi")),
  (399, 3, parse("movq %r15,%rdx")),
  (402, 3, parse("movq %r14,%r8")),
  (405, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-30362)))))]),
  (410, 4, parse("addq $0x60,%rsp")),
  (414, 1, parse("popq %rbx")),
  (415, 2, parse("popq %r12")),
  (417, 2, parse("popq %r13")),
  (419, 2, parse("popq %r14")),
  (421, 2, parse("popq %r15")),
  (423, 1, parse("retq "))]

/-- The original 99 instruction rows spanning all 424 wrapper bytes. -/
def program : List (Nat × Nat × Program) := programChunk0 ++ programChunk1

theorem program_length : program.length = 99 := by
  have h0 : programChunk0.length = 64 := by rfl
  have h1 : programChunk1.length = 35 := by rfl
  simp only [program, List.length_append, h0, h1]

def labels : List (String × Nat) := [
  ("serialize_u161", 161),
  ("serialize_u208", 208),
  ("serialize_u300", 300),
  ("serialize_u305", 305),
  ("serialize_u308", 308),
  ("serialize_u385", 385),
  ("serialize_u388", 388)]

def directives (row : Nat × Nat × Program) : List (Directive × Nat) :=
  ((labels.filter (fun item => item.2 == row.1)).map
    (fun item => (Directive.label item.1, 0))) ++
  row.2.2.map (fun instruction => (instruction, row.2.1))

/-- Structural ownership only: no wrapper execution or semantic refinement claim. -/
structure CodeAt (e : Executable) (base : Int64) : Prop where
  fetch : ∀ row ∈ program,
    e.directivesAtAddress (base + Int64.ofNat row.1) = directives row
  targets : ∀ item ∈ labels, e.labels.label item.1 = base + Int64.ofNat item.2

/-- Every component belongs to the same executable at its actual linked base. -/
structure ClosureAt (e : Executable) (base : Int64) : Prop where
  wrapper : CodeAt e base
  measure : Measure.CodeAt e (base + Int64.ofInt measureOffset)
  emit : Emit.CodeAt e (base + Int64.ofInt emitOffset)
  compare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset)
  fromU128 : NatFromU128.CodeAt e (base + Int64.ofInt fromU128Offset)
  memcpy : Emit.MemcpyCodeAt e (base + Int64.ofInt memcpyOffset)

end SszX86.Serialize

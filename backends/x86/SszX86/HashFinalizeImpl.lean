module

public import SszX86.HashImpl

@[expose] public section

namespace SszX86.Hash.Finalize
open Kraken.X64.Parser

def program : List Row := [
  (0, 2, parse("pushq %r14")),
  (2, 1, parse("pushq %rbx")),
  (3, 1, parse("pushq %rax")),
  (4, 3, parse("movq %rdi,%rbx")),
  (7, 4, parse("movq 0x60(%rsi),%rdi")),
  (11, 4, parse("cmpq $0x3f,%rdi")),
  (15, 6, parse("ja hash_finalize_u243")),
  (21, 3, parse("movq %rsi,%r14")),
  (24, 4, parse("movb $0x80,(%rsi,%rdi,1)")),
  (28, 4, parse("movq 0x60(%rsi),%rax")),
  (32, 4, parse("leaq 0x1(%rax),%rdi")),
  (36, 4, parse("movq %rdi,0x60(%rsi)")),
  (40, 4, parse("cmpq $0x38,%rdi")),
  (44, 2, parse("jbe hash_finalize_u97")),
  (46, 4, parse("cmpq $0x40,%rdi")),
  (50, 6, parse("ja hash_finalize_u228")),
  (56, 5, parse("movl $0x3f,%edx")),
  (61, 3, parse("subq %rax,%rdx")),
  (64, 3, parse("addq %r14,%rdi")),
  (67, 2, parse("xorl %esi,%esi")),
  (69, 6, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (128117)))))]),
  (75, 4, parse("leaq 0x40(%r14),%rdi")),
  (79, 3, parse("movq %r14,%rsi")),
  (82, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-743)))))]),
  (87, 8, parse("movq $0x0,0x60(%r14)")),
  (95, 2, parse("xorl %edi,%edi")),
  (97, 5, parse("movl $0x38,%edx")),
  (102, 3, parse("subq %rdi,%rdx")),
  (105, 3, parse("addq %r14,%rdi")),
  (108, 2, parse("xorl %esi,%esi")),
  (110, 6, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (128076)))))]),
  (116, 4, parse("movq 0x68(%r14),%rax")),
  (120, 4, parse("shlq $0x3,%rax")),
  (124, 3, parse("bswap %rax")),
  (127, 4, parse("movq %rax,0x38(%r14)")),
  (131, 4, parse("leaq 0x40(%r14),%rdi")),
  (135, 3, parse("movq %r14,%rsi")),
  (138, 5, [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-799)))))]),
  (143, 4, parse("movl 0x40(%r14),%eax")),
  (147, 4, parse("movl 0x44(%r14),%ecx")),
  (151, 2, parse("bswap %eax")),
  (153, 2, parse("bswap %ecx")),
  (155, 4, parse("movl 0x48(%r14),%edx")),
  (159, 2, parse("bswap %edx")),
  (161, 4, parse("movl 0x4c(%r14),%esi")),
  (165, 2, parse("bswap %esi")),
  (167, 4, parse("movl 0x50(%r14),%edi")),
  (171, 2, parse("bswap %edi")),
  (173, 4, parse("movl 0x54(%r14),%r8d")),
  (177, 3, parse("bswap %r8d")),
  (180, 4, parse("movl 0x58(%r14),%r9d")),
  (184, 3, parse("bswap %r9d")),
  (187, 4, parse("movl 0x5c(%r14),%r10d")),
  (191, 3, parse("bswap %r10d")),
  (194, 2, parse("movl %eax,(%rbx)")),
  (196, 3, parse("movl %ecx,0x4(%rbx)")),
  (199, 3, parse("movl %edx,0x8(%rbx)")),
  (202, 3, parse("movl %esi,0xc(%rbx)")),
  (205, 3, parse("movl %edi,0x10(%rbx)")),
  (208, 4, parse("movl %r8d,0x14(%rbx)")),
  (212, 4, parse("movl %r9d,0x18(%rbx)")),
  (216, 4, parse("movl %r10d,0x1c(%rbx)")),
  (220, 4, parse("addq $0x8,%rsp")),
  (224, 1, parse("popq %rbx")),
  (225, 2, parse("popq %r14")),
  (227, 1, parse("retq"))]

def labels : List (String × Nat) := [("hash_finalize_u97", 97), ("hash_finalize_u228", 228), ("hash_finalize_u243", 243)]

abbrev CodeAt (e : Executable) (base : Int64) :=
  Hash.CodeAt e base program labels

theorem program_length : program.length = 66 := rfl

end SszX86.Hash.Finalize

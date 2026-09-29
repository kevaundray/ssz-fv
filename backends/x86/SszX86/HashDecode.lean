import SszX86.HashFinalizeImpl
import SszX86.HashCombineImpl
import SszX86.DispatchPush
import SszX86.WordNormalize

namespace SszX86.Hash
open Kraken.X64.Parser

macro "hash_finalize_decoded_step " row:num " at " pc:num " encodedWidth " bytes:num
    " opcodeAST " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := Finalize.program) (n := $row)
     (by rw [Finalize.program_length]; decide)
   have fetched := Hash.step_at _ _ Finalize.program Finalize.labels $hc
     (($pc, $bytes, $instructions) : Row) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [Hash.directives, Finalize.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "hash_finalize_step " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| hash_finalize_decoded_step 0 at 0 encodedWidth 2
      opcodeAST parse("pushq %r14") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| hash_finalize_decoded_step 1 at 2 encodedWidth 1
      opcodeAST parse("pushq %rbx") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| hash_finalize_decoded_step 2 at 3 encodedWidth 1
      opcodeAST parse("pushq %rax") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| hash_finalize_decoded_step 3 at 4 encodedWidth 3
      opcodeAST parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| hash_finalize_decoded_step 4 at 7 encodedWidth 4
      opcodeAST parse("movq 0x60(%rsi),%rdi") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| hash_finalize_decoded_step 5 at 11 encodedWidth 4
      opcodeAST parse("cmpq $0x3f,%rdi") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| hash_finalize_decoded_step 6 at 15 encodedWidth 6
      opcodeAST parse("ja hash_finalize_u243") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| hash_finalize_decoded_step 7 at 21 encodedWidth 3
      opcodeAST parse("movq %rsi,%r14") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| hash_finalize_decoded_step 8 at 24 encodedWidth 4
      opcodeAST parse("movb $0x80,(%rsi,%rdi,1)") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| hash_finalize_decoded_step 9 at 28 encodedWidth 4
      opcodeAST parse("movq 0x60(%rsi),%rax") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| hash_finalize_decoded_step 10 at 32 encodedWidth 4
      opcodeAST parse("leaq 0x1(%rax),%rdi") using $hc)
  if row.getNat == 11 then
    return ← `(tactic| hash_finalize_decoded_step 11 at 36 encodedWidth 4
      opcodeAST parse("movq %rdi,0x60(%rsi)") using $hc)
  if row.getNat == 12 then
    return ← `(tactic| hash_finalize_decoded_step 12 at 40 encodedWidth 4
      opcodeAST parse("cmpq $0x38,%rdi") using $hc)
  if row.getNat == 13 then
    return ← `(tactic| hash_finalize_decoded_step 13 at 44 encodedWidth 2
      opcodeAST parse("jbe hash_finalize_u97") using $hc)
  if row.getNat == 14 then
    return ← `(tactic| hash_finalize_decoded_step 14 at 46 encodedWidth 4
      opcodeAST parse("cmpq $0x40,%rdi") using $hc)
  if row.getNat == 15 then
    return ← `(tactic| hash_finalize_decoded_step 15 at 50 encodedWidth 6
      opcodeAST parse("ja hash_finalize_u228") using $hc)
  if row.getNat == 16 then
    return ← `(tactic| hash_finalize_decoded_step 16 at 56 encodedWidth 5
      opcodeAST parse("movl $0x3f,%edx") using $hc)
  if row.getNat == 17 then
    return ← `(tactic| hash_finalize_decoded_step 17 at 61 encodedWidth 3
      opcodeAST parse("subq %rax,%rdx") using $hc)
  if row.getNat == 18 then
    return ← `(tactic| hash_finalize_decoded_step 18 at 64 encodedWidth 3
      opcodeAST parse("addq %r14,%rdi") using $hc)
  if row.getNat == 19 then
    return ← `(tactic| hash_finalize_decoded_step 19 at 67 encodedWidth 2
      opcodeAST parse("xorl %esi,%esi") using $hc)
  if row.getNat == 20 then
    return ← `(tactic| hash_finalize_decoded_step 20 at 69 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (128117)))))] using $hc)
  if row.getNat == 21 then
    return ← `(tactic| hash_finalize_decoded_step 21 at 75 encodedWidth 4
      opcodeAST parse("leaq 0x40(%r14),%rdi") using $hc)
  if row.getNat == 22 then
    return ← `(tactic| hash_finalize_decoded_step 22 at 79 encodedWidth 3
      opcodeAST parse("movq %r14,%rsi") using $hc)
  if row.getNat == 23 then
    return ← `(tactic| hash_finalize_decoded_step 23 at 82 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-743)))))] using $hc)
  if row.getNat == 24 then
    return ← `(tactic| hash_finalize_decoded_step 24 at 87 encodedWidth 8
      opcodeAST parse("movq $0x0,0x60(%r14)") using $hc)
  if row.getNat == 25 then
    return ← `(tactic| hash_finalize_decoded_step 25 at 95 encodedWidth 2
      opcodeAST parse("xorl %edi,%edi") using $hc)
  if row.getNat == 26 then
    return ← `(tactic| hash_finalize_decoded_step 26 at 97 encodedWidth 5
      opcodeAST parse("movl $0x38,%edx") using $hc)
  if row.getNat == 27 then
    return ← `(tactic| hash_finalize_decoded_step 27 at 102 encodedWidth 3
      opcodeAST parse("subq %rdi,%rdx") using $hc)
  if row.getNat == 28 then
    return ← `(tactic| hash_finalize_decoded_step 28 at 105 encodedWidth 3
      opcodeAST parse("addq %r14,%rdi") using $hc)
  if row.getNat == 29 then
    return ← `(tactic| hash_finalize_decoded_step 29 at 108 encodedWidth 2
      opcodeAST parse("xorl %esi,%esi") using $hc)
  if row.getNat == 30 then
    return ← `(tactic| hash_finalize_decoded_step 30 at 110 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (128076)))))] using $hc)
  if row.getNat == 31 then
    return ← `(tactic| hash_finalize_decoded_step 31 at 116 encodedWidth 4
      opcodeAST parse("movq 0x68(%r14),%rax") using $hc)
  if row.getNat == 32 then
    return ← `(tactic| hash_finalize_decoded_step 32 at 120 encodedWidth 4
      opcodeAST parse("shlq $0x3,%rax") using $hc)
  if row.getNat == 33 then
    return ← `(tactic| hash_finalize_decoded_step 33 at 124 encodedWidth 3
      opcodeAST parse("bswap %rax") using $hc)
  if row.getNat == 34 then
    return ← `(tactic| hash_finalize_decoded_step 34 at 127 encodedWidth 4
      opcodeAST parse("movq %rax,0x38(%r14)") using $hc)
  if row.getNat == 35 then
    return ← `(tactic| hash_finalize_decoded_step 35 at 131 encodedWidth 4
      opcodeAST parse("leaq 0x40(%r14),%rdi") using $hc)
  if row.getNat == 36 then
    return ← `(tactic| hash_finalize_decoded_step 36 at 135 encodedWidth 3
      opcodeAST parse("movq %r14,%rsi") using $hc)
  if row.getNat == 37 then
    return ← `(tactic| hash_finalize_decoded_step 37 at 138 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-799)))))] using $hc)
  if row.getNat == 38 then
    return ← `(tactic| hash_finalize_decoded_step 38 at 143 encodedWidth 4
      opcodeAST parse("movl 0x40(%r14),%eax") using $hc)
  if row.getNat == 39 then
    return ← `(tactic| hash_finalize_decoded_step 39 at 147 encodedWidth 4
      opcodeAST parse("movl 0x44(%r14),%ecx") using $hc)
  if row.getNat == 40 then
    return ← `(tactic| hash_finalize_decoded_step 40 at 151 encodedWidth 2
      opcodeAST parse("bswap %eax") using $hc)
  if row.getNat == 41 then
    return ← `(tactic| hash_finalize_decoded_step 41 at 153 encodedWidth 2
      opcodeAST parse("bswap %ecx") using $hc)
  if row.getNat == 42 then
    return ← `(tactic| hash_finalize_decoded_step 42 at 155 encodedWidth 4
      opcodeAST parse("movl 0x48(%r14),%edx") using $hc)
  if row.getNat == 43 then
    return ← `(tactic| hash_finalize_decoded_step 43 at 159 encodedWidth 2
      opcodeAST parse("bswap %edx") using $hc)
  if row.getNat == 44 then
    return ← `(tactic| hash_finalize_decoded_step 44 at 161 encodedWidth 4
      opcodeAST parse("movl 0x4c(%r14),%esi") using $hc)
  if row.getNat == 45 then
    return ← `(tactic| hash_finalize_decoded_step 45 at 165 encodedWidth 2
      opcodeAST parse("bswap %esi") using $hc)
  if row.getNat == 46 then
    return ← `(tactic| hash_finalize_decoded_step 46 at 167 encodedWidth 4
      opcodeAST parse("movl 0x50(%r14),%edi") using $hc)
  if row.getNat == 47 then
    return ← `(tactic| hash_finalize_decoded_step 47 at 171 encodedWidth 2
      opcodeAST parse("bswap %edi") using $hc)
  if row.getNat == 48 then
    return ← `(tactic| hash_finalize_decoded_step 48 at 173 encodedWidth 4
      opcodeAST parse("movl 0x54(%r14),%r8d") using $hc)
  if row.getNat == 49 then
    return ← `(tactic| hash_finalize_decoded_step 49 at 177 encodedWidth 3
      opcodeAST parse("bswap %r8d") using $hc)
  if row.getNat == 50 then
    return ← `(tactic| hash_finalize_decoded_step 50 at 180 encodedWidth 4
      opcodeAST parse("movl 0x58(%r14),%r9d") using $hc)
  if row.getNat == 51 then
    return ← `(tactic| hash_finalize_decoded_step 51 at 184 encodedWidth 3
      opcodeAST parse("bswap %r9d") using $hc)
  if row.getNat == 52 then
    return ← `(tactic| hash_finalize_decoded_step 52 at 187 encodedWidth 4
      opcodeAST parse("movl 0x5c(%r14),%r10d") using $hc)
  if row.getNat == 53 then
    return ← `(tactic| hash_finalize_decoded_step 53 at 191 encodedWidth 3
      opcodeAST parse("bswap %r10d") using $hc)
  if row.getNat == 54 then
    return ← `(tactic| hash_finalize_decoded_step 54 at 194 encodedWidth 2
      opcodeAST parse("movl %eax,(%rbx)") using $hc)
  if row.getNat == 55 then
    return ← `(tactic| hash_finalize_decoded_step 55 at 196 encodedWidth 3
      opcodeAST parse("movl %ecx,0x4(%rbx)") using $hc)
  if row.getNat == 56 then
    return ← `(tactic| hash_finalize_decoded_step 56 at 199 encodedWidth 3
      opcodeAST parse("movl %edx,0x8(%rbx)") using $hc)
  if row.getNat == 57 then
    return ← `(tactic| hash_finalize_decoded_step 57 at 202 encodedWidth 3
      opcodeAST parse("movl %esi,0xc(%rbx)") using $hc)
  if row.getNat == 58 then
    return ← `(tactic| hash_finalize_decoded_step 58 at 205 encodedWidth 3
      opcodeAST parse("movl %edi,0x10(%rbx)") using $hc)
  if row.getNat == 59 then
    return ← `(tactic| hash_finalize_decoded_step 59 at 208 encodedWidth 4
      opcodeAST parse("movl %r8d,0x14(%rbx)") using $hc)
  if row.getNat == 60 then
    return ← `(tactic| hash_finalize_decoded_step 60 at 212 encodedWidth 4
      opcodeAST parse("movl %r9d,0x18(%rbx)") using $hc)
  if row.getNat == 61 then
    return ← `(tactic| hash_finalize_decoded_step 61 at 216 encodedWidth 4
      opcodeAST parse("movl %r10d,0x1c(%rbx)") using $hc)
  if row.getNat == 62 then
    return ← `(tactic| hash_finalize_decoded_step 62 at 220 encodedWidth 4
      opcodeAST parse("addq $0x8,%rsp") using $hc)
  if row.getNat == 63 then
    return ← `(tactic| hash_finalize_decoded_step 63 at 224 encodedWidth 1
      opcodeAST parse("popq %rbx") using $hc)
  if row.getNat == 64 then
    return ← `(tactic| hash_finalize_decoded_step 64 at 225 encodedWidth 2
      opcodeAST parse("popq %r14") using $hc)
  if row.getNat == 65 then
    return ← `(tactic| hash_finalize_decoded_step 65 at 227 encodedWidth 1
      opcodeAST parse("retq") using $hc)
  Lean.Macro.throwError "unknown SHA instruction row"

macro "hash_combine_decoded_step " row:num " at " pc:num " encodedWidth " bytes:num
    " opcodeAST " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := Combine.program) (n := $row)
     (by rw [Combine.program_length]; decide)
   have fetched := Hash.step_at _ _ Combine.program Combine.labels $hc
     (($pc, $bytes, $instructions) : Row) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [Hash.directives, Combine.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "hash_combine_step " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| hash_combine_decoded_step 0 at 0 encodedWidth 1
      opcodeAST parse("pushq %rbp") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| hash_combine_decoded_step 1 at 1 encodedWidth 2
      opcodeAST parse("pushq %r15") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| hash_combine_decoded_step 2 at 3 encodedWidth 2
      opcodeAST parse("pushq %r14") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| hash_combine_decoded_step 3 at 5 encodedWidth 2
      opcodeAST parse("pushq %r13") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| hash_combine_decoded_step 4 at 7 encodedWidth 2
      opcodeAST parse("pushq %r12") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| hash_combine_decoded_step 5 at 9 encodedWidth 1
      opcodeAST parse("pushq %rbx") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| hash_combine_decoded_step 6 at 10 encodedWidth 4
      opcodeAST parse("subq $0x78,%rsp") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| hash_combine_decoded_step 7 at 14 encodedWidth 3
      opcodeAST parse("movq %r8,%r14") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| hash_combine_decoded_step 8 at 17 encodedWidth 3
      opcodeAST parse("movq %rcx,%r15") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| hash_combine_decoded_step 9 at 20 encodedWidth 3
      opcodeAST parse("movq %rdx,%r13") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| hash_combine_decoded_step 10 at 23 encodedWidth 3
      opcodeAST parse("movq %rsi,%rbp") using $hc)
  if row.getNat == 11 then
    return ← `(tactic| hash_combine_decoded_step 11 at 26 encodedWidth 3
      opcodeAST parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 12 then
    return ← `(tactic| hash_combine_decoded_step 12 at 29 encodedWidth 9
      opcodeAST parse("movq $0x0,0x40(%rsp)") using $hc)
  if row.getNat == 13 then
    return ← `(tactic| hash_combine_decoded_step 13 at 38 encodedWidth 9
      opcodeAST parse("movq $0x0,0x38(%rsp)") using $hc)
  if row.getNat == 14 then
    return ← `(tactic| hash_combine_decoded_step 14 at 47 encodedWidth 9
      opcodeAST parse("movq $0x0,0x30(%rsp)") using $hc)
  if row.getNat == 15 then
    return ← `(tactic| hash_combine_decoded_step 15 at 56 encodedWidth 9
      opcodeAST parse("movq $0x0,0x28(%rsp)") using $hc)
  if row.getNat == 16 then
    return ← `(tactic| hash_combine_decoded_step 16 at 65 encodedWidth 9
      opcodeAST parse("movq $0x0,0x20(%rsp)") using $hc)
  if row.getNat == 17 then
    return ← `(tactic| hash_combine_decoded_step 17 at 74 encodedWidth 9
      opcodeAST parse("movq $0x0,0x18(%rsp)") using $hc)
  if row.getNat == 18 then
    return ← `(tactic| hash_combine_decoded_step 18 at 83 encodedWidth 9
      opcodeAST parse("movq $0x0,0x10(%rsp)") using $hc)
  if row.getNat == 19 then
    return ← `(tactic| hash_combine_decoded_step 19 at 92 encodedWidth 9
      opcodeAST parse("movq $0x0,0x8(%rsp)") using $hc)
  if row.getNat == 20 then
    return ← `(tactic| hash_combine_decoded_step 20 at 101 encodedWidth 5
      opcodeAST parse("leaq 0x48(%rsp),%r12") using $hc)
  if row.getNat == 21 then
    return ← `(tactic| hash_combine_decoded_step 21 at 106 encodedWidth 10
      opcodeAST parse("movabsq $0xbb67ae856a09e667,%rax") using $hc)
  if row.getNat == 22 then
    return ← `(tactic| hash_combine_decoded_step 22 at 116 encodedWidth 5
      opcodeAST parse("movq %rax,0x48(%rsp)") using $hc)
  if row.getNat == 23 then
    return ← `(tactic| hash_combine_decoded_step 23 at 121 encodedWidth 10
      opcodeAST parse("movabsq $0xa54ff53a3c6ef372,%rax") using $hc)
  if row.getNat == 24 then
    return ← `(tactic| hash_combine_decoded_step 24 at 131 encodedWidth 5
      opcodeAST parse("movq %rax,0x50(%rsp)") using $hc)
  if row.getNat == 25 then
    return ← `(tactic| hash_combine_decoded_step 25 at 136 encodedWidth 10
      opcodeAST parse("movabsq $0x9b05688c510e527f,%rax") using $hc)
  if row.getNat == 26 then
    return ← `(tactic| hash_combine_decoded_step 26 at 146 encodedWidth 5
      opcodeAST parse("movq %rax,0x58(%rsp)") using $hc)
  if row.getNat == 27 then
    return ← `(tactic| hash_combine_decoded_step 27 at 151 encodedWidth 10
      opcodeAST parse("movabsq $0x5be0cd191f83d9ab,%rax") using $hc)
  if row.getNat == 28 then
    return ← `(tactic| hash_combine_decoded_step 28 at 161 encodedWidth 5
      opcodeAST parse("movq %rax,0x60(%rsp)") using $hc)
  if row.getNat == 29 then
    return ← `(tactic| hash_combine_decoded_step 29 at 166 encodedWidth 9
      opcodeAST parse("movq $0x0,0x68(%rsp)") using $hc)
  if row.getNat == 30 then
    return ← `(tactic| hash_combine_decoded_step 30 at 175 encodedWidth 5
      opcodeAST parse("movq %rdx,0x70(%rsp)") using $hc)
  if row.getNat == 31 then
    return ← `(tactic| hash_combine_decoded_step 31 at 180 encodedWidth 4
      opcodeAST parse("cmpq $0x40,%rdx") using $hc)
  if row.getNat == 32 then
    return ← `(tactic| hash_combine_decoded_step 32 at 184 encodedWidth 2
      opcodeAST parse("jb hash_combine_u217") using $hc)
  if row.getNat == 33 then
    return ← `(tactic| hash_combine_decoded_step 33 at 186 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.nop 6))] using $hc)
  if row.getNat == 34 then
    return ← `(tactic| hash_combine_decoded_step 34 at 192 encodedWidth 3
      opcodeAST parse("movq %r12,%rdi") using $hc)
  if row.getNat == 35 then
    return ← `(tactic| hash_combine_decoded_step 35 at 195 encodedWidth 3
      opcodeAST parse("movq %rbp,%rsi") using $hc)
  if row.getNat == 36 then
    return ← `(tactic| hash_combine_decoded_step 36 at 198 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-1115)))))] using $hc)
  if row.getNat == 37 then
    return ← `(tactic| hash_combine_decoded_step 37 at 203 encodedWidth 4
      opcodeAST parse("addq $0xffffffffffffffc0,%r13") using $hc)
  if row.getNat == 38 then
    return ← `(tactic| hash_combine_decoded_step 38 at 207 encodedWidth 4
      opcodeAST parse("addq $0x40,%rbp") using $hc)
  if row.getNat == 39 then
    return ← `(tactic| hash_combine_decoded_step 39 at 211 encodedWidth 4
      opcodeAST parse("cmpq $0x3f,%r13") using $hc)
  if row.getNat == 40 then
    return ← `(tactic| hash_combine_decoded_step 40 at 215 encodedWidth 2
      opcodeAST parse("ja hash_combine_u192") using $hc)
  if row.getNat == 41 then
    return ← `(tactic| hash_combine_decoded_step 41 at 217 encodedWidth 5
      opcodeAST parse("leaq 0x8(%rsp),%rdi") using $hc)
  if row.getNat == 42 then
    return ← `(tactic| hash_combine_decoded_step 42 at 222 encodedWidth 3
      opcodeAST parse("movq %rbp,%rsi") using $hc)
  if row.getNat == 43 then
    return ← `(tactic| hash_combine_decoded_step 43 at 225 encodedWidth 3
      opcodeAST parse("movq %r13,%rdx") using $hc)
  if row.getNat == 44 then
    return ← `(tactic| hash_combine_decoded_step 44 at 228 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (127638)))))] using $hc)
  if row.getNat == 45 then
    return ← `(tactic| hash_combine_decoded_step 45 at 234 encodedWidth 5
      opcodeAST parse("movq %r13,0x68(%rsp)") using $hc)
  if row.getNat == 46 then
    return ← `(tactic| hash_combine_decoded_step 46 at 239 encodedWidth 5
      opcodeAST parse("addq %r14,0x70(%rsp)") using $hc)
  if row.getNat == 47 then
    return ← `(tactic| hash_combine_decoded_step 47 at 244 encodedWidth 3
      opcodeAST parse("testq %r13,%r13") using $hc)
  if row.getNat == 48 then
    return ← `(tactic| hash_combine_decoded_step 48 at 247 encodedWidth 2
      opcodeAST parse("je hash_combine_u331") using $hc)
  if row.getNat == 49 then
    return ← `(tactic| hash_combine_decoded_step 49 at 249 encodedWidth 5
      opcodeAST parse("movl $0x40,%ebp") using $hc)
  if row.getNat == 50 then
    return ← `(tactic| hash_combine_decoded_step 50 at 254 encodedWidth 3
      opcodeAST parse("subq %r13,%rbp") using $hc)
  if row.getNat == 51 then
    return ← `(tactic| hash_combine_decoded_step 51 at 257 encodedWidth 3
      opcodeAST parse("cmpq %rbp,%r14") using $hc)
  if row.getNat == 52 then
    return ← `(tactic| hash_combine_decoded_step 52 at 260 encodedWidth 4
      opcodeAST [.instr (.regular .W64 .W64 (.cmovcc .c (.low .rbp .W64) (.reg (.low .r14 .W64))))] using $hc)
  if row.getNat == 53 then
    return ← `(tactic| hash_combine_decoded_step 53 at 264 encodedWidth 4
      opcodeAST parse("leaq (%rsp,%r13,1),%rdi") using $hc)
  if row.getNat == 54 then
    return ← `(tactic| hash_combine_decoded_step 54 at 268 encodedWidth 4
      opcodeAST parse("addq $0x8,%rdi") using $hc)
  if row.getNat == 55 then
    return ← `(tactic| hash_combine_decoded_step 55 at 272 encodedWidth 3
      opcodeAST parse("movq %r15,%rsi") using $hc)
  if row.getNat == 56 then
    return ← `(tactic| hash_combine_decoded_step 56 at 275 encodedWidth 3
      opcodeAST parse("movq %rbp,%rdx") using $hc)
  if row.getNat == 57 then
    return ← `(tactic| hash_combine_decoded_step 57 at 278 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (127588)))))] using $hc)
  if row.getNat == 58 then
    return ← `(tactic| hash_combine_decoded_step 58 at 284 encodedWidth 5
      opcodeAST parse("movq 0x68(%rsp),%rax") using $hc)
  if row.getNat == 59 then
    return ← `(tactic| hash_combine_decoded_step 59 at 289 encodedWidth 3
      opcodeAST parse("addq %rbp,%rax") using $hc)
  if row.getNat == 60 then
    return ← `(tactic| hash_combine_decoded_step 60 at 292 encodedWidth 5
      opcodeAST parse("movq %rax,0x68(%rsp)") using $hc)
  if row.getNat == 61 then
    return ← `(tactic| hash_combine_decoded_step 61 at 297 encodedWidth 4
      opcodeAST parse("cmpq $0x40,%rax") using $hc)
  if row.getNat == 62 then
    return ← `(tactic| hash_combine_decoded_step 62 at 301 encodedWidth 2
      opcodeAST parse("jb hash_combine_u399") using $hc)
  if row.getNat == 63 then
    return ← `(tactic| hash_combine_decoded_step 63 at 303 encodedWidth 3
      opcodeAST parse("addq %rbp,%r15") using $hc)
  if row.getNat == 64 then
    return ← `(tactic| hash_combine_decoded_step 64 at 306 encodedWidth 3
      opcodeAST parse("subq %rbp,%r14") using $hc)
  if row.getNat == 65 then
    return ← `(tactic| hash_combine_decoded_step 65 at 309 encodedWidth 5
      opcodeAST parse("leaq 0x8(%rsp),%rsi") using $hc)
  if row.getNat == 66 then
    return ← `(tactic| hash_combine_decoded_step 66 at 314 encodedWidth 3
      opcodeAST parse("movq %r12,%rdi") using $hc)
  if row.getNat == 67 then
    return ← `(tactic| hash_combine_decoded_step 67 at 317 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-1234)))))] using $hc)
  if row.getNat == 68 then
    return ← `(tactic| hash_combine_decoded_step 68 at 322 encodedWidth 9
      opcodeAST parse("movq $0x0,0x68(%rsp)") using $hc)
  if row.getNat == 69 then
    return ← `(tactic| hash_combine_decoded_step 69 at 331 encodedWidth 4
      opcodeAST parse("cmpq $0x40,%r14") using $hc)
  if row.getNat == 70 then
    return ← `(tactic| hash_combine_decoded_step 70 at 335 encodedWidth 2
      opcodeAST parse("jb hash_combine_u377") using $hc)
  if row.getNat == 71 then
    return ← `(tactic| hash_combine_decoded_step 71 at 337 encodedWidth 10
      opcodeAST [.instr (.regular .W64 .W64 (.nop 10))] using $hc)
  if row.getNat == 72 then
    return ← `(tactic| hash_combine_decoded_step 72 at 347 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.nop 5))] using $hc)
  if row.getNat == 73 then
    return ← `(tactic| hash_combine_decoded_step 73 at 352 encodedWidth 3
      opcodeAST parse("movq %r12,%rdi") using $hc)
  if row.getNat == 74 then
    return ← `(tactic| hash_combine_decoded_step 74 at 355 encodedWidth 3
      opcodeAST parse("movq %r15,%rsi") using $hc)
  if row.getNat == 75 then
    return ← `(tactic| hash_combine_decoded_step 75 at 358 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-1275)))))] using $hc)
  if row.getNat == 76 then
    return ← `(tactic| hash_combine_decoded_step 76 at 363 encodedWidth 4
      opcodeAST parse("addq $0xffffffffffffffc0,%r14") using $hc)
  if row.getNat == 77 then
    return ← `(tactic| hash_combine_decoded_step 77 at 367 encodedWidth 4
      opcodeAST parse("addq $0x40,%r15") using $hc)
  if row.getNat == 78 then
    return ← `(tactic| hash_combine_decoded_step 78 at 371 encodedWidth 4
      opcodeAST parse("cmpq $0x3f,%r14") using $hc)
  if row.getNat == 79 then
    return ← `(tactic| hash_combine_decoded_step 79 at 375 encodedWidth 2
      opcodeAST parse("ja hash_combine_u352") using $hc)
  if row.getNat == 80 then
    return ← `(tactic| hash_combine_decoded_step 80 at 377 encodedWidth 5
      opcodeAST parse("leaq 0x8(%rsp),%rdi") using $hc)
  if row.getNat == 81 then
    return ← `(tactic| hash_combine_decoded_step 81 at 382 encodedWidth 3
      opcodeAST parse("movq %r15,%rsi") using $hc)
  if row.getNat == 82 then
    return ← `(tactic| hash_combine_decoded_step 82 at 385 encodedWidth 3
      opcodeAST parse("movq %r14,%rdx") using $hc)
  if row.getNat == 83 then
    return ← `(tactic| hash_combine_decoded_step 83 at 388 encodedWidth 6
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (127478)))))] using $hc)
  if row.getNat == 84 then
    return ← `(tactic| hash_combine_decoded_step 84 at 394 encodedWidth 5
      opcodeAST parse("movq %r14,0x68(%rsp)") using $hc)
  if row.getNat == 85 then
    return ← `(tactic| hash_combine_decoded_step 85 at 399 encodedWidth 5
      opcodeAST parse("leaq 0x8(%rsp),%rsi") using $hc)
  if row.getNat == 86 then
    return ← `(tactic| hash_combine_decoded_step 86 at 404 encodedWidth 3
      opcodeAST parse("movq %rbx,%rdi") using $hc)
  if row.getNat == 87 then
    return ← `(tactic| hash_combine_decoded_step 87 at 407 encodedWidth 5
      opcodeAST [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-668)))))] using $hc)
  if row.getNat == 88 then
    return ← `(tactic| hash_combine_decoded_step 88 at 412 encodedWidth 4
      opcodeAST parse("addq $0x78,%rsp") using $hc)
  if row.getNat == 89 then
    return ← `(tactic| hash_combine_decoded_step 89 at 416 encodedWidth 1
      opcodeAST parse("popq %rbx") using $hc)
  if row.getNat == 90 then
    return ← `(tactic| hash_combine_decoded_step 90 at 417 encodedWidth 2
      opcodeAST parse("popq %r12") using $hc)
  if row.getNat == 91 then
    return ← `(tactic| hash_combine_decoded_step 91 at 419 encodedWidth 2
      opcodeAST parse("popq %r13") using $hc)
  if row.getNat == 92 then
    return ← `(tactic| hash_combine_decoded_step 92 at 421 encodedWidth 2
      opcodeAST parse("popq %r14") using $hc)
  if row.getNat == 93 then
    return ← `(tactic| hash_combine_decoded_step 93 at 423 encodedWidth 2
      opcodeAST parse("popq %r15") using $hc)
  if row.getNat == 94 then
    return ← `(tactic| hash_combine_decoded_step 94 at 425 encodedWidth 1
      opcodeAST parse("popq %rbp") using $hc)
  if row.getNat == 95 then
    return ← `(tactic| hash_combine_decoded_step 95 at 426 encodedWidth 1
      opcodeAST parse("retq") using $hc)
  Lean.Macro.throwError "unknown SHA instruction row"

end SszX86.Hash

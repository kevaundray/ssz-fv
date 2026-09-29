import SszX86.CodecMeasureFixedImpl
import SszX86.DelimitedCore

namespace SszX86.CodecMeasureFixed
open Kraken.X64.Parser
open BoolCodec UintCodec

macro "codec_measure_fixed_decoded_step " row:num " at " pc:num " width " bytes:num
    " opcode " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.CodecMeasureFixed.program) (n := $row)
     (by rw [SszX86.CodecMeasureFixed.program_length]; decide)
   have fetched := SszX86.CodecMeasureFixed.step_at _ _ $hc
     (($pc, $bytes, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecMeasureFixed.directives, SszX86.CodecMeasureFixed.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "codec_measure_fixed_step_chunk0 " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| codec_measure_fixed_decoded_step 0 at 0 width 1 opcode
      parse("pushq %rbp") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| codec_measure_fixed_decoded_step 1 at 1 width 2 opcode
      parse("pushq %r15") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| codec_measure_fixed_decoded_step 2 at 3 width 2 opcode
      parse("pushq %r14") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| codec_measure_fixed_decoded_step 3 at 5 width 2 opcode
      parse("pushq %r13") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| codec_measure_fixed_decoded_step 4 at 7 width 2 opcode
      parse("pushq %r12") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| codec_measure_fixed_decoded_step 5 at 9 width 1 opcode
      parse("pushq %rbx") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| codec_measure_fixed_decoded_step 6 at 10 width 4 opcode
      parse("subq $0x58,%rsp") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| codec_measure_fixed_decoded_step 7 at 14 width 3 opcode
      parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| codec_measure_fixed_decoded_step 8 at 17 width 3 opcode
      parse("movq (%rsi),%rax") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| codec_measure_fixed_decoded_step 9 at 20 width 4 opcode
      parse("cmpq $0xb,%rax") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| codec_measure_fixed_decoded_step 10 at 24 width 6 opcode
      parse("ja codec_measure_fixed_u680") using $hc)
  if row.getNat == 11 then
    return ← `(tactic| codec_measure_fixed_decoded_step 11 at 30 width 3 opcode
      parse("movq %rdx,%r12") using $hc)
  if row.getNat == 12 then
    return ← `(tactic| codec_measure_fixed_decoded_step 12 at 33 width 7 opcode
      [.instr (.regular .W64 .W64 (.lea .rcx {base := some .rip, idx := none, disp := .int64 (-116248)}))] using $hc)
  if row.getNat == 13 then
    return ← `(tactic| codec_measure_fixed_decoded_step 13 at 40 width 4 opcode
      [.instr (.regular .W64 .W64 (.movsx (.reg .rax) (.mem (w := .W32) {base := some (.reg .rcx), idx := some ⟨.rax, .W32⟩})))] using $hc)
  if row.getNat == 14 then
    return ← `(tactic| codec_measure_fixed_decoded_step 14 at 44 width 3 opcode
      parse("addq %rcx,%rax") using $hc)
  if row.getNat == 15 then
    return ← `(tactic| codec_measure_fixed_decoded_step 15 at 47 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.reg .rax)))] using $hc)
  if row.getNat == 16 then
    return ← `(tactic| codec_measure_fixed_decoded_step 16 at 49 width 4 opcode
      parse("movq 0x8(%rsi),%r14") using $hc)
  if row.getNat == 17 then
    return ← `(tactic| codec_measure_fixed_decoded_step 17 at 53 width 4 opcode
      parse("movq 0x10(%rsi),%r15") using $hc)
  if row.getNat == 18 then
    return ← `(tactic| codec_measure_fixed_decoded_step 18 at 57 width 5 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (209)))))] using $hc)
  if row.getNat == 19 then
    return ← `(tactic| codec_measure_fixed_decoded_step 19 at 62 width 5 opcode
      parse("movl $0x8,%eax") using $hc)
  if row.getNat == 20 then
    return ← `(tactic| codec_measure_fixed_decoded_step 20 at 67 width 5 opcode
      parse("movq 0x8(%rsi,%rax,1),%rcx") using $hc)
  if row.getNat == 21 then
    return ← `(tactic| codec_measure_fixed_decoded_step 21 at 72 width 3 opcode
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 22 then
    return ← `(tactic| codec_measure_fixed_decoded_step 22 at 75 width 6 opcode
      parse("je codec_measure_fixed_u254") using $hc)
  if row.getNat == 23 then
    return ← `(tactic| codec_measure_fixed_decoded_step 23 at 81 width 4 opcode
      parse("movq (%rsi,%rax,1),%rax") using $hc)
  if row.getNat == 24 then
    return ← `(tactic| codec_measure_fixed_decoded_step 24 at 85 width 5 opcode
      parse("movq %rax,0x50(%rsp)") using $hc)
  if row.getNat == 25 then
    return ← `(tactic| codec_measure_fixed_decoded_step 25 at 90 width 4 opcode
      parse("shlq $0x3,%rcx") using $hc)
  if row.getNat == 26 then
    return ← `(tactic| codec_measure_fixed_decoded_step 26 at 94 width 4 opcode
      parse("leaq (%rcx,%rcx,2),%rax") using $hc)
  if row.getNat == 27 then
    return ← `(tactic| codec_measure_fixed_decoded_step 27 at 98 width 5 opcode
      parse("movq %rax,0x48(%rsp)") using $hc)
  if row.getNat == 28 then
    return ← `(tactic| codec_measure_fixed_decoded_step 28 at 103 width 2 opcode
      parse("xorl %ebp,%ebp") using $hc)
  if row.getNat == 29 then
    return ← `(tactic| codec_measure_fixed_decoded_step 29 at 105 width 3 opcode
      parse("movq %rsp,%r13") using $hc)
  if row.getNat == 30 then
    return ← `(tactic| codec_measure_fixed_decoded_step 30 at 108 width 3 opcode
      parse("xorl %r14d,%r14d") using $hc)
  if row.getNat == 31 then
    return ← `(tactic| codec_measure_fixed_decoded_step 31 at 111 width 3 opcode
      parse("xorl %r15d,%r15d") using $hc)
  if row.getNat == 32 then
    return ← `(tactic| codec_measure_fixed_decoded_step 32 at 114 width 10 opcode
      [.instr (.regular .W64 .W64 (.nop 10))] using $hc)
  if row.getNat == 33 then
    return ← `(tactic| codec_measure_fixed_decoded_step 33 at 124 width 4 opcode
      [.instr (.regular .W64 .W64 (.nop 4))] using $hc)
  if row.getNat == 34 then
    return ← `(tactic| codec_measure_fixed_decoded_step 34 at 128 width 5 opcode
      parse("movq 0x50(%rsp),%rax") using $hc)
  if row.getNat == 35 then
    return ← `(tactic| codec_measure_fixed_decoded_step 35 at 133 width 5 opcode
      parse("movq 0x10(%rax,%rbp,1),%rsi") using $hc)
  if row.getNat == 36 then
    return ← `(tactic| codec_measure_fixed_decoded_step 36 at 138 width 3 opcode
      parse("movq %r13,%rdi") using $hc)
  if row.getNat == 37 then
    return ← `(tactic| codec_measure_fixed_decoded_step 37 at 141 width 3 opcode
      parse("movq %r12,%rdx") using $hc)
  if row.getNat == 38 then
    return ← `(tactic| codec_measure_fixed_decoded_step 38 at 144 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-149)))))] using $hc)
  if row.getNat == 39 then
    return ← `(tactic| codec_measure_fixed_decoded_step 39 at 149 width 4 opcode
      parse("movl 0x40(%rsp),%eax") using $hc)
  if row.getNat == 40 then
    return ← `(tactic| codec_measure_fixed_decoded_step 40 at 153 width 4 opcode
      parse("movq (%rsp),%rdx") using $hc)
  if row.getNat == 41 then
    return ← `(tactic| codec_measure_fixed_decoded_step 41 at 157 width 5 opcode
      parse("movq 0x8(%rsp),%rcx") using $hc)
  if row.getNat == 42 then
    return ← `(tactic| codec_measure_fixed_decoded_step 42 at 162 width 5 opcode
      parse("movq 0x10(%rsp),%r8") using $hc)
  if row.getNat == 43 then
    return ← `(tactic| codec_measure_fixed_decoded_step 43 at 167 width 2 opcode
      parse("testl %eax,%eax") using $hc)
  if row.getNat == 44 then
    return ← `(tactic| codec_measure_fixed_decoded_step 44 at 169 width 6 opcode
      parse("jne codec_measure_fixed_u709") using $hc)
  if row.getNat == 45 then
    return ← `(tactic| codec_measure_fixed_decoded_step 45 at 175 width 3 opcode
      parse("testb $0x1,%dl") using $hc)
  if row.getNat == 46 then
    return ← `(tactic| codec_measure_fixed_decoded_step 46 at 178 width 6 opcode
      parse("je codec_measure_fixed_u680") using $hc)
  if row.getNat == 47 then
    return ← `(tactic| codec_measure_fixed_decoded_step 47 at 184 width 3 opcode
      parse("movq %r13,%rdi") using $hc)
  if row.getNat == 48 then
    return ← `(tactic| codec_measure_fixed_decoded_step 48 at 187 width 3 opcode
      parse("movq %r14,%rsi") using $hc)
  if row.getNat == 49 then
    return ← `(tactic| codec_measure_fixed_decoded_step 49 at 190 width 3 opcode
      parse("movq %r15,%rdx") using $hc)
  if row.getNat == 50 then
    return ← `(tactic| codec_measure_fixed_decoded_step 50 at 193 width 3 opcode
      parse("movq %r12,%r9") using $hc)
  if row.getNat == 51 then
    return ← `(tactic| codec_measure_fixed_decoded_step 51 at 196 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-64873)))))] using $hc)
  if row.getNat == 52 then
    return ← `(tactic| codec_measure_fixed_decoded_step 52 at 201 width 4 opcode
      parse("movl 0x40(%rsp),%eax") using $hc)
  if row.getNat == 53 then
    return ← `(tactic| codec_measure_fixed_decoded_step 53 at 205 width 4 opcode
      parse("movq (%rsp),%r14") using $hc)
  if row.getNat == 54 then
    return ← `(tactic| codec_measure_fixed_decoded_step 54 at 209 width 5 opcode
      parse("movq 0x8(%rsp),%r15") using $hc)
  if row.getNat == 55 then
    return ← `(tactic| codec_measure_fixed_decoded_step 55 at 214 width 2 opcode
      parse("testl %eax,%eax") using $hc)
  if row.getNat == 56 then
    return ← `(tactic| codec_measure_fixed_decoded_step 56 at 216 width 6 opcode
      parse("jne codec_measure_fixed_u607") using $hc)
  if row.getNat == 57 then
    return ← `(tactic| codec_measure_fixed_decoded_step 57 at 222 width 4 opcode
      parse("addq $0x18,%rbp") using $hc)
  if row.getNat == 58 then
    return ← `(tactic| codec_measure_fixed_decoded_step 58 at 226 width 5 opcode
      parse("cmpq %rbp,0x48(%rsp)") using $hc)
  if row.getNat == 59 then
    return ← `(tactic| codec_measure_fixed_decoded_step 59 at 231 width 2 opcode
      parse("jne codec_measure_fixed_u128") using $hc)
  if row.getNat == 60 then
    return ← `(tactic| codec_measure_fixed_decoded_step 60 at 233 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (36)))))] using $hc)
  if row.getNat == 61 then
    return ← `(tactic| codec_measure_fixed_decoded_step 61 at 235 width 5 opcode
      parse("movl $0x18,%eax") using $hc)
  if row.getNat == 62 then
    return ← `(tactic| codec_measure_fixed_decoded_step 62 at 240 width 5 opcode
      parse("movq 0x8(%rsi,%rax,1),%rcx") using $hc)
  if row.getNat == 63 then
    return ← `(tactic| codec_measure_fixed_decoded_step 63 at 245 width 3 opcode
      parse("testq %rcx,%rcx") using $hc)
  Lean.Macro.throwUnsupported

macro "codec_measure_fixed_step_chunk1 " row:num " using " hc:term : tactic => do
  if row.getNat == 64 then
    return ← `(tactic| codec_measure_fixed_decoded_step 64 at 248 width 6 opcode
      parse("jne codec_measure_fixed_u81") using $hc)
  if row.getNat == 65 then
    return ← `(tactic| codec_measure_fixed_decoded_step 65 at 254 width 3 opcode
      parse("xorl %r14d,%r14d") using $hc)
  if row.getNat == 66 then
    return ← `(tactic| codec_measure_fixed_decoded_step 66 at 257 width 3 opcode
      parse("xorl %r15d,%r15d") using $hc)
  if row.getNat == 67 then
    return ← `(tactic| codec_measure_fixed_decoded_step 67 at 260 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (9)))))] using $hc)
  if row.getNat == 68 then
    return ← `(tactic| codec_measure_fixed_decoded_step 68 at 262 width 6 opcode
      parse("movl $0x1,%r15d") using $hc)
  if row.getNat == 69 then
    return ← `(tactic| codec_measure_fixed_decoded_step 69 at 268 width 3 opcode
      parse("xorl %r14d,%r14d") using $hc)
  if row.getNat == 70 then
    return ← `(tactic| codec_measure_fixed_decoded_step 70 at 271 width 4 opcode
      parse("movq %r14,0x8(%rbx)") using $hc)
  if row.getNat == 71 then
    return ← `(tactic| codec_measure_fixed_decoded_step 71 at 275 width 4 opcode
      parse("movq %r15,0x10(%rbx)") using $hc)
  if row.getNat == 72 then
    return ← `(tactic| codec_measure_fixed_decoded_step 72 at 279 width 7 opcode
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 73 then
    return ← `(tactic| codec_measure_fixed_decoded_step 73 at 286 width 5 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (396)))))] using $hc)
  if row.getNat == 74 then
    return ← `(tactic| codec_measure_fixed_decoded_step 74 at 291 width 4 opcode
      parse("movq 0x8(%rsi),%rax") using $hc)
  if row.getNat == 75 then
    return ← `(tactic| codec_measure_fixed_decoded_step 75 at 295 width 4 opcode
      parse("movq 0x10(%rsi),%rdx") using $hc)
  if row.getNat == 76 then
    return ← `(tactic| codec_measure_fixed_decoded_step 76 at 299 width 3 opcode
      parse("movq %rsp,%rdi") using $hc)
  if row.getNat == 77 then
    return ← `(tactic| codec_measure_fixed_decoded_step 77 at 302 width 5 opcode
      parse("movl $0x8,%ecx") using $hc)
  if row.getNat == 78 then
    return ← `(tactic| codec_measure_fixed_decoded_step 78 at 307 width 3 opcode
      parse("movq %rax,%rsi") using $hc)
  if row.getNat == 79 then
    return ← `(tactic| codec_measure_fixed_decoded_step 79 at 310 width 3 opcode
      parse("movq %r12,%r8") using $hc)
  if row.getNat == 80 then
    return ← `(tactic| codec_measure_fixed_decoded_step 80 at 313 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-73294)))))] using $hc)
  if row.getNat == 81 then
    return ← `(tactic| codec_measure_fixed_decoded_step 81 at 318 width 4 opcode
      parse("movl 0x40(%rsp),%eax") using $hc)
  if row.getNat == 82 then
    return ← `(tactic| codec_measure_fixed_decoded_step 82 at 322 width 4 opcode
      parse("movq (%rsp),%r14") using $hc)
  if row.getNat == 83 then
    return ← `(tactic| codec_measure_fixed_decoded_step 83 at 326 width 5 opcode
      parse("movq 0x8(%rsp),%r15") using $hc)
  if row.getNat == 84 then
    return ← `(tactic| codec_measure_fixed_decoded_step 84 at 331 width 5 opcode
      parse("movq 0x10(%rsp),%rcx") using $hc)
  if row.getNat == 85 then
    return ← `(tactic| codec_measure_fixed_decoded_step 85 at 336 width 2 opcode
      parse("testl %eax,%eax") using $hc)
  if row.getNat == 86 then
    return ← `(tactic| codec_measure_fixed_decoded_step 86 at 338 width 6 opcode
      parse("je codec_measure_fixed_u526") using $hc)
  if row.getNat == 87 then
    return ← `(tactic| codec_measure_fixed_decoded_step 87 at 344 width 5 opcode
      parse("movq 0x38(%rsp),%rdx") using $hc)
  if row.getNat == 88 then
    return ← `(tactic| codec_measure_fixed_decoded_step 88 at 349 width 4 opcode
      parse("movq %rdx,0x38(%rbx)") using $hc)
  if row.getNat == 89 then
    return ← `(tactic| codec_measure_fixed_decoded_step 89 at 353 width 5 opcode
      parse("movq 0x30(%rsp),%rdx") using $hc)
  if row.getNat == 90 then
    return ← `(tactic| codec_measure_fixed_decoded_step 90 at 358 width 4 opcode
      parse("movq %rdx,0x30(%rbx)") using $hc)
  if row.getNat == 91 then
    return ← `(tactic| codec_measure_fixed_decoded_step 91 at 362 width 5 opcode
      parse("movq 0x28(%rsp),%rdx") using $hc)
  if row.getNat == 92 then
    return ← `(tactic| codec_measure_fixed_decoded_step 92 at 367 width 4 opcode
      parse("movq %rdx,0x28(%rbx)") using $hc)
  if row.getNat == 93 then
    return ← `(tactic| codec_measure_fixed_decoded_step 93 at 371 width 5 opcode
      parse("movq 0x18(%rsp),%rdx") using $hc)
  if row.getNat == 94 then
    return ← `(tactic| codec_measure_fixed_decoded_step 94 at 376 width 5 opcode
      parse("movq 0x20(%rsp),%rsi") using $hc)
  if row.getNat == 95 then
    return ← `(tactic| codec_measure_fixed_decoded_step 95 at 381 width 4 opcode
      parse("movq %rsi,0x20(%rbx)") using $hc)
  if row.getNat == 96 then
    return ← `(tactic| codec_measure_fixed_decoded_step 96 at 385 width 4 opcode
      parse("movq %rdx,0x18(%rbx)") using $hc)
  if row.getNat == 97 then
    return ← `(tactic| codec_measure_fixed_decoded_step 97 at 389 width 4 opcode
      parse("movl 0x44(%rsp),%edx") using $hc)
  if row.getNat == 98 then
    return ← `(tactic| codec_measure_fixed_decoded_step 98 at 393 width 3 opcode
      parse("movq %r14,(%rbx)") using $hc)
  if row.getNat == 99 then
    return ← `(tactic| codec_measure_fixed_decoded_step 99 at 396 width 4 opcode
      parse("movq %r15,0x8(%rbx)") using $hc)
  if row.getNat == 100 then
    return ← `(tactic| codec_measure_fixed_decoded_step 100 at 400 width 4 opcode
      parse("movq %rcx,0x10(%rbx)") using $hc)
  if row.getNat == 101 then
    return ← `(tactic| codec_measure_fixed_decoded_step 101 at 404 width 3 opcode
      parse("movl %eax,0x40(%rbx)") using $hc)
  if row.getNat == 102 then
    return ← `(tactic| codec_measure_fixed_decoded_step 102 at 407 width 3 opcode
      parse("movl %edx,0x44(%rbx)") using $hc)
  if row.getNat == 103 then
    return ← `(tactic| codec_measure_fixed_decoded_step 103 at 410 width 5 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (279)))))] using $hc)
  if row.getNat == 104 then
    return ← `(tactic| codec_measure_fixed_decoded_step 104 at 415 width 3 opcode
      parse("movq %rsi,%r14") using $hc)
  if row.getNat == 105 then
    return ← `(tactic| codec_measure_fixed_decoded_step 105 at 418 width 4 opcode
      parse("movq 0x18(%rsi),%rsi") using $hc)
  if row.getNat == 106 then
    return ← `(tactic| codec_measure_fixed_decoded_step 106 at 422 width 3 opcode
      parse("movq %rsp,%rdi") using $hc)
  if row.getNat == 107 then
    return ← `(tactic| codec_measure_fixed_decoded_step 107 at 425 width 3 opcode
      parse("movq %r12,%rdx") using $hc)
  if row.getNat == 108 then
    return ← `(tactic| codec_measure_fixed_decoded_step 108 at 428 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-433)))))] using $hc)
  if row.getNat == 109 then
    return ← `(tactic| codec_measure_fixed_decoded_step 109 at 433 width 4 opcode
      parse("movl 0x40(%rsp),%eax") using $hc)
  if row.getNat == 110 then
    return ← `(tactic| codec_measure_fixed_decoded_step 110 at 437 width 4 opcode
      parse("movq (%rsp),%rcx") using $hc)
  if row.getNat == 111 then
    return ← `(tactic| codec_measure_fixed_decoded_step 111 at 441 width 5 opcode
      parse("movq 0x8(%rsp),%rsi") using $hc)
  if row.getNat == 112 then
    return ← `(tactic| codec_measure_fixed_decoded_step 112 at 446 width 5 opcode
      parse("movq 0x10(%rsp),%rdx") using $hc)
  if row.getNat == 113 then
    return ← `(tactic| codec_measure_fixed_decoded_step 113 at 451 width 2 opcode
      parse("testl %eax,%eax") using $hc)
  if row.getNat == 114 then
    return ← `(tactic| codec_measure_fixed_decoded_step 114 at 453 width 2 opcode
      parse("je codec_measure_fixed_u562") using $hc)
  if row.getNat == 115 then
    return ← `(tactic| codec_measure_fixed_decoded_step 115 at 455 width 5 opcode
      parse("movq 0x38(%rsp),%rdi") using $hc)
  if row.getNat == 116 then
    return ← `(tactic| codec_measure_fixed_decoded_step 116 at 460 width 4 opcode
      parse("movq %rdi,0x38(%rbx)") using $hc)
  if row.getNat == 117 then
    return ← `(tactic| codec_measure_fixed_decoded_step 117 at 464 width 5 opcode
      parse("movq 0x30(%rsp),%rdi") using $hc)
  if row.getNat == 118 then
    return ← `(tactic| codec_measure_fixed_decoded_step 118 at 469 width 4 opcode
      parse("movq %rdi,0x30(%rbx)") using $hc)
  if row.getNat == 119 then
    return ← `(tactic| codec_measure_fixed_decoded_step 119 at 473 width 5 opcode
      parse("movq 0x28(%rsp),%rdi") using $hc)
  if row.getNat == 120 then
    return ← `(tactic| codec_measure_fixed_decoded_step 120 at 478 width 4 opcode
      parse("movq %rdi,0x28(%rbx)") using $hc)
  if row.getNat == 121 then
    return ← `(tactic| codec_measure_fixed_decoded_step 121 at 482 width 5 opcode
      parse("movq 0x18(%rsp),%rdi") using $hc)
  if row.getNat == 122 then
    return ← `(tactic| codec_measure_fixed_decoded_step 122 at 487 width 5 opcode
      parse("movq 0x20(%rsp),%r8") using $hc)
  if row.getNat == 123 then
    return ← `(tactic| codec_measure_fixed_decoded_step 123 at 492 width 4 opcode
      parse("movq %r8,0x20(%rbx)") using $hc)
  if row.getNat == 124 then
    return ← `(tactic| codec_measure_fixed_decoded_step 124 at 496 width 4 opcode
      parse("movq %rdi,0x18(%rbx)") using $hc)
  if row.getNat == 125 then
    return ← `(tactic| codec_measure_fixed_decoded_step 125 at 500 width 4 opcode
      parse("movl 0x44(%rsp),%edi") using $hc)
  if row.getNat == 126 then
    return ← `(tactic| codec_measure_fixed_decoded_step 126 at 504 width 4 opcode
      parse("movq %rsi,0x8(%rbx)") using $hc)
  if row.getNat == 127 then
    return ← `(tactic| codec_measure_fixed_decoded_step 127 at 508 width 4 opcode
      parse("movq %rdx,0x10(%rbx)") using $hc)
  Lean.Macro.throwUnsupported

macro "codec_measure_fixed_step_chunk2 " row:num " using " hc:term : tactic => do
  if row.getNat == 128 then
    return ← `(tactic| codec_measure_fixed_decoded_step 128 at 512 width 3 opcode
      parse("movq %rcx,(%rbx)") using $hc)
  if row.getNat == 129 then
    return ← `(tactic| codec_measure_fixed_decoded_step 129 at 515 width 3 opcode
      parse("movl %eax,0x40(%rbx)") using $hc)
  if row.getNat == 130 then
    return ← `(tactic| codec_measure_fixed_decoded_step 130 at 518 width 3 opcode
      parse("movl %edi,0x44(%rbx)") using $hc)
  if row.getNat == 131 then
    return ← `(tactic| codec_measure_fixed_decoded_step 131 at 521 width 5 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (168)))))] using $hc)
  if row.getNat == 132 then
    return ← `(tactic| codec_measure_fixed_decoded_step 132 at 526 width 3 opcode
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 133 then
    return ← `(tactic| codec_measure_fixed_decoded_step 133 at 529 width 6 opcode
      parse("je codec_measure_fixed_u271") using $hc)
  if row.getNat == 134 then
    return ← `(tactic| codec_measure_fixed_decoded_step 134 at 535 width 3 opcode
      parse("movq %rsp,%rdi") using $hc)
  if row.getNat == 135 then
    return ← `(tactic| codec_measure_fixed_decoded_step 135 at 538 width 6 opcode
      parse("movl $0x1,%r8d") using $hc)
  if row.getNat == 136 then
    return ← `(tactic| codec_measure_fixed_decoded_step 136 at 544 width 3 opcode
      parse("movq %r14,%rsi") using $hc)
  if row.getNat == 137 then
    return ← `(tactic| codec_measure_fixed_decoded_step 137 at 547 width 3 opcode
      parse("movq %r15,%rdx") using $hc)
  if row.getNat == 138 then
    return ← `(tactic| codec_measure_fixed_decoded_step 138 at 550 width 2 opcode
      parse("xorl %ecx,%ecx") using $hc)
  if row.getNat == 139 then
    return ← `(tactic| codec_measure_fixed_decoded_step 139 at 552 width 3 opcode
      parse("movq %r12,%r9") using $hc)
  if row.getNat == 140 then
    return ← `(tactic| codec_measure_fixed_decoded_step 140 at 555 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-65232)))))] using $hc)
  if row.getNat == 141 then
    return ← `(tactic| codec_measure_fixed_decoded_step 141 at 560 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (24)))))] using $hc)
  if row.getNat == 142 then
    return ← `(tactic| codec_measure_fixed_decoded_step 142 at 562 width 3 opcode
      parse("testb $0x1,%cl") using $hc)
  if row.getNat == 143 then
    return ← `(tactic| codec_measure_fixed_decoded_step 143 at 565 width 2 opcode
      parse("je codec_measure_fixed_u680") using $hc)
  if row.getNat == 144 then
    return ← `(tactic| codec_measure_fixed_decoded_step 144 at 567 width 4 opcode
      parse("movq 0x8(%r14),%rcx") using $hc)
  if row.getNat == 145 then
    return ← `(tactic| codec_measure_fixed_decoded_step 145 at 571 width 4 opcode
      parse("movq 0x10(%r14),%r8") using $hc)
  if row.getNat == 146 then
    return ← `(tactic| codec_measure_fixed_decoded_step 146 at 575 width 3 opcode
      parse("movq %rsp,%rdi") using $hc)
  if row.getNat == 147 then
    return ← `(tactic| codec_measure_fixed_decoded_step 147 at 578 width 3 opcode
      parse("movq %r12,%r9") using $hc)
  if row.getNat == 148 then
    return ← `(tactic| codec_measure_fixed_decoded_step 148 at 581 width 5 opcode
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-62378)))))] using $hc)
  if row.getNat == 149 then
    return ← `(tactic| codec_measure_fixed_decoded_step 149 at 586 width 4 opcode
      parse("movl 0x40(%rsp),%eax") using $hc)
  if row.getNat == 150 then
    return ← `(tactic| codec_measure_fixed_decoded_step 150 at 590 width 4 opcode
      parse("movq (%rsp),%r14") using $hc)
  if row.getNat == 151 then
    return ← `(tactic| codec_measure_fixed_decoded_step 151 at 594 width 5 opcode
      parse("movq 0x8(%rsp),%r15") using $hc)
  if row.getNat == 152 then
    return ← `(tactic| codec_measure_fixed_decoded_step 152 at 599 width 2 opcode
      parse("testl %eax,%eax") using $hc)
  if row.getNat == 153 then
    return ← `(tactic| codec_measure_fixed_decoded_step 153 at 601 width 6 opcode
      parse("je codec_measure_fixed_u271") using $hc)
  if row.getNat == 154 then
    return ← `(tactic| codec_measure_fixed_decoded_step 154 at 607 width 5 opcode
      parse("movq 0x38(%rsp),%rcx") using $hc)
  if row.getNat == 155 then
    return ← `(tactic| codec_measure_fixed_decoded_step 155 at 612 width 4 opcode
      parse("movq %rcx,0x38(%rbx)") using $hc)
  if row.getNat == 156 then
    return ← `(tactic| codec_measure_fixed_decoded_step 156 at 616 width 5 opcode
      parse("movq 0x30(%rsp),%rcx") using $hc)
  if row.getNat == 157 then
    return ← `(tactic| codec_measure_fixed_decoded_step 157 at 621 width 4 opcode
      parse("movq %rcx,0x30(%rbx)") using $hc)
  if row.getNat == 158 then
    return ← `(tactic| codec_measure_fixed_decoded_step 158 at 625 width 5 opcode
      parse("movq 0x28(%rsp),%rcx") using $hc)
  if row.getNat == 159 then
    return ← `(tactic| codec_measure_fixed_decoded_step 159 at 630 width 4 opcode
      parse("movq %rcx,0x28(%rbx)") using $hc)
  if row.getNat == 160 then
    return ← `(tactic| codec_measure_fixed_decoded_step 160 at 634 width 5 opcode
      parse("movq 0x20(%rsp),%rcx") using $hc)
  if row.getNat == 161 then
    return ← `(tactic| codec_measure_fixed_decoded_step 161 at 639 width 4 opcode
      parse("movq %rcx,0x20(%rbx)") using $hc)
  if row.getNat == 162 then
    return ← `(tactic| codec_measure_fixed_decoded_step 162 at 643 width 5 opcode
      parse("movq 0x10(%rsp),%rcx") using $hc)
  if row.getNat == 163 then
    return ← `(tactic| codec_measure_fixed_decoded_step 163 at 648 width 5 opcode
      parse("movq 0x18(%rsp),%rdx") using $hc)
  if row.getNat == 164 then
    return ← `(tactic| codec_measure_fixed_decoded_step 164 at 653 width 4 opcode
      parse("movq %rdx,0x18(%rbx)") using $hc)
  if row.getNat == 165 then
    return ← `(tactic| codec_measure_fixed_decoded_step 165 at 657 width 4 opcode
      parse("movq %rcx,0x10(%rbx)") using $hc)
  if row.getNat == 166 then
    return ← `(tactic| codec_measure_fixed_decoded_step 166 at 661 width 4 opcode
      parse("movl 0x44(%rsp),%ecx") using $hc)
  if row.getNat == 167 then
    return ← `(tactic| codec_measure_fixed_decoded_step 167 at 665 width 3 opcode
      parse("movq %r14,(%rbx)") using $hc)
  if row.getNat == 168 then
    return ← `(tactic| codec_measure_fixed_decoded_step 168 at 668 width 4 opcode
      parse("movq %r15,0x8(%rbx)") using $hc)
  if row.getNat == 169 then
    return ← `(tactic| codec_measure_fixed_decoded_step 169 at 672 width 3 opcode
      parse("movl %eax,0x40(%rbx)") using $hc)
  if row.getNat == 170 then
    return ← `(tactic| codec_measure_fixed_decoded_step 170 at 675 width 3 opcode
      parse("movl %ecx,0x44(%rbx)") using $hc)
  if row.getNat == 171 then
    return ← `(tactic| codec_measure_fixed_decoded_step 171 at 678 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (14)))))] using $hc)
  if row.getNat == 172 then
    return ← `(tactic| codec_measure_fixed_decoded_step 172 at 680 width 7 opcode
      parse("movq $0x0,(%rbx)") using $hc)
  if row.getNat == 173 then
    return ← `(tactic| codec_measure_fixed_decoded_step 173 at 687 width 7 opcode
      parse("movl $0x0,0x40(%rbx)") using $hc)
  if row.getNat == 174 then
    return ← `(tactic| codec_measure_fixed_decoded_step 174 at 694 width 4 opcode
      parse("addq $0x58,%rsp") using $hc)
  if row.getNat == 175 then
    return ← `(tactic| codec_measure_fixed_decoded_step 175 at 698 width 1 opcode
      parse("popq %rbx") using $hc)
  if row.getNat == 176 then
    return ← `(tactic| codec_measure_fixed_decoded_step 176 at 699 width 2 opcode
      parse("popq %r12") using $hc)
  if row.getNat == 177 then
    return ← `(tactic| codec_measure_fixed_decoded_step 177 at 701 width 2 opcode
      parse("popq %r13") using $hc)
  if row.getNat == 178 then
    return ← `(tactic| codec_measure_fixed_decoded_step 178 at 703 width 2 opcode
      parse("popq %r14") using $hc)
  if row.getNat == 179 then
    return ← `(tactic| codec_measure_fixed_decoded_step 179 at 705 width 2 opcode
      parse("popq %r15") using $hc)
  if row.getNat == 180 then
    return ← `(tactic| codec_measure_fixed_decoded_step 180 at 707 width 1 opcode
      parse("popq %rbp") using $hc)
  if row.getNat == 181 then
    return ← `(tactic| codec_measure_fixed_decoded_step 181 at 708 width 1 opcode
      parse("retq ") using $hc)
  if row.getNat == 182 then
    return ← `(tactic| codec_measure_fixed_decoded_step 182 at 709 width 5 opcode
      parse("movq 0x38(%rsp),%rsi") using $hc)
  if row.getNat == 183 then
    return ← `(tactic| codec_measure_fixed_decoded_step 183 at 714 width 4 opcode
      parse("movq %rsi,0x38(%rbx)") using $hc)
  if row.getNat == 184 then
    return ← `(tactic| codec_measure_fixed_decoded_step 184 at 718 width 5 opcode
      parse("movq 0x30(%rsp),%rsi") using $hc)
  if row.getNat == 185 then
    return ← `(tactic| codec_measure_fixed_decoded_step 185 at 723 width 4 opcode
      parse("movq %rsi,0x30(%rbx)") using $hc)
  if row.getNat == 186 then
    return ← `(tactic| codec_measure_fixed_decoded_step 186 at 727 width 5 opcode
      parse("movq 0x28(%rsp),%rsi") using $hc)
  if row.getNat == 187 then
    return ← `(tactic| codec_measure_fixed_decoded_step 187 at 732 width 4 opcode
      parse("movq %rsi,0x28(%rbx)") using $hc)
  if row.getNat == 188 then
    return ← `(tactic| codec_measure_fixed_decoded_step 188 at 736 width 5 opcode
      parse("movq 0x18(%rsp),%rsi") using $hc)
  if row.getNat == 189 then
    return ← `(tactic| codec_measure_fixed_decoded_step 189 at 741 width 5 opcode
      parse("movq 0x20(%rsp),%rdi") using $hc)
  if row.getNat == 190 then
    return ← `(tactic| codec_measure_fixed_decoded_step 190 at 746 width 4 opcode
      parse("movq %rdi,0x20(%rbx)") using $hc)
  if row.getNat == 191 then
    return ← `(tactic| codec_measure_fixed_decoded_step 191 at 750 width 4 opcode
      parse("movq %rsi,0x18(%rbx)") using $hc)
  Lean.Macro.throwUnsupported

macro "codec_measure_fixed_step_chunk3 " row:num " using " hc:term : tactic => do
  if row.getNat == 192 then
    return ← `(tactic| codec_measure_fixed_decoded_step 192 at 754 width 4 opcode
      parse("movl 0x44(%rsp),%esi") using $hc)
  if row.getNat == 193 then
    return ← `(tactic| codec_measure_fixed_decoded_step 193 at 758 width 4 opcode
      parse("movq %rcx,0x8(%rbx)") using $hc)
  if row.getNat == 194 then
    return ← `(tactic| codec_measure_fixed_decoded_step 194 at 762 width 4 opcode
      parse("movq %r8,0x10(%rbx)") using $hc)
  if row.getNat == 195 then
    return ← `(tactic| codec_measure_fixed_decoded_step 195 at 766 width 3 opcode
      parse("movq %rdx,(%rbx)") using $hc)
  if row.getNat == 196 then
    return ← `(tactic| codec_measure_fixed_decoded_step 196 at 769 width 3 opcode
      parse("movl %eax,0x40(%rbx)") using $hc)
  if row.getNat == 197 then
    return ← `(tactic| codec_measure_fixed_decoded_step 197 at 772 width 3 opcode
      parse("movl %esi,0x44(%rbx)") using $hc)
  if row.getNat == 198 then
    return ← `(tactic| codec_measure_fixed_decoded_step 198 at 775 width 2 opcode
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-83)))))] using $hc)
  Lean.Macro.throwUnsupported

macro "codec_measure_fixed_step " row:num " using " hc:term : tactic => do
  if row.getNat < 64 then
    return ← `(tactic| codec_measure_fixed_step_chunk0 $row using $hc)
  if row.getNat < 128 then
    return ← `(tactic| codec_measure_fixed_step_chunk1 $row using $hc)
  if row.getNat < 192 then
    return ← `(tactic| codec_measure_fixed_step_chunk2 $row using $hc)
  return ← `(tactic| codec_measure_fixed_step_chunk3 $row using $hc)

macro "codec_measure_fixed_load " loaded:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($loaded), Delimited.word_cast])

end SszX86.CodecMeasureFixed

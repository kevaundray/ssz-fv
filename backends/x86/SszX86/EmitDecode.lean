import SszX86.EmitChunks
import SszX86.DispatchPush

namespace SszX86.Emit
open Kraken.X64.Parser
open BoolCodec UintCodec

/-- A bounded fetch contract checks one concrete row against the actual image. -/
macro "emit_decoded_step " row:num " at " pc:num " encodedWidth " bytes:num " opcodeAST " instructions:term
    " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.Emit.program) (n := $row)
     (by rw [SszX86.Emit.program_length]; decide)
   have fetched := SszX86.Emit.step_at _ _ $hc
     (($pc, $bytes, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Emit.directives, SszX86.Emit.labels,
      Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

/-- Concrete row selection is elaborator work, not whole-image proof reduction. -/
macro "emit_step_low " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| emit_decoded_step 0 at 0 encodedWidth 1 opcodeAST
      parse("pushq %rbp") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| emit_decoded_step 1 at 1 encodedWidth 2 opcodeAST
      parse("pushq %r15") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| emit_decoded_step 2 at 3 encodedWidth 2 opcodeAST
      parse("pushq %r14") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| emit_decoded_step 3 at 5 encodedWidth 2 opcodeAST
      parse("pushq %r13") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| emit_decoded_step 4 at 7 encodedWidth 2 opcodeAST
      parse("pushq %r12") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| emit_decoded_step 5 at 9 encodedWidth 1 opcodeAST
      parse("pushq %rbx") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| emit_decoded_step 6 at 10 encodedWidth 4 opcodeAST
      parse("subq $0x68,%rsp") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| emit_decoded_step 7 at 14 encodedWidth 3 opcodeAST
      parse("movq %r8,%r14") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| emit_decoded_step 8 at 17 encodedWidth 3 opcodeAST
      parse("movq %rcx,%r8") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| emit_decoded_step 9 at 20 encodedWidth 3 opcodeAST
      parse("movq %rdx,%r12") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| emit_decoded_step 10 at 23 encodedWidth 3 opcodeAST
      parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 11 then
    return ← `(tactic| emit_decoded_step 11 at 26 encodedWidth 3 opcodeAST
      parse("movq (%rsi),%rax") using $hc)
  if row.getNat == 12 then
    return ← `(tactic| emit_decoded_step 12 at 29 encodedWidth 3 opcodeAST
      [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rcx .W32)) (.mem (w := .W8) { base := some (.reg .rdx), idx := none, disp := .int64 (0) })))] using $hc)
  if row.getNat == 13 then
    return ← `(tactic| emit_decoded_step 13 at 32 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 14 then
    return ← `(tactic| emit_decoded_step 14 at 35 encodedWidth 6 opcodeAST
      parse("je emit_u190") using $hc)
  if row.getNat == 15 then
    return ← `(tactic| emit_decoded_step 15 at 41 encodedWidth 3 opcodeAST
      parse("cmpl $0x1,%eax") using $hc)
  if row.getNat == 16 then
    return ← `(tactic| emit_decoded_step 16 at 44 encodedWidth 6 opcodeAST
      parse("jne emit_u228") using $hc)
  if row.getNat == 17 then
    return ← `(tactic| emit_decoded_step 17 at 50 encodedWidth 3 opcodeAST
      parse("cmpl $0x1,%ecx") using $hc)
  if row.getNat == 18 then
    return ← `(tactic| emit_decoded_step 18 at 53 encodedWidth 6 opcodeAST
      parse("jne emit_u801") using $hc)
  if row.getNat == 19 then
    return ← `(tactic| emit_decoded_step 19 at 59 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rax") using $hc)
  if row.getNat == 20 then
    return ← `(tactic| emit_decoded_step 20 at 63 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rsi") using $hc)
  if row.getNat == 21 then
    return ← `(tactic| emit_decoded_step 21 at 67 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 22 then
    return ← `(tactic| emit_decoded_step 22 at 70 encodedWidth 6 opcodeAST
      parse("je emit_u583") using $hc)
  if row.getNat == 23 then
    return ← `(tactic| emit_decoded_step 23 at 76 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%rsi),%rcx") using $hc)
  if row.getNat == 24 then
    return ← `(tactic| emit_decoded_step 24 at 80 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rcx") using $hc)
  if row.getNat == 25 then
    return ← `(tactic| emit_decoded_step 25 at 84 encodedWidth 6 opcodeAST
      parse("je emit_u575") using $hc)
  if row.getNat == 26 then
    return ← `(tactic| emit_decoded_step 26 at 90 encodedWidth 4 opcodeAST
      parse("leaq -0x1(%rcx),%rdx") using $hc)
  if row.getNat == 27 then
    return ← `(tactic| emit_decoded_step 27 at 94 encodedWidth 6 opcodeAST
      parse("cmpq $0x0,-0x10(%rax,%rcx,8)") using $hc)
  if row.getNat == 28 then
    return ← `(tactic| emit_decoded_step 28 at 100 encodedWidth 3 opcodeAST
      parse("movq %rdx,%rcx") using $hc)
  if row.getNat == 29 then
    return ← `(tactic| emit_decoded_step 29 at 103 encodedWidth 2 opcodeAST
      parse("je emit_u80") using $hc)
  if row.getNat == 30 then
    return ← `(tactic| emit_decoded_step 30 at 105 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rdx") using $hc)
  if row.getNat == 31 then
    return ← `(tactic| emit_decoded_step 31 at 109 encodedWidth 6 opcodeAST
      parse("je emit_u580") using $hc)
  if row.getNat == 32 then
    return ← `(tactic| emit_decoded_step 32 at 115 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 33 then
    return ← `(tactic| emit_decoded_step 33 at 123 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 34 then
    return ← `(tactic| emit_decoded_step 34 at 131 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x28(%rbx)") using $hc)
  if row.getNat == 35 then
    return ← `(tactic| emit_decoded_step 35 at 139 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 36 then
    return ← `(tactic| emit_decoded_step 36 at 147 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x18(%rbx)") using $hc)
  if row.getNat == 37 then
    return ← `(tactic| emit_decoded_step 37 at 155 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x10(%rbx)") using $hc)
  if row.getNat == 38 then
    return ← `(tactic| emit_decoded_step 38 at 163 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 39 then
    return ← `(tactic| emit_decoded_step 39 at 171 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 40 then
    return ← `(tactic| emit_decoded_step 40 at 178 encodedWidth 7 opcodeAST
      parse("movl $0x8001,0x40(%rbx)") using $hc)
  if row.getNat == 41 then
    return ← `(tactic| emit_decoded_step 41 at 185 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1410)))))] using $hc)
  if row.getNat == 42 then
    return ← `(tactic| emit_decoded_step 42 at 190 encodedWidth 2 opcodeAST
      parse("testl %ecx,%ecx") using $hc)
  if row.getNat == 43 then
    return ← `(tactic| emit_decoded_step 43 at 192 encodedWidth 6 opcodeAST
      parse("jne emit_u801") using $hc)
  if row.getNat == 44 then
    return ← `(tactic| emit_decoded_step 44 at 198 encodedWidth 3 opcodeAST
      parse("testq %r9,%r9") using $hc)
  if row.getNat == 45 then
    return ← `(tactic| emit_decoded_step 45 at 201 encodedWidth 6 opcodeAST
      parse("je emit_u1666") using $hc)
  if row.getNat == 46 then
    return ← `(tactic| emit_decoded_step 46 at 207 encodedWidth 6 opcodeAST
      [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .r12), idx := none, disp := .int64 (1) })))] using $hc)
  if row.getNat == 47 then
    return ← `(tactic| emit_decoded_step 47 at 213 encodedWidth 3 opcodeAST
      parse("movb %al,(%r14)") using $hc)
  if row.getNat == 48 then
    return ← `(tactic| emit_decoded_step 48 at 216 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 49 then
    return ← `(tactic| emit_decoded_step 49 at 223 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1365)))))] using $hc)
  if row.getNat == 50 then
    return ← `(tactic| emit_decoded_step 50 at 228 encodedWidth 3 opcodeAST
      parse("addl $0xfffffffe,%ecx") using $hc)
  if row.getNat == 51 then
    return ← `(tactic| emit_decoded_step 51 at 231 encodedWidth 3 opcodeAST
      parse("cmpl $0x3,%ecx") using $hc)
  if row.getNat == 52 then
    return ← `(tactic| emit_decoded_step 52 at 234 encodedWidth 6 opcodeAST
      parse("ja emit_u801") using $hc)
  if row.getNat == 53 then
    return ← `(tactic| emit_decoded_step 53 at 240 encodedWidth 7 opcodeAST
      [.instr (.regular .W64 .W64 (.lea .rdx {base := some .rip, idx := none, disp := .int64 (-93047)}))] using $hc)
  if row.getNat == 54 then
    return ← `(tactic| emit_decoded_step 54 at 247 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W64 (.movsx (.reg .rcx) (.mem (w := .W32) {base := some (.reg .rdx), idx := some ⟨.rcx, .W32⟩})))] using $hc)
  if row.getNat == 55 then
    return ← `(tactic| emit_decoded_step 55 at 251 encodedWidth 3 opcodeAST
      parse("addq %rdx,%rcx") using $hc)
  if row.getNat == 56 then
    return ← `(tactic| emit_decoded_step 56 at 254 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.reg .rcx)))] using $hc)
  if row.getNat == 57 then
    return ← `(tactic| emit_decoded_step 57 at 256 encodedWidth 3 opcodeAST
      parse("andl $0xfffffffe,%eax") using $hc)
  if row.getNat == 58 then
    return ← `(tactic| emit_decoded_step 58 at 259 encodedWidth 3 opcodeAST
      parse("cmpl $0x2,%eax") using $hc)
  if row.getNat == 59 then
    return ← `(tactic| emit_decoded_step 59 at 262 encodedWidth 6 opcodeAST
      parse("jne emit_u801") using $hc)
  if row.getNat == 60 then
    return ← `(tactic| emit_decoded_step 60 at 268 encodedWidth 5 opcodeAST
      parse("movq 0x10(%r12),%r13") using $hc)
  if row.getNat == 61 then
    return ← `(tactic| emit_decoded_step 61 at 273 encodedWidth 3 opcodeAST
      parse("cmpq %r9,%r13") using $hc)
  if row.getNat == 62 then
    return ← `(tactic| emit_decoded_step 62 at 276 encodedWidth 6 opcodeAST
      parse("ja emit_u1625") using $hc)
  if row.getNat == 63 then
    return ← `(tactic| emit_decoded_step 63 at 282 encodedWidth 5 opcodeAST
      parse("movq 0x8(%r12),%rsi") using $hc)
  if row.getNat == 64 then
    return ← `(tactic| emit_decoded_step 64 at 287 encodedWidth 3 opcodeAST
      parse("movq %r14,%rdi") using $hc)
  if row.getNat == 65 then
    return ← `(tactic| emit_decoded_step 65 at 290 encodedWidth 3 opcodeAST
      parse("movq %r13,%rdx") using $hc)
  if row.getNat == 66 then
    return ← `(tactic| emit_decoded_step 66 at 293 encodedWidth 6 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (110437)))))] using $hc)
  if row.getNat == 67 then
    return ← `(tactic| emit_decoded_step 67 at 299 encodedWidth 3 opcodeAST
      parse("movq %r13,(%rbx)") using $hc)
  if row.getNat == 68 then
    return ← `(tactic| emit_decoded_step 68 at 302 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1286)))))] using $hc)
  if row.getNat == 69 then
    return ← `(tactic| emit_decoded_step 69 at 414 encodedWidth 4 opcodeAST
      parse("leaq -0x5(%rax),%rcx") using $hc)
  if row.getNat == 70 then
    return ← `(tactic| emit_decoded_step 70 at 418 encodedWidth 4 opcodeAST
      parse("cmpq $0x2,%rcx") using $hc)
  if row.getNat == 71 then
    return ← `(tactic| emit_decoded_step 71 at 422 encodedWidth 6 opcodeAST
      parse("jae emit_u663") using $hc)
  if row.getNat == 72 then
    return ← `(tactic| emit_decoded_step 72 at 428 encodedWidth 5 opcodeAST
      parse("movq 0x20(%r12),%rax") using $hc)
  if row.getNat == 73 then
    return ← `(tactic| emit_decoded_step 73 at 433 encodedWidth 5 opcodeAST
      parse("movq 0x28(%r12),%r13") using $hc)
  if row.getNat == 74 then
    return ← `(tactic| emit_decoded_step 74 at 438 encodedWidth 5 opcodeAST
      parse("shldq $0x3d,%rax,%r13") using $hc)
  if row.getNat == 75 then
    return ← `(tactic| emit_decoded_step 75 at 443 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%r9") using $hc)
  if row.getNat == 76 then
    return ← `(tactic| emit_decoded_step 76 at 446 encodedWidth 6 opcodeAST
      parse("jb emit_u1625") using $hc)
  if row.getNat == 77 then
    return ← `(tactic| emit_decoded_step 77 at 452 encodedWidth 5 opcodeAST
      parse("movq 0x18(%r12),%rcx") using $hc)
  if row.getNat == 78 then
    return ← `(tactic| emit_decoded_step 78 at 457 encodedWidth 5 opcodeAST
      parse("movq %rcx,0x8(%rsp)") using $hc)
  if row.getNat == 79 then
    return ← `(tactic| emit_decoded_step 79 at 462 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%rcx") using $hc)
  if row.getNat == 80 then
    return ← `(tactic| emit_decoded_step 80 at 465 encodedWidth 6 opcodeAST
      parse("jb emit_u1638") using $hc)
  if row.getNat == 81 then
    return ← `(tactic| emit_decoded_step 81 at 471 encodedWidth 3 opcodeAST
      parse("movq %r9,%r15") using $hc)
  if row.getNat == 82 then
    return ← `(tactic| emit_decoded_step 82 at 474 encodedWidth 5 opcodeAST
      parse("movq %rax,0x10(%rsp)") using $hc)
  if row.getNat == 83 then
    return ← `(tactic| emit_decoded_step 83 at 479 encodedWidth 2 opcodeAST
      parse("movl %eax,%ebp") using $hc)
  if row.getNat == 84 then
    return ← `(tactic| emit_decoded_step 84 at 481 encodedWidth 3 opcodeAST
      parse("andl $0x7,%ebp") using $hc)
  if row.getNat == 85 then
    return ← `(tactic| emit_decoded_step 85 at 484 encodedWidth 5 opcodeAST
      parse("movq 0x10(%r12),%r12") using $hc)
  if row.getNat == 86 then
    return ← `(tactic| emit_decoded_step 86 at 489 encodedWidth 3 opcodeAST
      parse("movq %r14,%rdi") using $hc)
  if row.getNat == 87 then
    return ← `(tactic| emit_decoded_step 87 at 492 encodedWidth 3 opcodeAST
      parse("movq %r12,%rsi") using $hc)
  if row.getNat == 88 then
    return ← `(tactic| emit_decoded_step 88 at 495 encodedWidth 3 opcodeAST
      parse("movq %r13,%rdx") using $hc)
  if row.getNat == 89 then
    return ← `(tactic| emit_decoded_step 89 at 498 encodedWidth 6 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (110232)))))] using $hc)
  if row.getNat == 90 then
    return ← `(tactic| emit_decoded_step 90 at 504 encodedWidth 2 opcodeAST
      parse("testl %ebp,%ebp") using $hc)
  if row.getNat == 91 then
    return ← `(tactic| emit_decoded_step 91 at 506 encodedWidth 6 opcodeAST
      parse("je emit_u1155") using $hc)
  Lean.Macro.throwErrorAt row "not a low primitive emit instruction index"

macro "emit_step_mid " row:num " using " hc:term : tactic => do
  if row.getNat == 92 then
    return ← `(tactic| emit_decoded_step 92 at 512 encodedWidth 5 opcodeAST
      parse("movq 0x8(%rsp),%rdx") using $hc)
  if row.getNat == 93 then
    return ← `(tactic| emit_decoded_step 93 at 517 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%rdx") using $hc)
  if row.getNat == 94 then
    return ← `(tactic| emit_decoded_step 94 at 520 encodedWidth 6 opcodeAST
      parse("jbe emit_u1683") using $hc)
  if row.getNat == 95 then
    return ← `(tactic| emit_decoded_step 95 at 526 encodedWidth 3 opcodeAST
      parse("movq %r15,%rsi") using $hc)
  if row.getNat == 96 then
    return ← `(tactic| emit_decoded_step 96 at 529 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .r12), idx := some ⟨.r13, .W8⟩, disp := .int64 (0) })))] using $hc)
  if row.getNat == 97 then
    return ← `(tactic| emit_decoded_step 97 at 534 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%r13),%rcx") using $hc)
  if row.getNat == 98 then
    return ← `(tactic| emit_decoded_step 98 at 538 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%rcx") using $hc)
  if row.getNat == 99 then
    return ← `(tactic| emit_decoded_step 99 at 541 encodedWidth 2 opcodeAST
      parse("jne emit_u562") using $hc)
  if row.getNat == 100 then
    return ← `(tactic| emit_decoded_step 100 at 543 encodedWidth 5 opcodeAST
      parse("movq 0x10(%rsp),%rcx") using $hc)
  if row.getNat == 101 then
    return ← `(tactic| emit_decoded_step 101 at 548 encodedWidth 4 opcodeAST
      parse("andq $0x7,%rcx") using $hc)
  if row.getNat == 102 then
    return ← `(tactic| emit_decoded_step 102 at 552 encodedWidth 2 opcodeAST
      parse("je emit_u562") using $hc)
  if row.getNat == 103 then
    return ← `(tactic| emit_decoded_step 103 at 554 encodedWidth 2 opcodeAST
      parse("movb $0xff,%dl") using $hc)
  if row.getNat == 104 then
    return ← `(tactic| emit_decoded_step 104 at 556 encodedWidth 2 opcodeAST
      parse("shlb %cl,%dl") using $hc)
  if row.getNat == 105 then
    return ← `(tactic| emit_decoded_step 105 at 558 encodedWidth 2 opcodeAST
      parse("notb %dl") using $hc)
  if row.getNat == 106 then
    return ← `(tactic| emit_decoded_step 106 at 560 encodedWidth 2 opcodeAST
      parse("andb %dl,%al") using $hc)
  if row.getNat == 107 then
    return ← `(tactic| emit_decoded_step 107 at 562 encodedWidth 2 opcodeAST
      parse("movb $0x1,%dl") using $hc)
  if row.getNat == 108 then
    return ← `(tactic| emit_decoded_step 108 at 564 encodedWidth 2 opcodeAST
      parse("movl %ebp,%ecx") using $hc)
  if row.getNat == 109 then
    return ← `(tactic| emit_decoded_step 109 at 566 encodedWidth 2 opcodeAST
      parse("shlb %cl,%dl") using $hc)
  if row.getNat == 110 then
    return ← `(tactic| emit_decoded_step 110 at 568 encodedWidth 2 opcodeAST
      parse("orb %al,%dl") using $hc)
  if row.getNat == 111 then
    return ← `(tactic| emit_decoded_step 111 at 570 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (585)))))] using $hc)
  if row.getNat == 112 then
    return ← `(tactic| emit_decoded_step 112 at 575 encodedWidth 3 opcodeAST
      parse("testq %rsi,%rsi") using $hc)
  if row.getNat == 113 then
    return ← `(tactic| emit_decoded_step 113 at 578 encodedWidth 2 opcodeAST
      parse("je emit_u653") using $hc)
  if row.getNat == 114 then
    return ← `(tactic| emit_decoded_step 114 at 580 encodedWidth 3 opcodeAST
      parse("movq (%rax),%rsi") using $hc)
  if row.getNat == 115 then
    return ← `(tactic| emit_decoded_step 115 at 583 encodedWidth 3 opcodeAST
      parse("cmpq %r9,%rsi") using $hc)
  if row.getNat == 116 then
    return ← `(tactic| emit_decoded_step 116 at 586 encodedWidth 6 opcodeAST
      parse("ja emit_u1615") using $hc)
  if row.getNat == 117 then
    return ← `(tactic| emit_decoded_step 117 at 592 encodedWidth 3 opcodeAST
      parse("testq %rsi,%rsi") using $hc)
  if row.getNat == 118 then
    return ← `(tactic| emit_decoded_step 118 at 595 encodedWidth 2 opcodeAST
      parse("je emit_u653") using $hc)
  if row.getNat == 119 then
    return ← `(tactic| emit_decoded_step 119 at 597 encodedWidth 5 opcodeAST
      parse("movq 0x8(%r12),%rdi") using $hc)
  if row.getNat == 120 then
    return ← `(tactic| emit_decoded_step 120 at 602 encodedWidth 5 opcodeAST
      parse("movq 0x10(%r12),%rdx") using $hc)
  if row.getNat == 121 then
    return ← `(tactic| emit_decoded_step 121 at 607 encodedWidth 3 opcodeAST
      parse("testq %rdi,%rdi") using $hc)
  if row.getNat == 122 then
    return ← `(tactic| emit_decoded_step 122 at 610 encodedWidth 6 opcodeAST
      parse("je emit_u876") using $hc)
  if row.getNat == 123 then
    return ← `(tactic| emit_decoded_step 123 at 616 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rsi") using $hc)
  if row.getNat == 124 then
    return ← `(tactic| emit_decoded_step 124 at 620 encodedWidth 6 opcodeAST
      parse("jne emit_u893") using $hc)
  if row.getNat == 125 then
    return ← `(tactic| emit_decoded_step 125 at 626 encodedWidth 2 opcodeAST
      parse("xorl %eax,%eax") using $hc)
  if row.getNat == 126 then
    return ← `(tactic| emit_decoded_step 126 at 628 encodedWidth 3 opcodeAST
      parse("movq %rax,%rcx") using $hc)
  if row.getNat == 127 then
    return ← `(tactic| emit_decoded_step 127 at 631 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%rcx") using $hc)
  if row.getNat == 128 then
    return ← `(tactic| emit_decoded_step 128 at 635 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%rcx") using $hc)
  if row.getNat == 129 then
    return ← `(tactic| emit_decoded_step 129 at 638 encodedWidth 6 opcodeAST
      parse("jae emit_u1031") using $hc)
  if row.getNat == 130 then
    return ← `(tactic| emit_decoded_step 130 at 644 encodedWidth 4 opcodeAST
      parse("movq (%rdi,%rcx,8),%rdx") using $hc)
  if row.getNat == 131 then
    return ← `(tactic| emit_decoded_step 131 at 648 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (483)))))] using $hc)
  if row.getNat == 132 then
    return ← `(tactic| emit_decoded_step 132 at 653 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 133 then
    return ← `(tactic| emit_decoded_step 133 at 655 encodedWidth 3 opcodeAST
      parse("movq %rsi,(%rbx)") using $hc)
  if row.getNat == 134 then
    return ← `(tactic| emit_decoded_step 134 at 658 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (930)))))] using $hc)
  if row.getNat == 135 then
    return ← `(tactic| emit_decoded_step 135 at 663 encodedWidth 3 opcodeAST
      parse("cmpl $0x4,%eax") using $hc)
  if row.getNat == 136 then
    return ← `(tactic| emit_decoded_step 136 at 666 encodedWidth 6 opcodeAST
      parse("jne emit_u801") using $hc)
  if row.getNat == 137 then
    return ← `(tactic| emit_decoded_step 137 at 672 encodedWidth 5 opcodeAST
      parse("movq 0x20(%r12),%rax") using $hc)
  if row.getNat == 138 then
    return ← `(tactic| emit_decoded_step 138 at 677 encodedWidth 5 opcodeAST
      parse("movq 0x28(%r12),%r13") using $hc)
  if row.getNat == 139 then
    return ← `(tactic| emit_decoded_step 139 at 682 encodedWidth 5 opcodeAST
      parse("shldq $0x3d,%rax,%r13") using $hc)
  if row.getNat == 140 then
    return ← `(tactic| emit_decoded_step 140 at 687 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%r9") using $hc)
  if row.getNat == 141 then
    return ← `(tactic| emit_decoded_step 141 at 690 encodedWidth 6 opcodeAST
      parse("jb emit_u1625") using $hc)
  if row.getNat == 142 then
    return ← `(tactic| emit_decoded_step 142 at 696 encodedWidth 5 opcodeAST
      parse("movq %rax,0x8(%rsp)") using $hc)
  if row.getNat == 143 then
    return ← `(tactic| emit_decoded_step 143 at 701 encodedWidth 5 opcodeAST
      parse("movq 0x18(%r12),%rbp") using $hc)
  if row.getNat == 144 then
    return ← `(tactic| emit_decoded_step 144 at 706 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%rbp") using $hc)
  if row.getNat == 145 then
    return ← `(tactic| emit_decoded_step 145 at 709 encodedWidth 6 opcodeAST
      parse("jb emit_u1653") using $hc)
  if row.getNat == 146 then
    return ← `(tactic| emit_decoded_step 146 at 715 encodedWidth 3 opcodeAST
      parse("movq %r9,%r15") using $hc)
  if row.getNat == 147 then
    return ← `(tactic| emit_decoded_step 147 at 718 encodedWidth 5 opcodeAST
      parse("movq 0x10(%r12),%r12") using $hc)
  if row.getNat == 148 then
    return ← `(tactic| emit_decoded_step 148 at 723 encodedWidth 3 opcodeAST
      parse("movq %r14,%rdi") using $hc)
  if row.getNat == 149 then
    return ← `(tactic| emit_decoded_step 149 at 726 encodedWidth 3 opcodeAST
      parse("movq %r12,%rsi") using $hc)
  if row.getNat == 150 then
    return ← `(tactic| emit_decoded_step 150 at 729 encodedWidth 3 opcodeAST
      parse("movq %r13,%rdx") using $hc)
  if row.getNat == 151 then
    return ← `(tactic| emit_decoded_step 151 at 732 encodedWidth 6 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (109998)))))] using $hc)
  if row.getNat == 152 then
    return ← `(tactic| emit_decoded_step 152 at 738 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%rbp") using $hc)
  if row.getNat == 153 then
    return ← `(tactic| emit_decoded_step 153 at 741 encodedWidth 6 opcodeAST
      parse("jbe emit_u1275") using $hc)
  if row.getNat == 154 then
    return ← `(tactic| emit_decoded_step 154 at 747 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%r15") using $hc)
  if row.getNat == 155 then
    return ← `(tactic| emit_decoded_step 155 at 750 encodedWidth 6 opcodeAST
      parse("jbe emit_u1694") using $hc)
  if row.getNat == 156 then
    return ← `(tactic| emit_decoded_step 156 at 756 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .r12), idx := some ⟨.r13, .W8⟩, disp := .int64 (0) })))] using $hc)
  if row.getNat == 157 then
    return ← `(tactic| emit_decoded_step 157 at 761 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%r13),%rcx") using $hc)
  if row.getNat == 158 then
    return ← `(tactic| emit_decoded_step 158 at 765 encodedWidth 3 opcodeAST
      parse("cmpq %rbp,%rcx") using $hc)
  if row.getNat == 159 then
    return ← `(tactic| emit_decoded_step 159 at 768 encodedWidth 2 opcodeAST
      parse("jne emit_u789") using $hc)
  if row.getNat == 160 then
    return ← `(tactic| emit_decoded_step 160 at 770 encodedWidth 5 opcodeAST
      parse("movq 0x8(%rsp),%rcx") using $hc)
  if row.getNat == 161 then
    return ← `(tactic| emit_decoded_step 161 at 775 encodedWidth 4 opcodeAST
      parse("andq $0x7,%rcx") using $hc)
  if row.getNat == 162 then
    return ← `(tactic| emit_decoded_step 162 at 779 encodedWidth 2 opcodeAST
      parse("je emit_u789") using $hc)
  if row.getNat == 163 then
    return ← `(tactic| emit_decoded_step 163 at 781 encodedWidth 2 opcodeAST
      parse("movb $0xff,%dl") using $hc)
  if row.getNat == 164 then
    return ← `(tactic| emit_decoded_step 164 at 783 encodedWidth 2 opcodeAST
      parse("shlb %cl,%dl") using $hc)
  if row.getNat == 165 then
    return ← `(tactic| emit_decoded_step 165 at 785 encodedWidth 2 opcodeAST
      parse("notb %dl") using $hc)
  if row.getNat == 166 then
    return ← `(tactic| emit_decoded_step 166 at 787 encodedWidth 2 opcodeAST
      parse("andb %dl,%al") using $hc)
  if row.getNat == 167 then
    return ← `(tactic| emit_decoded_step 167 at 789 encodedWidth 4 opcodeAST
      parse("movb %al,(%r14,%r13,1)") using $hc)
  if row.getNat == 168 then
    return ← `(tactic| emit_decoded_step 168 at 793 encodedWidth 3 opcodeAST
      parse("movq %rbp,(%rbx)") using $hc)
  if row.getNat == 169 then
    return ← `(tactic| emit_decoded_step 169 at 796 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (792)))))] using $hc)
  if row.getNat == 170 then
    return ← `(tactic| emit_decoded_step 170 at 801 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 171 then
    return ← `(tactic| emit_decoded_step 171 at 808 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 172 then
    return ← `(tactic| emit_decoded_step 172 at 816 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x10(%rbx)") using $hc)
  if row.getNat == 173 then
    return ← `(tactic| emit_decoded_step 173 at 824 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x18(%rbx)") using $hc)
  if row.getNat == 174 then
    return ← `(tactic| emit_decoded_step 174 at 832 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 175 then
    return ← `(tactic| emit_decoded_step 175 at 840 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x28(%rbx)") using $hc)
  if row.getNat == 176 then
    return ← `(tactic| emit_decoded_step 176 at 848 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 177 then
    return ← `(tactic| emit_decoded_step 177 at 856 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 178 then
    return ← `(tactic| emit_decoded_step 178 at 864 encodedWidth 7 opcodeAST
      parse("movl $0x1,0x40(%rbx)") using $hc)
  if row.getNat == 179 then
    return ← `(tactic| emit_decoded_step 179 at 871 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (724)))))] using $hc)
  if row.getNat == 180 then
    return ← `(tactic| emit_decoded_step 180 at 876 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rsi") using $hc)
  if row.getNat == 181 then
    return ← `(tactic| emit_decoded_step 181 at 880 encodedWidth 6 opcodeAST
      parse("jne emit_u1035") using $hc)
  if row.getNat == 182 then
    return ← `(tactic| emit_decoded_step 182 at 886 encodedWidth 2 opcodeAST
      parse("xorl %eax,%eax") using $hc)
  if row.getNat == 183 then
    return ← `(tactic| emit_decoded_step 183 at 888 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (243)))))] using $hc)
  Lean.Macro.throwErrorAt row "not a middle primitive emit instruction index"

macro "emit_step_high " row:num " using " hc:term : tactic => do
  if row.getNat == 184 then
    return ← `(tactic| emit_decoded_step 184 at 893 encodedWidth 3 opcodeAST
      parse("movq %rsi,%r8") using $hc)
  if row.getNat == 185 then
    return ← `(tactic| emit_decoded_step 185 at 896 encodedWidth 4 opcodeAST
      parse("andq $0xfffffffffffffffe,%r8") using $hc)
  if row.getNat == 186 then
    return ← `(tactic| emit_decoded_step 186 at 900 encodedWidth 3 opcodeAST
      parse("xorl %r9d,%r9d") using $hc)
  if row.getNat == 187 then
    return ← `(tactic| emit_decoded_step 187 at 903 encodedWidth 2 opcodeAST
      parse("xorl %eax,%eax") using $hc)
  if row.getNat == 188 then
    return ← `(tactic| emit_decoded_step 188 at 905 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (39)))))] using $hc)
  if row.getNat == 189 then
    return ← `(tactic| emit_decoded_step 189 at 912 encodedWidth 4 opcodeAST
      parse("movq (%rdi,%r10,8),%r10") using $hc)
  if row.getNat == 190 then
    return ← `(tactic| emit_decoded_step 190 at 916 encodedWidth 3 opcodeAST
      parse("movl %r9d,%ecx") using $hc)
  if row.getNat == 191 then
    return ← `(tactic| emit_decoded_step 191 at 919 encodedWidth 3 opcodeAST
      parse("andb $0x30,%cl") using $hc)
  if row.getNat == 192 then
    return ← `(tactic| emit_decoded_step 192 at 922 encodedWidth 3 opcodeAST
      parse("orb $0x8,%cl") using $hc)
  if row.getNat == 193 then
    return ← `(tactic| emit_decoded_step 193 at 925 encodedWidth 3 opcodeAST
      parse("shrq %cl,%r10") using $hc)
  if row.getNat == 194 then
    return ← `(tactic| emit_decoded_step 194 at 928 encodedWidth 5 opcodeAST
      parse("movb %r10b,0x1(%r14,%rax,1)") using $hc)
  if row.getNat == 195 then
    return ← `(tactic| emit_decoded_step 195 at 933 encodedWidth 4 opcodeAST
      parse("addq $0x2,%rax") using $hc)
  if row.getNat == 196 then
    return ← `(tactic| emit_decoded_step 196 at 937 encodedWidth 4 opcodeAST
      parse("addq $0x10,%r9") using $hc)
  if row.getNat == 197 then
    return ← `(tactic| emit_decoded_step 197 at 941 encodedWidth 3 opcodeAST
      parse("cmpq %rax,%r8") using $hc)
  if row.getNat == 198 then
    return ← `(tactic| emit_decoded_step 198 at 944 encodedWidth 2 opcodeAST
      parse("je emit_u1002") using $hc)
  if row.getNat == 199 then
    return ← `(tactic| emit_decoded_step 199 at 946 encodedWidth 3 opcodeAST
      parse("movq %rax,%r10") using $hc)
  if row.getNat == 200 then
    return ← `(tactic| emit_decoded_step 200 at 949 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%r10") using $hc)
  if row.getNat == 201 then
    return ← `(tactic| emit_decoded_step 201 at 953 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%r10") using $hc)
  if row.getNat == 202 then
    return ← `(tactic| emit_decoded_step 202 at 956 encodedWidth 2 opcodeAST
      parse("jae emit_u976") using $hc)
  if row.getNat == 203 then
    return ← `(tactic| emit_decoded_step 203 at 958 encodedWidth 4 opcodeAST
      parse("movq (%rdi,%r10,8),%r11") using $hc)
  if row.getNat == 204 then
    return ← `(tactic| emit_decoded_step 204 at 962 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (15)))))] using $hc)
  if row.getNat == 205 then
    return ← `(tactic| emit_decoded_step 205 at 976 encodedWidth 3 opcodeAST
      parse("xorl %r11d,%r11d") using $hc)
  if row.getNat == 206 then
    return ← `(tactic| emit_decoded_step 206 at 979 encodedWidth 3 opcodeAST
      parse("movl %r9d,%ecx") using $hc)
  if row.getNat == 207 then
    return ← `(tactic| emit_decoded_step 207 at 982 encodedWidth 3 opcodeAST
      parse("andb $0x30,%cl") using $hc)
  if row.getNat == 208 then
    return ← `(tactic| emit_decoded_step 208 at 985 encodedWidth 3 opcodeAST
      parse("shrq %cl,%r11") using $hc)
  if row.getNat == 209 then
    return ← `(tactic| emit_decoded_step 209 at 988 encodedWidth 4 opcodeAST
      parse("movb %r11b,(%r14,%rax,1)") using $hc)
  if row.getNat == 210 then
    return ← `(tactic| emit_decoded_step 210 at 992 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%r10") using $hc)
  if row.getNat == 211 then
    return ← `(tactic| emit_decoded_step 211 at 995 encodedWidth 2 opcodeAST
      parse("jb emit_u912") using $hc)
  if row.getNat == 212 then
    return ← `(tactic| emit_decoded_step 212 at 997 encodedWidth 3 opcodeAST
      parse("xorl %r10d,%r10d") using $hc)
  if row.getNat == 213 then
    return ← `(tactic| emit_decoded_step 213 at 1000 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (-86)))))] using $hc)
  if row.getNat == 214 then
    return ← `(tactic| emit_decoded_step 214 at 1002 encodedWidth 4 opcodeAST
      parse("testb $0x1,%sil") using $hc)
  if row.getNat == 215 then
    return ← `(tactic| emit_decoded_step 215 at 1006 encodedWidth 6 opcodeAST
      parse("je emit_u1147") using $hc)
  if row.getNat == 216 then
    return ← `(tactic| emit_decoded_step 216 at 1012 encodedWidth 3 opcodeAST
      parse("addq %rax,%r14") using $hc)
  if row.getNat == 217 then
    return ← `(tactic| emit_decoded_step 217 at 1015 encodedWidth 3 opcodeAST
      parse("movq %rax,%rcx") using $hc)
  if row.getNat == 218 then
    return ← `(tactic| emit_decoded_step 218 at 1018 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%rcx") using $hc)
  if row.getNat == 219 then
    return ← `(tactic| emit_decoded_step 219 at 1022 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%rcx") using $hc)
  if row.getNat == 220 then
    return ← `(tactic| emit_decoded_step 220 at 1025 encodedWidth 6 opcodeAST
      parse("jb emit_u644") using $hc)
  if row.getNat == 221 then
    return ← `(tactic| emit_decoded_step 221 at 1031 encodedWidth 2 opcodeAST
      parse("xorl %edx,%edx") using $hc)
  if row.getNat == 222 then
    return ← `(tactic| emit_decoded_step 222 at 1033 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (101)))))] using $hc)
  if row.getNat == 223 then
    return ← `(tactic| emit_decoded_step 223 at 1035 encodedWidth 3 opcodeAST
      parse("movq %rsi,%rdi") using $hc)
  if row.getNat == 224 then
    return ← `(tactic| emit_decoded_step 224 at 1038 encodedWidth 4 opcodeAST
      parse("andq $0xfffffffffffffffe,%rdi") using $hc)
  if row.getNat == 225 then
    return ← `(tactic| emit_decoded_step 225 at 1042 encodedWidth 3 opcodeAST
      parse("xorl %r9d,%r9d") using $hc)
  if row.getNat == 226 then
    return ← `(tactic| emit_decoded_step 226 at 1045 encodedWidth 2 opcodeAST
      parse("xorl %eax,%eax") using $hc)
  if row.getNat == 227 then
    return ← `(tactic| emit_decoded_step 227 at 1047 encodedWidth 9 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 9))] using $hc)
  if row.getNat == 228 then
    return ← `(tactic| emit_decoded_step 228 at 1056 encodedWidth 3 opcodeAST
      parse("movq %rax,%r8") using $hc)
  if row.getNat == 229 then
    return ← `(tactic| emit_decoded_step 229 at 1059 encodedWidth 4 opcodeAST
      parse("cmpq $0x8,%rax") using $hc)
  if row.getNat == 230 then
    return ← `(tactic| emit_decoded_step 230 at 1063 encodedWidth 6 opcodeAST
      parse("movl $0x0,%r10d") using $hc)
  if row.getNat == 231 then
    return ← `(tactic| emit_decoded_step 231 at 1069 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W64 (.cmovcc .c (.low .r10 .W64) (.reg (.low .rdx .W64))))] using $hc)
  if row.getNat == 232 then
    return ← `(tactic| emit_decoded_step 232 at 1073 encodedWidth 3 opcodeAST
      parse("movl %r9d,%ecx") using $hc)
  if row.getNat == 233 then
    return ← `(tactic| emit_decoded_step 233 at 1076 encodedWidth 3 opcodeAST
      parse("andb $0x30,%cl") using $hc)
  if row.getNat == 234 then
    return ← `(tactic| emit_decoded_step 234 at 1079 encodedWidth 3 opcodeAST
      parse("movq %r10,%rax") using $hc)
  if row.getNat == 235 then
    return ← `(tactic| emit_decoded_step 235 at 1082 encodedWidth 3 opcodeAST
      parse("shrq %cl,%rax") using $hc)
  if row.getNat == 236 then
    return ← `(tactic| emit_decoded_step 236 at 1085 encodedWidth 4 opcodeAST
      parse("movb %al,(%r14,%r8,1)") using $hc)
  if row.getNat == 237 then
    return ← `(tactic| emit_decoded_step 237 at 1089 encodedWidth 3 opcodeAST
      parse("orb $0x8,%cl") using $hc)
  if row.getNat == 238 then
    return ← `(tactic| emit_decoded_step 238 at 1092 encodedWidth 3 opcodeAST
      parse("shrq %cl,%r10") using $hc)
  if row.getNat == 239 then
    return ← `(tactic| emit_decoded_step 239 at 1095 encodedWidth 4 opcodeAST
      parse("leaq 0x2(%r8),%rax") using $hc)
  if row.getNat == 240 then
    return ← `(tactic| emit_decoded_step 240 at 1099 encodedWidth 5 opcodeAST
      parse("movb %r10b,0x1(%r14,%r8,1)") using $hc)
  if row.getNat == 241 then
    return ← `(tactic| emit_decoded_step 241 at 1104 encodedWidth 4 opcodeAST
      parse("addq $0x10,%r9") using $hc)
  if row.getNat == 242 then
    return ← `(tactic| emit_decoded_step 242 at 1108 encodedWidth 3 opcodeAST
      parse("cmpq %rax,%rdi") using $hc)
  if row.getNat == 243 then
    return ← `(tactic| emit_decoded_step 243 at 1111 encodedWidth 2 opcodeAST
      parse("jne emit_u1056") using $hc)
  if row.getNat == 244 then
    return ← `(tactic| emit_decoded_step 244 at 1113 encodedWidth 4 opcodeAST
      parse("testb $0x1,%sil") using $hc)
  if row.getNat == 245 then
    return ← `(tactic| emit_decoded_step 245 at 1117 encodedWidth 2 opcodeAST
      parse("je emit_u1147") using $hc)
  if row.getNat == 246 then
    return ← `(tactic| emit_decoded_step 246 at 1119 encodedWidth 3 opcodeAST
      parse("addq %r8,%r14") using $hc)
  if row.getNat == 247 then
    return ← `(tactic| emit_decoded_step 247 at 1122 encodedWidth 4 opcodeAST
      parse("addq $0x2,%r14") using $hc)
  if row.getNat == 248 then
    return ← `(tactic| emit_decoded_step 248 at 1126 encodedWidth 2 opcodeAST
      parse("xorl %ecx,%ecx") using $hc)
  if row.getNat == 249 then
    return ← `(tactic| emit_decoded_step 249 at 1128 encodedWidth 4 opcodeAST
      parse("cmpq $0x8,%rax") using $hc)
  if row.getNat == 250 then
    return ← `(tactic| emit_decoded_step 250 at 1132 encodedWidth 4 opcodeAST
      parse("cmovae %rcx,%rdx") using $hc)
  if row.getNat == 251 then
    return ← `(tactic| emit_decoded_step 251 at 1136 encodedWidth 3 opcodeAST
      parse("shll $0x3,%eax") using $hc)
  if row.getNat == 252 then
    return ← `(tactic| emit_decoded_step 252 at 1139 encodedWidth 2 opcodeAST
      parse("movl %eax,%ecx") using $hc)
  if row.getNat == 253 then
    return ← `(tactic| emit_decoded_step 253 at 1141 encodedWidth 3 opcodeAST
      parse("shrq %cl,%rdx") using $hc)
  if row.getNat == 254 then
    return ← `(tactic| emit_decoded_step 254 at 1144 encodedWidth 3 opcodeAST
      parse("movb %dl,(%r14)") using $hc)
  if row.getNat == 255 then
    return ← `(tactic| emit_decoded_step 255 at 1147 encodedWidth 3 opcodeAST
      parse("movq %rsi,(%rbx)") using $hc)
  if row.getNat == 256 then
    return ← `(tactic| emit_decoded_step 256 at 1150 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (438)))))] using $hc)
  if row.getNat == 257 then
    return ← `(tactic| emit_decoded_step 257 at 1155 encodedWidth 2 opcodeAST
      parse("movb $0x1,%dl") using $hc)
  if row.getNat == 258 then
    return ← `(tactic| emit_decoded_step 258 at 1157 encodedWidth 3 opcodeAST
      parse("movq %r15,%rsi") using $hc)
  if row.getNat == 259 then
    return ← `(tactic| emit_decoded_step 259 at 1160 encodedWidth 3 opcodeAST
      parse("cmpq %r13,%rsi") using $hc)
  if row.getNat == 260 then
    return ← `(tactic| emit_decoded_step 260 at 1163 encodedWidth 6 opcodeAST
      parse("jbe emit_u1675") using $hc)
  if row.getNat == 261 then
    return ← `(tactic| emit_decoded_step 261 at 1169 encodedWidth 4 opcodeAST
      parse("movb %dl,(%r14,%r13,1)") using $hc)
  if row.getNat == 262 then
    return ← `(tactic| emit_decoded_step 262 at 1173 encodedWidth 3 opcodeAST
      [.instr (.regular .W64 .W64 (.inc (.reg (.low .r13 .W64))))] using $hc)
  if row.getNat == 263 then
    return ← `(tactic| emit_decoded_step 263 at 1176 encodedWidth 3 opcodeAST
      parse("movq %r13,(%rbx)") using $hc)
  if row.getNat == 264 then
    return ← `(tactic| emit_decoded_step 264 at 1179 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (409)))))] using $hc)
  if row.getNat == 265 then
    return ← `(tactic| emit_decoded_step 265 at 1275 encodedWidth 3 opcodeAST
      parse("movq %rbp,(%rbx)") using $hc)
  if row.getNat == 266 then
    return ← `(tactic| emit_decoded_step 266 at 1278 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (310)))))] using $hc)
  if row.getNat == 267 then
    return ← `(tactic| emit_decoded_step 267 at 1593 encodedWidth 7 opcodeAST
      parse("movl $0x0,0x40(%rbx)") using $hc)
  if row.getNat == 268 then
    return ← `(tactic| emit_decoded_step 268 at 1600 encodedWidth 4 opcodeAST
      parse("addq $0x68,%rsp") using $hc)
  if row.getNat == 269 then
    return ← `(tactic| emit_decoded_step 269 at 1604 encodedWidth 1 opcodeAST
      parse("popq %rbx") using $hc)
  if row.getNat == 270 then
    return ← `(tactic| emit_decoded_step 270 at 1605 encodedWidth 2 opcodeAST
      parse("popq %r12") using $hc)
  if row.getNat == 271 then
    return ← `(tactic| emit_decoded_step 271 at 1607 encodedWidth 2 opcodeAST
      parse("popq %r13") using $hc)
  if row.getNat == 272 then
    return ← `(tactic| emit_decoded_step 272 at 1609 encodedWidth 2 opcodeAST
      parse("popq %r14") using $hc)
  if row.getNat == 273 then
    return ← `(tactic| emit_decoded_step 273 at 1611 encodedWidth 2 opcodeAST
      parse("popq %r15") using $hc)
  if row.getNat == 274 then
    return ← `(tactic| emit_decoded_step 274 at 1613 encodedWidth 1 opcodeAST
      parse("popq %rbp") using $hc)
  if row.getNat == 275 then
    return ← `(tactic| emit_decoded_step 275 at 1614 encodedWidth 1 opcodeAST
      parse("retq ") using $hc)
  Lean.Macro.throwErrorAt row "not a primitive emit instruction index"

macro "emit_step " row:num " using " hc:term : tactic => do
  if row.getNat < 92 then
    return ← `(tactic| emit_step_low $row using $hc)
  if row.getNat < 184 then
    return ← `(tactic| emit_step_mid $row using $hc)
  return ← `(tactic| emit_step_high $row using $hc)

end SszX86.Emit

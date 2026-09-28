import SszX86.MeasureImpl
import SszX86.DispatchPush

namespace SszX86.Measure
open Kraken.X64.Parser
open BoolCodec UintCodec

abbrev step (e : Executable) := BoolCodec.step e

/-- One concrete fetched row, without unfolding the whole execution state. -/
macro "measure_decoded_step " row:num " at " pc:num " encodedWidth " bytes:num " opcodeAST " instructions:term
    " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.Measure.program) (n := $row)
     (by rw [SszX86.Measure.program_length]; decide)
   have fetched := SszX86.Measure.step_at _ _ $hc
     (($pc, $bytes, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Measure.directives, SszX86.Measure.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "measure_step_chunk0 " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| measure_decoded_step 0 at 0 encodedWidth 1 opcodeAST
      parse("pushq %rbp") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| measure_decoded_step 1 at 1 encodedWidth 2 opcodeAST
      parse("pushq %r15") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| measure_decoded_step 2 at 3 encodedWidth 2 opcodeAST
      parse("pushq %r14") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| measure_decoded_step 3 at 5 encodedWidth 2 opcodeAST
      parse("pushq %r13") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| measure_decoded_step 4 at 7 encodedWidth 2 opcodeAST
      parse("pushq %r12") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| measure_decoded_step 5 at 9 encodedWidth 1 opcodeAST
      parse("pushq %rbx") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| measure_decoded_step 6 at 10 encodedWidth 7 opcodeAST
      parse("subq $0xd8,%rsp") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| measure_decoded_step 7 at 17 encodedWidth 3 opcodeAST
      parse("movq %rdx,%r14") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| measure_decoded_step 8 at 20 encodedWidth 3 opcodeAST
      parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| measure_decoded_step 9 at 23 encodedWidth 3 opcodeAST
      parse("movq (%rsi),%rdx") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| measure_decoded_step 10 at 26 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W32 (.movzx (.reg (.low .rax .W32)) (.mem (w := .W8) { base := some (.reg .r14), idx := none, disp := .int64 (0) })))] using $hc)
  if row.getNat == 11 then
    return ← `(tactic| measure_decoded_step 11 at 30 encodedWidth 7 opcodeAST
      [.instr (.regular .W64 .W64 (.lea .rdi {base := some .rip, idx := none, disp := .int64 (-89353)}))] using $hc)
  if row.getNat == 12 then
    return ← `(tactic| measure_decoded_step 12 at 37 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W64 (.movsx (.reg .rdx) (.mem (w := .W32) {base := some (.reg .rdi), idx := some ⟨.rdx, .W32⟩})))] using $hc)
  if row.getNat == 13 then
    return ← `(tactic| measure_decoded_step 13 at 41 encodedWidth 3 opcodeAST
      parse("addq %rdi,%rdx") using $hc)
  if row.getNat == 14 then
    return ← `(tactic| measure_decoded_step 14 at 44 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.reg .rdx)))] using $hc)
  if row.getNat == 15 then
    return ← `(tactic| measure_decoded_step 15 at 46 encodedWidth 2 opcodeAST
      parse("testb %al,%al") using $hc)
  if row.getNat == 16 then
    return ← `(tactic| measure_decoded_step 16 at 48 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 17 then
    return ← `(tactic| measure_decoded_step 17 at 54 encodedWidth 5 opcodeAST
      parse("movl $0x1,%eax") using $hc)
  if row.getNat == 18 then
    return ← `(tactic| measure_decoded_step 18 at 59 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2986)))))] using $hc)
  if row.getNat == 19 then
    return ← `(tactic| measure_decoded_step 19 at 82 encodedWidth 2 opcodeAST
      parse("cmpb $0x3,%al") using $hc)
  if row.getNat == 20 then
    return ← `(tactic| measure_decoded_step 20 at 84 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 21 then
    return ← `(tactic| measure_decoded_step 21 at 90 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%r8") using $hc)
  if row.getNat == 22 then
    return ← `(tactic| measure_decoded_step 22 at 94 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rdi") using $hc)
  if row.getNat == 23 then
    return ← `(tactic| measure_decoded_step 23 at 98 encodedWidth 4 opcodeAST
      parse("movq 0x20(%r14),%rax") using $hc)
  if row.getNat == 24 then
    return ← `(tactic| measure_decoded_step 24 at 102 encodedWidth 4 opcodeAST
      parse("movq 0x28(%r14),%rdx") using $hc)
  if row.getNat == 25 then
    return ← `(tactic| measure_decoded_step 25 at 106 encodedWidth 3 opcodeAST
      parse("testq %r8,%r8") using $hc)
  if row.getNat == 26 then
    return ← `(tactic| measure_decoded_step 26 at 109 encodedWidth 6 opcodeAST
      parse("je measure_u1654") using $hc)
  if row.getNat == 27 then
    return ← `(tactic| measure_decoded_step 27 at 115 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%rdi),%r9") using $hc)
  if row.getNat == 28 then
    return ← `(tactic| measure_decoded_step 28 at 119 encodedWidth 9 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 9))] using $hc)
  if row.getNat == 29 then
    return ← `(tactic| measure_decoded_step 29 at 128 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%r9") using $hc)
  if row.getNat == 30 then
    return ← `(tactic| measure_decoded_step 30 at 132 encodedWidth 6 opcodeAST
      parse("je measure_u1854") using $hc)
  if row.getNat == 31 then
    return ← `(tactic| measure_decoded_step 31 at 138 encodedWidth 4 opcodeAST
      parse("leaq -0x1(%r9),%r10") using $hc)
  if row.getNat == 32 then
    return ← `(tactic| measure_decoded_step 32 at 142 encodedWidth 6 opcodeAST
      parse("cmpq $0x0,-0x10(%r8,%r9,8)") using $hc)
  if row.getNat == 33 then
    return ← `(tactic| measure_decoded_step 33 at 148 encodedWidth 3 opcodeAST
      parse("movq %r10,%r9") using $hc)
  if row.getNat == 34 then
    return ← `(tactic| measure_decoded_step 34 at 151 encodedWidth 2 opcodeAST
      parse("je measure_u128") using $hc)
  if row.getNat == 35 then
    return ← `(tactic| measure_decoded_step 35 at 153 encodedWidth 4 opcodeAST
      parse("cmpq $0x3,%r10") using $hc)
  if row.getNat == 36 then
    return ← `(tactic| measure_decoded_step 36 at 157 encodedWidth 6 opcodeAST
      parse("jb measure_u1863") using $hc)
  if row.getNat == 37 then
    return ← `(tactic| measure_decoded_step 37 at 163 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2637)))))] using $hc)
  if row.getNat == 38 then
    return ← `(tactic| measure_decoded_step 38 at 529 encodedWidth 2 opcodeAST
      parse("cmpb $0x2,%al") using $hc)
  if row.getNat == 39 then
    return ← `(tactic| measure_decoded_step 39 at 531 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 40 then
    return ← `(tactic| measure_decoded_step 40 at 537 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rcx") using $hc)
  if row.getNat == 41 then
    return ← `(tactic| measure_decoded_step 41 at 541 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rdx") using $hc)
  if row.getNat == 42 then
    return ← `(tactic| measure_decoded_step 42 at 545 encodedWidth 4 opcodeAST
      parse("movq 0x10(%r14),%rax") using $hc)
  if row.getNat == 43 then
    return ← `(tactic| measure_decoded_step 43 at 549 encodedWidth 3 opcodeAST
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 44 then
    return ← `(tactic| measure_decoded_step 44 at 552 encodedWidth 6 opcodeAST
      parse("je measure_u1662") using $hc)
  if row.getNat == 45 then
    return ← `(tactic| measure_decoded_step 45 at 558 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%rdx),%rsi") using $hc)
  if row.getNat == 46 then
    return ← `(tactic| measure_decoded_step 46 at 562 encodedWidth 10 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 10))] using $hc)
  if row.getNat == 47 then
    return ← `(tactic| measure_decoded_step 47 at 572 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 4))] using $hc)
  if row.getNat == 48 then
    return ← `(tactic| measure_decoded_step 48 at 576 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rsi") using $hc)
  if row.getNat == 49 then
    return ← `(tactic| measure_decoded_step 49 at 580 encodedWidth 6 opcodeAST
      parse("je measure_u1885") using $hc)
  if row.getNat == 50 then
    return ← `(tactic| measure_decoded_step 50 at 586 encodedWidth 4 opcodeAST
      parse("leaq -0x1(%rsi),%rdi") using $hc)
  if row.getNat == 51 then
    return ← `(tactic| measure_decoded_step 51 at 590 encodedWidth 6 opcodeAST
      parse("cmpq $0x0,-0x10(%rcx,%rsi,8)") using $hc)
  if row.getNat == 52 then
    return ← `(tactic| measure_decoded_step 52 at 596 encodedWidth 3 opcodeAST
      parse("movq %rdi,%rsi") using $hc)
  if row.getNat == 53 then
    return ← `(tactic| measure_decoded_step 53 at 599 encodedWidth 2 opcodeAST
      parse("je measure_u576") using $hc)
  if row.getNat == 54 then
    return ← `(tactic| measure_decoded_step 54 at 601 encodedWidth 4 opcodeAST
      parse("cmpq $0x3,%rdi") using $hc)
  if row.getNat == 55 then
    return ← `(tactic| measure_decoded_step 55 at 605 encodedWidth 6 opcodeAST
      parse("jb measure_u1894") using $hc)
  if row.getNat == 56 then
    return ← `(tactic| measure_decoded_step 56 at 611 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (2479)))))] using $hc)
  if row.getNat == 57 then
    return ← `(tactic| measure_decoded_step 57 at 616 encodedWidth 2 opcodeAST
      parse("cmpb $0x2,%al") using $hc)
  if row.getNat == 58 then
    return ← `(tactic| measure_decoded_step 58 at 618 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 59 then
    return ← `(tactic| measure_decoded_step 59 at 624 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rcx") using $hc)
  if row.getNat == 60 then
    return ← `(tactic| measure_decoded_step 60 at 628 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rdx") using $hc)
  if row.getNat == 61 then
    return ← `(tactic| measure_decoded_step 61 at 632 encodedWidth 4 opcodeAST
      parse("movq 0x10(%r14),%rax") using $hc)
  if row.getNat == 62 then
    return ← `(tactic| measure_decoded_step 62 at 636 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 63 then
    return ← `(tactic| measure_decoded_step 63 at 638 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk1 " row:num " using " hc:term : tactic => do
  if row.getNat == 64 then
    return ← `(tactic| measure_decoded_step 64 at 641 encodedWidth 4 opcodeAST
      parse("setne %dil") using $hc)
  if row.getNat == 65 then
    return ← `(tactic| measure_decoded_step 65 at 645 encodedWidth 3 opcodeAST
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 66 then
    return ← `(tactic| measure_decoded_step 66 at 648 encodedWidth 6 opcodeAST
      parse("je measure_u1672") using $hc)
  if row.getNat == 67 then
    return ← `(tactic| measure_decoded_step 67 at 654 encodedWidth 3 opcodeAST
      parse("movb %dil,%sil") using $hc)
  if row.getNat == 68 then
    return ← `(tactic| measure_decoded_step 68 at 657 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%rdx),%rdi") using $hc)
  if row.getNat == 69 then
    return ← `(tactic| measure_decoded_step 69 at 661 encodedWidth 10 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 10))] using $hc)
  if row.getNat == 70 then
    return ← `(tactic| measure_decoded_step 70 at 671 encodedWidth 1 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 1))] using $hc)
  if row.getNat == 71 then
    return ← `(tactic| measure_decoded_step 71 at 672 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rdi") using $hc)
  if row.getNat == 72 then
    return ← `(tactic| measure_decoded_step 72 at 676 encodedWidth 6 opcodeAST
      parse("je measure_u1916") using $hc)
  if row.getNat == 73 then
    return ← `(tactic| measure_decoded_step 73 at 682 encodedWidth 4 opcodeAST
      parse("leaq -0x1(%rdi),%r8") using $hc)
  if row.getNat == 74 then
    return ← `(tactic| measure_decoded_step 74 at 686 encodedWidth 6 opcodeAST
      parse("cmpq $0x0,-0x10(%rcx,%rdi,8)") using $hc)
  if row.getNat == 75 then
    return ← `(tactic| measure_decoded_step 75 at 692 encodedWidth 3 opcodeAST
      parse("movq %r8,%rdi") using $hc)
  if row.getNat == 76 then
    return ← `(tactic| measure_decoded_step 76 at 695 encodedWidth 2 opcodeAST
      parse("je measure_u672") using $hc)
  if row.getNat == 77 then
    return ← `(tactic| measure_decoded_step 77 at 697 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1217)))))] using $hc)
  if row.getNat == 78 then
    return ← `(tactic| measure_decoded_step 78 at 795 encodedWidth 2 opcodeAST
      parse("cmpb $0x1,%al") using $hc)
  if row.getNat == 79 then
    return ← `(tactic| measure_decoded_step 79 at 797 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 80 then
    return ← `(tactic| measure_decoded_step 80 at 803 encodedWidth 4 opcodeAST
      parse("movq 0x8(%r14),%rdx") using $hc)
  if row.getNat == 81 then
    return ← `(tactic| measure_decoded_step 81 at 807 encodedWidth 4 opcodeAST
      parse("movq 0x10(%r14),%rcx") using $hc)
  if row.getNat == 82 then
    return ← `(tactic| measure_decoded_step 82 at 811 encodedWidth 3 opcodeAST
      parse("testq %rdx,%rdx") using $hc)
  if row.getNat == 83 then
    return ← `(tactic| measure_decoded_step 83 at 814 encodedWidth 6 opcodeAST
      parse("je measure_u1720") using $hc)
  if row.getNat == 84 then
    return ← `(tactic| measure_decoded_step 84 at 820 encodedWidth 3 opcodeAST
      [.instr (.regular .W64 .W64 (.inc (.reg (.low .rcx .W64))))] using $hc)
  if row.getNat == 85 then
    return ← `(tactic| measure_decoded_step 85 at 823 encodedWidth 2 opcodeAST
      parse("xorl %edi,%edi") using $hc)
  if row.getNat == 86 then
    return ← `(tactic| measure_decoded_step 86 at 825 encodedWidth 3 opcodeAST
      parse("movq %rcx,%rax") using $hc)
  if row.getNat == 87 then
    return ← `(tactic| measure_decoded_step 87 at 828 encodedWidth 4 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 4))] using $hc)
  if row.getNat == 88 then
    return ← `(tactic| measure_decoded_step 88 at 832 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rax") using $hc)
  if row.getNat == 89 then
    return ← `(tactic| measure_decoded_step 89 at 836 encodedWidth 6 opcodeAST
      parse("je measure_u2011") using $hc)
  if row.getNat == 90 then
    return ← `(tactic| measure_decoded_step 90 at 842 encodedWidth 5 opcodeAST
      parse("movq -0x10(%rdx,%rax,8),%rcx") using $hc)
  if row.getNat == 91 then
    return ← `(tactic| measure_decoded_step 91 at 847 encodedWidth 3 opcodeAST
      parse("decq %rax") using $hc)
  if row.getNat == 92 then
    return ← `(tactic| measure_decoded_step 92 at 850 encodedWidth 3 opcodeAST
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 93 then
    return ← `(tactic| measure_decoded_step 93 at 853 encodedWidth 2 opcodeAST
      parse("je measure_u832") using $hc)
  if row.getNat == 94 then
    return ← `(tactic| measure_decoded_step 94 at 855 encodedWidth 3 opcodeAST
      parse("movq %rax,%rdx") using $hc)
  if row.getNat == 95 then
    return ← `(tactic| measure_decoded_step 95 at 858 encodedWidth 4 opcodeAST
      parse("shrq $0x3a,%rdx") using $hc)
  if row.getNat == 96 then
    return ← `(tactic| measure_decoded_step 96 at 862 encodedWidth 4 opcodeAST
      parse("shlq $0x6,%rax") using $hc)
  if row.getNat == 97 then
    return ← `(tactic| measure_decoded_step 97 at 866 encodedWidth 4 opcodeAST
      parse("addq $0xffffffffffffffc7,%rax") using $hc)
  if row.getNat == 98 then
    return ← `(tactic| measure_decoded_step 98 at 870 encodedWidth 4 opcodeAST
      parse("adcq $0xffffffffffffffff,%rdx") using $hc)
  if row.getNat == 99 then
    return ← `(tactic| measure_decoded_step 99 at 874 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (857)))))] using $hc)
  if row.getNat == 100 then
    return ← `(tactic| measure_decoded_step 100 at 879 encodedWidth 2 opcodeAST
      parse("cmpb $0x3,%al") using $hc)
  if row.getNat == 101 then
    return ← `(tactic| measure_decoded_step 101 at 881 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 102 then
    return ← `(tactic| measure_decoded_step 102 at 887 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%r13") using $hc)
  if row.getNat == 103 then
    return ← `(tactic| measure_decoded_step 103 at 891 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%r12") using $hc)
  if row.getNat == 104 then
    return ← `(tactic| measure_decoded_step 104 at 895 encodedWidth 4 opcodeAST
      parse("movq 0x20(%r14),%r15") using $hc)
  if row.getNat == 105 then
    return ← `(tactic| measure_decoded_step 105 at 899 encodedWidth 4 opcodeAST
      parse("movq 0x28(%r14),%r14") using $hc)
  if row.getNat == 106 then
    return ← `(tactic| measure_decoded_step 106 at 903 encodedWidth 3 opcodeAST
      parse("testq %r14,%r14") using $hc)
  if row.getNat == 107 then
    return ← `(tactic| measure_decoded_step 107 at 906 encodedWidth 6 opcodeAST
      parse("jne measure_u1235") using $hc)
  if row.getNat == 108 then
    return ← `(tactic| measure_decoded_step 108 at 912 encodedWidth 5 opcodeAST
      parse("movq %rcx,0x8(%rsp)") using $hc)
  if row.getNat == 109 then
    return ← `(tactic| measure_decoded_step 109 at 917 encodedWidth 2 opcodeAST
      parse("xorl %ebp,%ebp") using $hc)
  if row.getNat == 110 then
    return ← `(tactic| measure_decoded_step 110 at 919 encodedWidth 5 opcodeAST
      parse("movq %r15,0x10(%rsp)") using $hc)
  if row.getNat == 111 then
    return ← `(tactic| measure_decoded_step 111 at 924 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (412)))))] using $hc)
  if row.getNat == 112 then
    return ← `(tactic| measure_decoded_step 112 at 929 encodedWidth 2 opcodeAST
      parse("cmpb $0x3,%al") using $hc)
  if row.getNat == 113 then
    return ← `(tactic| measure_decoded_step 113 at 931 encodedWidth 6 opcodeAST
      parse("jne measure_u3265") using $hc)
  if row.getNat == 114 then
    return ← `(tactic| measure_decoded_step 114 at 937 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rax") using $hc)
  if row.getNat == 115 then
    return ← `(tactic| measure_decoded_step 115 at 941 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rbp") using $hc)
  if row.getNat == 116 then
    return ← `(tactic| measure_decoded_step 116 at 945 encodedWidth 4 opcodeAST
      parse("movq 0x18(%rsi),%r12") using $hc)
  if row.getNat == 117 then
    return ← `(tactic| measure_decoded_step 117 at 949 encodedWidth 4 opcodeAST
      parse("movq 0x20(%r14),%r15") using $hc)
  if row.getNat == 118 then
    return ← `(tactic| measure_decoded_step 118 at 953 encodedWidth 4 opcodeAST
      parse("movq 0x28(%r14),%r14") using $hc)
  if row.getNat == 119 then
    return ← `(tactic| measure_decoded_step 119 at 957 encodedWidth 3 opcodeAST
      parse("testq %r14,%r14") using $hc)
  if row.getNat == 120 then
    return ← `(tactic| measure_decoded_step 120 at 960 encodedWidth 6 opcodeAST
      parse("jne measure_u1425") using $hc)
  if row.getNat == 121 then
    return ← `(tactic| measure_decoded_step 121 at 966 encodedWidth 3 opcodeAST
      parse("xorl %r13d,%r13d") using $hc)
  if row.getNat == 122 then
    return ← `(tactic| measure_decoded_step 122 at 969 encodedWidth 3 opcodeAST
      parse("movq %r15,%rsi") using $hc)
  if row.getNat == 123 then
    return ← `(tactic| measure_decoded_step 123 at 972 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (543)))))] using $hc)
  if row.getNat == 124 then
    return ← `(tactic| measure_decoded_step 124 at 1235 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%rax") using $hc)
  if row.getNat == 125 then
    return ← `(tactic| measure_decoded_step 125 at 1238 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rcx),%rsi") using $hc)
  if row.getNat == 126 then
    return ← `(tactic| measure_decoded_step 126 at 1242 encodedWidth 3 opcodeAST
      parse("movq %rsi,%rdi") using $hc)
  if row.getNat == 127 then
    return ← `(tactic| measure_decoded_step 127 at 1245 encodedWidth 3 opcodeAST
      parse("addq %rax,%rdi") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk2 " row:num " using " hc:term : tactic => do
  if row.getNat == 128 then
    return ← `(tactic| measure_decoded_step 128 at 1248 encodedWidth 6 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 129 then
    return ← `(tactic| measure_decoded_step 129 at 1254 encodedWidth 4 opcodeAST
      parse("cmpq $0xfffffffffffffff8,%rdi") using $hc)
  if row.getNat == 130 then
    return ← `(tactic| measure_decoded_step 130 at 1258 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 131 then
    return ← `(tactic| measure_decoded_step 131 at 1264 encodedWidth 4 opcodeAST
      parse("leaq 0x7(%rdi),%r8") using $hc)
  if row.getNat == 132 then
    return ← `(tactic| measure_decoded_step 132 at 1268 encodedWidth 4 opcodeAST
      parse("andq $0xfffffffffffffff8,%r8") using $hc)
  if row.getNat == 133 then
    return ← `(tactic| measure_decoded_step 133 at 1272 encodedWidth 3 opcodeAST
      parse("subq %rdi,%r8") using $hc)
  if row.getNat == 134 then
    return ← `(tactic| measure_decoded_step 134 at 1275 encodedWidth 3 opcodeAST
      parse("addq %rsi,%r8") using $hc)
  if row.getNat == 135 then
    return ← `(tactic| measure_decoded_step 135 at 1278 encodedWidth 6 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 136 then
    return ← `(tactic| measure_decoded_step 136 at 1284 encodedWidth 4 opcodeAST
      parse("cmpq $0xffffffffffffffef,%r8") using $hc)
  if row.getNat == 137 then
    return ← `(tactic| measure_decoded_step 137 at 1288 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 138 then
    return ← `(tactic| measure_decoded_step 138 at 1294 encodedWidth 4 opcodeAST
      parse("leaq 0x10(%r8),%rsi") using $hc)
  if row.getNat == 139 then
    return ← `(tactic| measure_decoded_step 139 at 1298 encodedWidth 4 opcodeAST
      parse("cmpq 0x8(%rcx),%rsi") using $hc)
  if row.getNat == 140 then
    return ← `(tactic| measure_decoded_step 140 at 1302 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 141 then
    return ← `(tactic| measure_decoded_step 141 at 1308 encodedWidth 5 opcodeAST
      parse("movq %rcx,0x8(%rsp)") using $hc)
  if row.getNat == 142 then
    return ← `(tactic| measure_decoded_step 142 at 1313 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x10(%rcx)") using $hc)
  if row.getNat == 143 then
    return ← `(tactic| measure_decoded_step 143 at 1317 encodedWidth 4 opcodeAST
      parse("leaq (%rax,%r8,1),%rbp") using $hc)
  if row.getNat == 144 then
    return ← `(tactic| measure_decoded_step 144 at 1321 encodedWidth 5 opcodeAST
      parse("movq %r15,0x10(%rsp)") using $hc)
  if row.getNat == 145 then
    return ← `(tactic| measure_decoded_step 145 at 1326 encodedWidth 4 opcodeAST
      parse("movq %r15,(%rax,%r8,1)") using $hc)
  if row.getNat == 146 then
    return ← `(tactic| measure_decoded_step 146 at 1330 encodedWidth 5 opcodeAST
      parse("movq %r14,0x8(%rax,%r8,1)") using $hc)
  if row.getNat == 147 then
    return ← `(tactic| measure_decoded_step 147 at 1335 encodedWidth 6 opcodeAST
      parse("movl $0x2,%r15d") using $hc)
  if row.getNat == 148 then
    return ← `(tactic| measure_decoded_step 148 at 1341 encodedWidth 3 opcodeAST
      parse("movq %rbp,%rdi") using $hc)
  if row.getNat == 149 then
    return ← `(tactic| measure_decoded_step 149 at 1344 encodedWidth 3 opcodeAST
      parse("movq %r15,%rsi") using $hc)
  if row.getNat == 150 then
    return ← `(tactic| measure_decoded_step 150 at 1347 encodedWidth 3 opcodeAST
      parse("movq %r13,%rdx") using $hc)
  if row.getNat == 151 then
    return ← `(tactic| measure_decoded_step 151 at 1350 encodedWidth 3 opcodeAST
      parse("movq %r12,%rcx") using $hc)
  if row.getNat == 152 then
    return ← `(tactic| measure_decoded_step 152 at 1353 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-34238)))))] using $hc)
  if row.getNat == 153 then
    return ← `(tactic| measure_decoded_step 153 at 1358 encodedWidth 2 opcodeAST
      parse("testb %al,%al") using $hc)
  if row.getNat == 154 then
    return ← `(tactic| measure_decoded_step 154 at 1360 encodedWidth 6 opcodeAST
      parse("jle measure_u2079") using $hc)
  if row.getNat == 155 then
    return ← `(tactic| measure_decoded_step 155 at 1366 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 156 then
    return ← `(tactic| measure_decoded_step 156 at 1374 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 157 then
    return ← `(tactic| measure_decoded_step 157 at 1382 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 158 then
    return ← `(tactic| measure_decoded_step 158 at 1389 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 159 then
    return ← `(tactic| measure_decoded_step 159 at 1397 encodedWidth 4 opcodeAST
      parse("movq %r13,0x10(%rbx)") using $hc)
  if row.getNat == 160 then
    return ← `(tactic| measure_decoded_step 160 at 1401 encodedWidth 4 opcodeAST
      parse("movq %r12,0x18(%rbx)") using $hc)
  if row.getNat == 161 then
    return ← `(tactic| measure_decoded_step 161 at 1405 encodedWidth 4 opcodeAST
      parse("movq %rbp,0x20(%rbx)") using $hc)
  if row.getNat == 162 then
    return ← `(tactic| measure_decoded_step 162 at 1409 encodedWidth 4 opcodeAST
      parse("movq %r15,0x28(%rbx)") using $hc)
  if row.getNat == 163 then
    return ← `(tactic| measure_decoded_step 163 at 1413 encodedWidth 7 opcodeAST
      parse("movl $0x2,0x40(%rbx)") using $hc)
  if row.getNat == 164 then
    return ← `(tactic| measure_decoded_step 164 at 1420 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1910)))))] using $hc)
  if row.getNat == 165 then
    return ← `(tactic| measure_decoded_step 165 at 1425 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%r9") using $hc)
  if row.getNat == 166 then
    return ← `(tactic| measure_decoded_step 166 at 1428 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rcx),%rdi") using $hc)
  if row.getNat == 167 then
    return ← `(tactic| measure_decoded_step 167 at 1432 encodedWidth 3 opcodeAST
      parse("movq %rdi,%r8") using $hc)
  if row.getNat == 168 then
    return ← `(tactic| measure_decoded_step 168 at 1435 encodedWidth 3 opcodeAST
      parse("addq %r9,%r8") using $hc)
  if row.getNat == 169 then
    return ← `(tactic| measure_decoded_step 169 at 1438 encodedWidth 6 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 170 then
    return ← `(tactic| measure_decoded_step 170 at 1444 encodedWidth 4 opcodeAST
      parse("cmpq $0xfffffffffffffff8,%r8") using $hc)
  if row.getNat == 171 then
    return ← `(tactic| measure_decoded_step 171 at 1448 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 172 then
    return ← `(tactic| measure_decoded_step 172 at 1454 encodedWidth 4 opcodeAST
      parse("leaq 0x7(%r8),%rsi") using $hc)
  if row.getNat == 173 then
    return ← `(tactic| measure_decoded_step 173 at 1458 encodedWidth 4 opcodeAST
      parse("andq $0xfffffffffffffff8,%rsi") using $hc)
  if row.getNat == 174 then
    return ← `(tactic| measure_decoded_step 174 at 1462 encodedWidth 3 opcodeAST
      parse("subq %r8,%rsi") using $hc)
  if row.getNat == 175 then
    return ← `(tactic| measure_decoded_step 175 at 1465 encodedWidth 3 opcodeAST
      parse("addq %rdi,%rsi") using $hc)
  if row.getNat == 176 then
    return ← `(tactic| measure_decoded_step 176 at 1468 encodedWidth 6 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 177 then
    return ← `(tactic| measure_decoded_step 177 at 1474 encodedWidth 4 opcodeAST
      parse("cmpq $0xffffffffffffffef,%rsi") using $hc)
  if row.getNat == 178 then
    return ← `(tactic| measure_decoded_step 178 at 1478 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 179 then
    return ← `(tactic| measure_decoded_step 179 at 1484 encodedWidth 4 opcodeAST
      parse("leaq 0x10(%rsi),%rdi") using $hc)
  if row.getNat == 180 then
    return ← `(tactic| measure_decoded_step 180 at 1488 encodedWidth 4 opcodeAST
      parse("cmpq 0x8(%rcx),%rdi") using $hc)
  if row.getNat == 181 then
    return ← `(tactic| measure_decoded_step 181 at 1492 encodedWidth 6 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 182 then
    return ← `(tactic| measure_decoded_step 182 at 1498 encodedWidth 4 opcodeAST
      parse("movq %rdi,0x10(%rcx)") using $hc)
  if row.getNat == 183 then
    return ← `(tactic| measure_decoded_step 183 at 1502 encodedWidth 4 opcodeAST
      parse("leaq (%r9,%rsi,1),%r13") using $hc)
  if row.getNat == 184 then
    return ← `(tactic| measure_decoded_step 184 at 1506 encodedWidth 4 opcodeAST
      parse("movq %r15,(%r9,%rsi,1)") using $hc)
  if row.getNat == 185 then
    return ← `(tactic| measure_decoded_step 185 at 1510 encodedWidth 5 opcodeAST
      parse("movq %r14,0x8(%r9,%rsi,1)") using $hc)
  if row.getNat == 186 then
    return ← `(tactic| measure_decoded_step 186 at 1515 encodedWidth 5 opcodeAST
      parse("movl $0x2,%esi") using $hc)
  if row.getNat == 187 then
    return ← `(tactic| measure_decoded_step 187 at 1520 encodedWidth 2 opcodeAST
      parse("testb $0x1,%al") using $hc)
  if row.getNat == 188 then
    return ← `(tactic| measure_decoded_step 188 at 1522 encodedWidth 2 opcodeAST
      parse("je measure_u1621") using $hc)
  if row.getNat == 189 then
    return ← `(tactic| measure_decoded_step 189 at 1524 encodedWidth 3 opcodeAST
      parse("movq %r13,%rdi") using $hc)
  if row.getNat == 190 then
    return ← `(tactic| measure_decoded_step 190 at 1527 encodedWidth 3 opcodeAST
      parse("movq %rbp,%rdx") using $hc)
  if row.getNat == 191 then
    return ← `(tactic| measure_decoded_step 191 at 1530 encodedWidth 5 opcodeAST
      parse("movq %rcx,0x8(%rsp)") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk3 " row:num " using " hc:term : tactic => do
  if row.getNat == 192 then
    return ← `(tactic| measure_decoded_step 192 at 1535 encodedWidth 3 opcodeAST
      parse("movq %r12,%rcx") using $hc)
  if row.getNat == 193 then
    return ← `(tactic| measure_decoded_step 193 at 1538 encodedWidth 5 opcodeAST
      parse("movq %rsi,0x10(%rsp)") using $hc)
  if row.getNat == 194 then
    return ← `(tactic| measure_decoded_step 194 at 1543 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-34428)))))] using $hc)
  if row.getNat == 195 then
    return ← `(tactic| measure_decoded_step 195 at 1548 encodedWidth 5 opcodeAST
      parse("movq 0x10(%rsp),%rdi") using $hc)
  if row.getNat == 196 then
    return ← `(tactic| measure_decoded_step 196 at 1553 encodedWidth 5 opcodeAST
      parse("movq 0x8(%rsp),%rcx") using $hc)
  if row.getNat == 197 then
    return ← `(tactic| measure_decoded_step 197 at 1558 encodedWidth 2 opcodeAST
      parse("testb %al,%al") using $hc)
  if row.getNat == 198 then
    return ← `(tactic| measure_decoded_step 198 at 1560 encodedWidth 2 opcodeAST
      parse("jle measure_u1621") using $hc)
  if row.getNat == 199 then
    return ← `(tactic| measure_decoded_step 199 at 1562 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 200 then
    return ← `(tactic| measure_decoded_step 200 at 1570 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 201 then
    return ← `(tactic| measure_decoded_step 201 at 1578 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 202 then
    return ← `(tactic| measure_decoded_step 202 at 1585 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 203 then
    return ← `(tactic| measure_decoded_step 203 at 1593 encodedWidth 4 opcodeAST
      parse("movq %rbp,0x10(%rbx)") using $hc)
  if row.getNat == 204 then
    return ← `(tactic| measure_decoded_step 204 at 1597 encodedWidth 4 opcodeAST
      parse("movq %r12,0x18(%rbx)") using $hc)
  if row.getNat == 205 then
    return ← `(tactic| measure_decoded_step 205 at 1601 encodedWidth 4 opcodeAST
      parse("movq %r13,0x20(%rbx)") using $hc)
  if row.getNat == 206 then
    return ← `(tactic| measure_decoded_step 206 at 1605 encodedWidth 4 opcodeAST
      parse("movq %rdi,0x28(%rbx)") using $hc)
  if row.getNat == 207 then
    return ← `(tactic| measure_decoded_step 207 at 1609 encodedWidth 7 opcodeAST
      parse("movl $0x2,0x40(%rbx)") using $hc)
  if row.getNat == 208 then
    return ← `(tactic| measure_decoded_step 208 at 1616 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1714)))))] using $hc)
  if row.getNat == 209 then
    return ← `(tactic| measure_decoded_step 209 at 1621 encodedWidth 5 opcodeAST
      parse("shrdq $0x3,%r14,%r15") using $hc)
  if row.getNat == 210 then
    return ← `(tactic| measure_decoded_step 210 at 1626 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%r14") using $hc)
  if row.getNat == 211 then
    return ← `(tactic| measure_decoded_step 211 at 1630 encodedWidth 4 opcodeAST
      parse("addq $0x1,%r15") using $hc)
  if row.getNat == 212 then
    return ← `(tactic| measure_decoded_step 212 at 1634 encodedWidth 4 opcodeAST
      parse("adcq $0x0,%r14") using $hc)
  if row.getNat == 213 then
    return ← `(tactic| measure_decoded_step 213 at 1638 encodedWidth 5 opcodeAST
      parse("leaq 0x18(%rsp),%rdi") using $hc)
  if row.getNat == 214 then
    return ← `(tactic| measure_decoded_step 214 at 1643 encodedWidth 3 opcodeAST
      parse("movq %r15,%rsi") using $hc)
  if row.getNat == 215 then
    return ← `(tactic| measure_decoded_step 215 at 1646 encodedWidth 3 opcodeAST
      parse("movq %r14,%rdx") using $hc)
  if row.getNat == 216 then
    return ← `(tactic| measure_decoded_step 216 at 1649 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (460)))))] using $hc)
  if row.getNat == 217 then
    return ← `(tactic| measure_decoded_step 217 at 1654 encodedWidth 3 opcodeAST
      parse("xorl %r8d,%r8d") using $hc)
  if row.getNat == 218 then
    return ← `(tactic| measure_decoded_step 218 at 1657 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1123)))))] using $hc)
  if row.getNat == 219 then
    return ← `(tactic| measure_decoded_step 219 at 1662 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 220 then
    return ← `(tactic| measure_decoded_step 220 at 1664 encodedWidth 3 opcodeAST
      parse("movq %rdx,%rdi") using $hc)
  if row.getNat == 221 then
    return ← `(tactic| measure_decoded_step 221 at 1667 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1370)))))] using $hc)
  if row.getNat == 222 then
    return ← `(tactic| measure_decoded_step 222 at 1672 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 223 then
    return ← `(tactic| measure_decoded_step 223 at 1675 encodedWidth 4 opcodeAST
      parse("setne %sil") using $hc)
  if row.getNat == 224 then
    return ← `(tactic| measure_decoded_step 224 at 1679 encodedWidth 3 opcodeAST
      parse("testq %rdx,%rdx") using $hc)
  if row.getNat == 225 then
    return ← `(tactic| measure_decoded_step 225 at 1682 encodedWidth 4 opcodeAST
      parse("sete %dil") using $hc)
  if row.getNat == 226 then
    return ← `(tactic| measure_decoded_step 226 at 1686 encodedWidth 4 opcodeAST
      parse("setne %r8b") using $hc)
  if row.getNat == 227 then
    return ← `(tactic| measure_decoded_step 227 at 1690 encodedWidth 3 opcodeAST
      parse("xorb %sil,%r8b") using $hc)
  if row.getNat == 228 then
    return ← `(tactic| measure_decoded_step 228 at 1693 encodedWidth 6 opcodeAST
      parse("je measure_u2217") using $hc)
  if row.getNat == 229 then
    return ← `(tactic| measure_decoded_step 229 at 1699 encodedWidth 3 opcodeAST
      parse("andb %dil,%sil") using $hc)
  if row.getNat == 230 then
    return ← `(tactic| measure_decoded_step 230 at 1702 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (256)))))] using $hc)
  if row.getNat == 231 then
    return ← `(tactic| measure_decoded_step 231 at 1720 encodedWidth 5 opcodeAST
      parse("movl $0x7,%eax") using $hc)
  if row.getNat == 232 then
    return ← `(tactic| measure_decoded_step 232 at 1725 encodedWidth 2 opcodeAST
      parse("xorl %edx,%edx") using $hc)
  if row.getNat == 233 then
    return ← `(tactic| measure_decoded_step 233 at 1727 encodedWidth 3 opcodeAST
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 234 then
    return ← `(tactic| measure_decoded_step 234 at 1730 encodedWidth 6 opcodeAST
      parse("je measure_u2684") using $hc)
  if row.getNat == 235 then
    return ← `(tactic| measure_decoded_step 235 at 1736 encodedWidth 5 opcodeAST
      parse("leaq -0x10(%rsp),%rsp") using $hc)
  if row.getNat == 236 then
    return ← `(tactic| measure_decoded_step 236 at 1741 encodedWidth 4 opcodeAST
      parse("movq %r11,(%rsp)") using $hc)
  if row.getNat == 237 then
    return ← `(tactic| measure_decoded_step 237 at 1745 encodedWidth 5 opcodeAST
      parse("movq %r10,0x8(%rsp)") using $hc)
  if row.getNat == 238 then
    return ← `(tactic| measure_decoded_step 238 at 1750 encodedWidth 3 opcodeAST
      parse("movq %rcx,%r11") using $hc)
  if row.getNat == 239 then
    return ← `(tactic| measure_decoded_step 239 at 1753 encodedWidth 3 opcodeAST
      parse("testq %r11,%r11") using $hc)
  if row.getNat == 240 then
    return ← `(tactic| measure_decoded_step 240 at 1756 encodedWidth 2 opcodeAST
      parse("je measure_u1782") using $hc)
  if row.getNat == 241 then
    return ← `(tactic| measure_decoded_step 241 at 1758 encodedWidth 7 opcodeAST
      parse("movq $0xffffffffffffffff,%r10") using $hc)
  if row.getNat == 242 then
    return ← `(tactic| measure_decoded_step 242 at 1765 encodedWidth 3 opcodeAST
      [.instr (.regular .W64 .W64 (.inc (.reg (.low .r10 .W64))))] using $hc)
  if row.getNat == 243 then
    return ← `(tactic| measure_decoded_step 243 at 1768 encodedWidth 3 opcodeAST
      parse("shrq $1,%r11") using $hc)
  if row.getNat == 244 then
    return ← `(tactic| measure_decoded_step 244 at 1771 encodedWidth 2 opcodeAST
      parse("jne measure_u1765") using $hc)
  if row.getNat == 245 then
    return ← `(tactic| measure_decoded_step 245 at 1773 encodedWidth 3 opcodeAST
      parse("movq %r10,%rdi") using $hc)
  if row.getNat == 246 then
    return ← `(tactic| measure_decoded_step 246 at 1776 encodedWidth 4 opcodeAST
      parse("cmpq $0xffffffffffffffff,%r10") using $hc)
  if row.getNat == 247 then
    return ← `(tactic| measure_decoded_step 247 at 1780 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (0)))))] using $hc)
  if row.getNat == 248 then
    return ← `(tactic| measure_decoded_step 248 at 1782 encodedWidth 4 opcodeAST
      parse("movq (%rsp),%r11") using $hc)
  if row.getNat == 249 then
    return ← `(tactic| measure_decoded_step 249 at 1786 encodedWidth 5 opcodeAST
      parse("movq 0x8(%rsp),%r10") using $hc)
  if row.getNat == 250 then
    return ← `(tactic| measure_decoded_step 250 at 1791 encodedWidth 5 opcodeAST
      parse("leaq 0x10(%rsp),%rsp") using $hc)
  if row.getNat == 251 then
    return ← `(tactic| measure_decoded_step 251 at 1796 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W32 (.inc (.reg (.low .rdi .W32))))] using $hc)
  if row.getNat == 252 then
    return ← `(tactic| measure_decoded_step 252 at 1798 encodedWidth 3 opcodeAST
      parse("addq %rax,%rdi") using $hc)
  if row.getNat == 253 then
    return ← `(tactic| measure_decoded_step 253 at 1801 encodedWidth 4 opcodeAST
      parse("adcq $0x0,%rdx") using $hc)
  if row.getNat == 254 then
    return ← `(tactic| measure_decoded_step 254 at 1805 encodedWidth 5 opcodeAST
      parse("shrdq $0x3,%rdx,%rdi") using $hc)
  if row.getNat == 255 then
    return ← `(tactic| measure_decoded_step 255 at 1810 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%rdx") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk4 " row:num " using " hc:term : tactic => do
  if row.getNat == 256 then
    return ← `(tactic| measure_decoded_step 256 at 1814 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (867)))))] using $hc)
  if row.getNat == 257 then
    return ← `(tactic| measure_decoded_step 257 at 1854 encodedWidth 3 opcodeAST
      parse("testq %rdi,%rdi") using $hc)
  if row.getNat == 258 then
    return ← `(tactic| measure_decoded_step 258 at 1857 encodedWidth 6 opcodeAST
      parse("je measure_u2780") using $hc)
  if row.getNat == 259 then
    return ← `(tactic| measure_decoded_step 259 at 1863 encodedWidth 3 opcodeAST
      parse("movq (%r8),%r9") using $hc)
  if row.getNat == 260 then
    return ← `(tactic| measure_decoded_step 260 at 1866 encodedWidth 4 opcodeAST
      parse("cmpq $0x2,%rdi") using $hc)
  if row.getNat == 261 then
    return ← `(tactic| measure_decoded_step 261 at 1870 encodedWidth 6 opcodeAST
      parse("jb measure_u2662") using $hc)
  if row.getNat == 262 then
    return ← `(tactic| measure_decoded_step 262 at 1876 encodedWidth 4 opcodeAST
      parse("movq 0x8(%r8),%r8") using $hc)
  if row.getNat == 263 then
    return ← `(tactic| measure_decoded_step 263 at 1880 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (780)))))] using $hc)
  if row.getNat == 264 then
    return ← `(tactic| measure_decoded_step 264 at 1885 encodedWidth 3 opcodeAST
      parse("testq %rdx,%rdx") using $hc)
  if row.getNat == 265 then
    return ← `(tactic| measure_decoded_step 265 at 1888 encodedWidth 6 opcodeAST
      parse("je measure_u3038") using $hc)
  if row.getNat == 266 then
    return ← `(tactic| measure_decoded_step 266 at 1894 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%rdi") using $hc)
  if row.getNat == 267 then
    return ← `(tactic| measure_decoded_step 267 at 1897 encodedWidth 4 opcodeAST
      parse("cmpq $0x2,%rdx") using $hc)
  if row.getNat == 268 then
    return ← `(tactic| measure_decoded_step 268 at 1901 encodedWidth 6 opcodeAST
      parse("jb measure_u2670") using $hc)
  if row.getNat == 269 then
    return ← `(tactic| measure_decoded_step 269 at 1907 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rcx),%rsi") using $hc)
  if row.getNat == 270 then
    return ← `(tactic| measure_decoded_step 270 at 1911 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1126)))))] using $hc)
  if row.getNat == 271 then
    return ← `(tactic| measure_decoded_step 271 at 1916 encodedWidth 3 opcodeAST
      parse("xorl %r8d,%r8d") using $hc)
  if row.getNat == 272 then
    return ← `(tactic| measure_decoded_step 272 at 1919 encodedWidth 3 opcodeAST
      parse("cmpq %rsi,%r8") using $hc)
  if row.getNat == 273 then
    return ← `(tactic| measure_decoded_step 273 at 1922 encodedWidth 4 opcodeAST
      parse("setb %sil") using $hc)
  if row.getNat == 274 then
    return ← `(tactic| measure_decoded_step 274 at 1926 encodedWidth 2 opcodeAST
      parse("jne measure_u1963") using $hc)
  if row.getNat == 275 then
    return ← `(tactic| measure_decoded_step 275 at 1928 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 276 then
    return ← `(tactic| measure_decoded_step 276 at 1931 encodedWidth 6 opcodeAST
      parse("je measure_u3050") using $hc)
  if row.getNat == 277 then
    return ← `(tactic| measure_decoded_step 277 at 1937 encodedWidth 3 opcodeAST
      parse("testq %rdx,%rdx") using $hc)
  if row.getNat == 278 then
    return ← `(tactic| measure_decoded_step 278 at 1940 encodedWidth 6 opcodeAST
      parse("je measure_u2252") using $hc)
  if row.getNat == 279 then
    return ← `(tactic| measure_decoded_step 279 at 1946 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%rsi") using $hc)
  if row.getNat == 280 then
    return ← `(tactic| measure_decoded_step 280 at 1949 encodedWidth 3 opcodeAST
      parse("cmpq %rsi,%rax") using $hc)
  if row.getNat == 281 then
    return ← `(tactic| measure_decoded_step 281 at 1952 encodedWidth 6 opcodeAST
      parse("jne measure_u2243") using $hc)
  if row.getNat == 282 then
    return ← `(tactic| measure_decoded_step 282 at 1958 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1087)))))] using $hc)
  if row.getNat == 283 then
    return ← `(tactic| measure_decoded_step 283 at 1963 encodedWidth 3 opcodeAST
      parse("testb %sil,%sil") using $hc)
  if row.getNat == 284 then
    return ← `(tactic| measure_decoded_step 284 at 1966 encodedWidth 6 opcodeAST
      parse("jne measure_u2252") using $hc)
  if row.getNat == 285 then
    return ← `(tactic| measure_decoded_step 285 at 1972 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1073)))))] using $hc)
  if row.getNat == 286 then
    return ← `(tactic| measure_decoded_step 286 at 2011 encodedWidth 2 opcodeAST
      parse("xorl %edx,%edx") using $hc)
  if row.getNat == 287 then
    return ← `(tactic| measure_decoded_step 287 at 2013 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (668)))))] using $hc)
  if row.getNat == 288 then
    return ← `(tactic| measure_decoded_step 288 at 2079 encodedWidth 5 opcodeAST
      parse("movq 0x10(%rsp),%rsi") using $hc)
  if row.getNat == 289 then
    return ← `(tactic| measure_decoded_step 289 at 2084 encodedWidth 5 opcodeAST
      parse("shrdq $0x3,%r14,%rsi") using $hc)
  if row.getNat == 290 then
    return ← `(tactic| measure_decoded_step 290 at 2089 encodedWidth 4 opcodeAST
      parse("shrq $0x3,%r14") using $hc)
  if row.getNat == 291 then
    return ← `(tactic| measure_decoded_step 291 at 2093 encodedWidth 4 opcodeAST
      parse("addq $0x1,%rsi") using $hc)
  if row.getNat == 292 then
    return ← `(tactic| measure_decoded_step 292 at 2097 encodedWidth 4 opcodeAST
      parse("adcq $0x0,%r14") using $hc)
  if row.getNat == 293 then
    return ← `(tactic| measure_decoded_step 293 at 2101 encodedWidth 5 opcodeAST
      parse("leaq 0x18(%rsp),%rdi") using $hc)
  if row.getNat == 294 then
    return ← `(tactic| measure_decoded_step 294 at 2106 encodedWidth 3 opcodeAST
      parse("movq %r14,%rdx") using $hc)
  if row.getNat == 295 then
    return ← `(tactic| measure_decoded_step 295 at 2109 encodedWidth 5 opcodeAST
      parse("movq 0x8(%rsp),%rcx") using $hc)
  if row.getNat == 296 then
    return ← `(tactic| measure_decoded_step 296 at 2114 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-16823)))))] using $hc)
  if row.getNat == 297 then
    return ← `(tactic| measure_decoded_step 297 at 2119 encodedWidth 4 opcodeAST
      parse("movl 0x58(%rsp),%edx") using $hc)
  if row.getNat == 298 then
    return ← `(tactic| measure_decoded_step 298 at 2123 encodedWidth 5 opcodeAST
      parse("movq 0x18(%rsp),%rcx") using $hc)
  if row.getNat == 299 then
    return ← `(tactic| measure_decoded_step 299 at 2128 encodedWidth 5 opcodeAST
      parse("movq 0x20(%rsp),%rax") using $hc)
  if row.getNat == 300 then
    return ← `(tactic| measure_decoded_step 300 at 2133 encodedWidth 2 opcodeAST
      parse("testl %edx,%edx") using $hc)
  if row.getNat == 301 then
    return ← `(tactic| measure_decoded_step 301 at 2135 encodedWidth 6 opcodeAST
      parse("je measure_u3052") using $hc)
  if row.getNat == 302 then
    return ← `(tactic| measure_decoded_step 302 at 2141 encodedWidth 5 opcodeAST
      parse("movq 0x50(%rsp),%rsi") using $hc)
  if row.getNat == 303 then
    return ← `(tactic| measure_decoded_step 303 at 2146 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x38(%rbx)") using $hc)
  if row.getNat == 304 then
    return ← `(tactic| measure_decoded_step 304 at 2150 encodedWidth 5 opcodeAST
      parse("movq 0x48(%rsp),%rsi") using $hc)
  if row.getNat == 305 then
    return ← `(tactic| measure_decoded_step 305 at 2155 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x30(%rbx)") using $hc)
  if row.getNat == 306 then
    return ← `(tactic| measure_decoded_step 306 at 2159 encodedWidth 5 opcodeAST
      parse("movq 0x40(%rsp),%rsi") using $hc)
  if row.getNat == 307 then
    return ← `(tactic| measure_decoded_step 307 at 2164 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x28(%rbx)") using $hc)
  if row.getNat == 308 then
    return ← `(tactic| measure_decoded_step 308 at 2168 encodedWidth 5 opcodeAST
      parse("movq 0x38(%rsp),%rsi") using $hc)
  if row.getNat == 309 then
    return ← `(tactic| measure_decoded_step 309 at 2173 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x20(%rbx)") using $hc)
  if row.getNat == 310 then
    return ← `(tactic| measure_decoded_step 310 at 2177 encodedWidth 5 opcodeAST
      parse("movq 0x28(%rsp),%rsi") using $hc)
  if row.getNat == 311 then
    return ← `(tactic| measure_decoded_step 311 at 2182 encodedWidth 5 opcodeAST
      parse("movq 0x30(%rsp),%rdi") using $hc)
  if row.getNat == 312 then
    return ← `(tactic| measure_decoded_step 312 at 2187 encodedWidth 4 opcodeAST
      parse("movq %rdi,0x18(%rbx)") using $hc)
  if row.getNat == 313 then
    return ← `(tactic| measure_decoded_step 313 at 2191 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x10(%rbx)") using $hc)
  if row.getNat == 314 then
    return ← `(tactic| measure_decoded_step 314 at 2195 encodedWidth 4 opcodeAST
      parse("movl 0x5c(%rsp),%esi") using $hc)
  if row.getNat == 315 then
    return ← `(tactic| measure_decoded_step 315 at 2199 encodedWidth 3 opcodeAST
      parse("movq %rcx,(%rbx)") using $hc)
  if row.getNat == 316 then
    return ← `(tactic| measure_decoded_step 316 at 2202 encodedWidth 4 opcodeAST
      parse("movq %rax,0x8(%rbx)") using $hc)
  if row.getNat == 317 then
    return ← `(tactic| measure_decoded_step 317 at 2206 encodedWidth 3 opcodeAST
      parse("movl %edx,0x40(%rbx)") using $hc)
  if row.getNat == 318 then
    return ← `(tactic| measure_decoded_step 318 at 2209 encodedWidth 3 opcodeAST
      parse("movl %esi,0x44(%rbx)") using $hc)
  if row.getNat == 319 then
    return ← `(tactic| measure_decoded_step 319 at 2212 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (1118)))))] using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk5 " row:num " using " hc:term : tactic => do
  if row.getNat == 320 then
    return ← `(tactic| measure_decoded_step 320 at 2217 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 321 then
    return ← `(tactic| measure_decoded_step 321 at 2220 encodedWidth 4 opcodeAST
      parse("setne %dil") using $hc)
  if row.getNat == 322 then
    return ← `(tactic| measure_decoded_step 322 at 2224 encodedWidth 3 opcodeAST
      parse("cmpq %rdx,%rax") using $hc)
  if row.getNat == 323 then
    return ← `(tactic| measure_decoded_step 323 at 2227 encodedWidth 4 opcodeAST
      parse("setne %r8b") using $hc)
  if row.getNat == 324 then
    return ← `(tactic| measure_decoded_step 324 at 2231 encodedWidth 3 opcodeAST
      parse("movq %rdx,%rsi") using $hc)
  if row.getNat == 325 then
    return ← `(tactic| measure_decoded_step 325 at 2234 encodedWidth 3 opcodeAST
      parse("testb %r8b,%dil") using $hc)
  if row.getNat == 326 then
    return ← `(tactic| measure_decoded_step 326 at 2237 encodedWidth 6 opcodeAST
      parse("je measure_u3050") using $hc)
  if row.getNat == 327 then
    return ← `(tactic| measure_decoded_step 327 at 2243 encodedWidth 3 opcodeAST
      parse("cmpq %rsi,%rax") using $hc)
  if row.getNat == 328 then
    return ← `(tactic| measure_decoded_step 328 at 2246 encodedWidth 6 opcodeAST
      parse("jbe measure_u3050") using $hc)
  if row.getNat == 329 then
    return ← `(tactic| measure_decoded_step 329 at 2252 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 330 then
    return ← `(tactic| measure_decoded_step 330 at 2260 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 331 then
    return ← `(tactic| measure_decoded_step 331 at 2268 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 332 then
    return ← `(tactic| measure_decoded_step 332 at 2275 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 333 then
    return ← `(tactic| measure_decoded_step 333 at 2283 encodedWidth 4 opcodeAST
      parse("movq %rcx,0x10(%rbx)") using $hc)
  if row.getNat == 334 then
    return ← `(tactic| measure_decoded_step 334 at 2287 encodedWidth 4 opcodeAST
      parse("movq %rdx,0x18(%rbx)") using $hc)
  if row.getNat == 335 then
    return ← `(tactic| measure_decoded_step 335 at 2291 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (66)))))] using $hc)
  if row.getNat == 336 then
    return ← `(tactic| measure_decoded_step 336 at 2359 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 337 then
    return ← `(tactic| measure_decoded_step 337 at 2367 encodedWidth 4 opcodeAST
      parse("movq %rax,0x28(%rbx)") using $hc)
  if row.getNat == 338 then
    return ← `(tactic| measure_decoded_step 338 at 2371 encodedWidth 7 opcodeAST
      parse("movl $0x2,0x40(%rbx)") using $hc)
  if row.getNat == 339 then
    return ← `(tactic| measure_decoded_step 339 at 2378 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (952)))))] using $hc)
  if row.getNat == 340 then
    return ← `(tactic| measure_decoded_step 340 at 2662 encodedWidth 3 opcodeAST
      parse("xorl %r8d,%r8d") using $hc)
  if row.getNat == 341 then
    return ← `(tactic| measure_decoded_step 341 at 2665 encodedWidth 3 opcodeAST
      parse("movq %r9,%rdi") using $hc)
  if row.getNat == 342 then
    return ← `(tactic| measure_decoded_step 342 at 2668 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (115)))))] using $hc)
  if row.getNat == 343 then
    return ← `(tactic| measure_decoded_step 343 at 2670 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 344 then
    return ← `(tactic| measure_decoded_step 344 at 2672 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (365)))))] using $hc)
  if row.getNat == 345 then
    return ← `(tactic| measure_decoded_step 345 at 2684 encodedWidth 2 opcodeAST
      parse("xorl %edi,%edi") using $hc)
  if row.getNat == 346 then
    return ← `(tactic| measure_decoded_step 346 at 2686 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rcx") using $hc)
  if row.getNat == 347 then
    return ← `(tactic| measure_decoded_step 347 at 2690 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rsi),%rax") using $hc)
  if row.getNat == 348 then
    return ← `(tactic| measure_decoded_step 348 at 2694 encodedWidth 3 opcodeAST
      parse("testq %rcx,%rcx") using $hc)
  if row.getNat == 349 then
    return ← `(tactic| measure_decoded_step 349 at 2697 encodedWidth 2 opcodeAST
      parse("je measure_u2736") using $hc)
  if row.getNat == 350 then
    return ← `(tactic| measure_decoded_step 350 at 2699 encodedWidth 4 opcodeAST
      parse("leaq 0x1(%rax),%rsi") using $hc)
  if row.getNat == 351 then
    return ← `(tactic| measure_decoded_step 351 at 2703 encodedWidth 1 opcodeAST
      [.instr (.regular .W64 .W64 (.nop 1))] using $hc)
  if row.getNat == 352 then
    return ← `(tactic| measure_decoded_step 352 at 2704 encodedWidth 4 opcodeAST
      parse("cmpq $0x1,%rsi") using $hc)
  if row.getNat == 353 then
    return ← `(tactic| measure_decoded_step 353 at 2708 encodedWidth 2 opcodeAST
      parse("je measure_u2746") using $hc)
  if row.getNat == 354 then
    return ← `(tactic| measure_decoded_step 354 at 2710 encodedWidth 4 opcodeAST
      parse("leaq -0x1(%rsi),%r8") using $hc)
  if row.getNat == 355 then
    return ← `(tactic| measure_decoded_step 355 at 2714 encodedWidth 6 opcodeAST
      parse("cmpq $0x0,-0x10(%rcx,%rsi,8)") using $hc)
  if row.getNat == 356 then
    return ← `(tactic| measure_decoded_step 356 at 2720 encodedWidth 3 opcodeAST
      parse("movq %r8,%rsi") using $hc)
  if row.getNat == 357 then
    return ← `(tactic| measure_decoded_step 357 at 2723 encodedWidth 2 opcodeAST
      parse("je measure_u2704") using $hc)
  if row.getNat == 358 then
    return ← `(tactic| measure_decoded_step 358 at 2725 encodedWidth 4 opcodeAST
      parse("cmpq $0x3,%r8") using $hc)
  if row.getNat == 359 then
    return ← `(tactic| measure_decoded_step 359 at 2729 encodedWidth 2 opcodeAST
      parse("jb measure_u2755") using $hc)
  if row.getNat == 360 then
    return ← `(tactic| measure_decoded_step 360 at 2731 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (316)))))] using $hc)
  if row.getNat == 361 then
    return ← `(tactic| measure_decoded_step 361 at 2736 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 362 then
    return ← `(tactic| measure_decoded_step 362 at 2738 encodedWidth 3 opcodeAST
      parse("movq %rax,%r8") using $hc)
  if row.getNat == 363 then
    return ← `(tactic| measure_decoded_step 363 at 2741 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (507)))))] using $hc)
  if row.getNat == 364 then
    return ← `(tactic| measure_decoded_step 364 at 2746 encodedWidth 3 opcodeAST
      parse("testq %rax,%rax") using $hc)
  if row.getNat == 365 then
    return ← `(tactic| measure_decoded_step 365 at 2749 encodedWidth 6 opcodeAST
      parse("je measure_u3248") using $hc)
  if row.getNat == 366 then
    return ← `(tactic| measure_decoded_step 366 at 2755 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%r8") using $hc)
  if row.getNat == 367 then
    return ← `(tactic| measure_decoded_step 367 at 2758 encodedWidth 4 opcodeAST
      parse("cmpq $0x2,%rax") using $hc)
  if row.getNat == 368 then
    return ← `(tactic| measure_decoded_step 368 at 2762 encodedWidth 2 opcodeAST
      parse("jb measure_u2773") using $hc)
  if row.getNat == 369 then
    return ← `(tactic| measure_decoded_step 369 at 2764 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rcx),%rsi") using $hc)
  if row.getNat == 370 then
    return ← `(tactic| measure_decoded_step 370 at 2768 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (480)))))] using $hc)
  if row.getNat == 371 then
    return ← `(tactic| measure_decoded_step 371 at 2773 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 372 then
    return ← `(tactic| measure_decoded_step 372 at 2775 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (473)))))] using $hc)
  if row.getNat == 373 then
    return ← `(tactic| measure_decoded_step 373 at 2780 encodedWidth 3 opcodeAST
      parse("xorl %r8d,%r8d") using $hc)
  if row.getNat == 374 then
    return ← `(tactic| measure_decoded_step 374 at 2783 encodedWidth 2 opcodeAST
      parse("xorl %edi,%edi") using $hc)
  if row.getNat == 375 then
    return ← `(tactic| measure_decoded_step 375 at 2785 encodedWidth 3 opcodeAST
      parse("xorq %rax,%rdi") using $hc)
  if row.getNat == 376 then
    return ← `(tactic| measure_decoded_step 376 at 2788 encodedWidth 3 opcodeAST
      parse("xorq %rdx,%r8") using $hc)
  if row.getNat == 377 then
    return ← `(tactic| measure_decoded_step 377 at 2791 encodedWidth 3 opcodeAST
      parse("orq %rdi,%r8") using $hc)
  if row.getNat == 378 then
    return ← `(tactic| measure_decoded_step 378 at 2794 encodedWidth 2 opcodeAST
      parse("jne measure_u2805") using $hc)
  if row.getNat == 379 then
    return ← `(tactic| measure_decoded_step 379 at 2796 encodedWidth 4 opcodeAST
      parse("movq 0x18(%r14),%rax") using $hc)
  if row.getNat == 380 then
    return ← `(tactic| measure_decoded_step 380 at 2800 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (245)))))] using $hc)
  if row.getNat == 381 then
    return ← `(tactic| measure_decoded_step 381 at 2805 encodedWidth 3 opcodeAST
      parse("testq %rdx,%rdx") using $hc)
  if row.getNat == 382 then
    return ← `(tactic| measure_decoded_step 382 at 2808 encodedWidth 2 opcodeAST
      parse("jne measure_u2814") using $hc)
  if row.getNat == 383 then
    return ← `(tactic| measure_decoded_step 383 at 2810 encodedWidth 2 opcodeAST
      parse("xorl %ecx,%ecx") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk6 " row:num " using " hc:term : tactic => do
  if row.getNat == 384 then
    return ← `(tactic| measure_decoded_step 384 at 2812 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (79)))))] using $hc)
  if row.getNat == 385 then
    return ← `(tactic| measure_decoded_step 385 at 2814 encodedWidth 3 opcodeAST
      parse("movq (%rcx),%rdi") using $hc)
  if row.getNat == 386 then
    return ← `(tactic| measure_decoded_step 386 at 2817 encodedWidth 4 opcodeAST
      parse("movq 0x10(%rcx),%r9") using $hc)
  if row.getNat == 387 then
    return ← `(tactic| measure_decoded_step 387 at 2821 encodedWidth 3 opcodeAST
      parse("movq %r9,%r10") using $hc)
  if row.getNat == 388 then
    return ← `(tactic| measure_decoded_step 388 at 2824 encodedWidth 3 opcodeAST
      parse("addq %rdi,%r10") using $hc)
  if row.getNat == 389 then
    return ← `(tactic| measure_decoded_step 389 at 2827 encodedWidth 6 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 390 then
    return ← `(tactic| measure_decoded_step 390 at 2833 encodedWidth 4 opcodeAST
      parse("cmpq $0xfffffffffffffff8,%r10") using $hc)
  if row.getNat == 391 then
    return ← `(tactic| measure_decoded_step 391 at 2837 encodedWidth 2 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 392 then
    return ← `(tactic| measure_decoded_step 392 at 2839 encodedWidth 4 opcodeAST
      parse("leaq 0x7(%r10),%r8") using $hc)
  if row.getNat == 393 then
    return ← `(tactic| measure_decoded_step 393 at 2843 encodedWidth 4 opcodeAST
      parse("andq $0xfffffffffffffff8,%r8") using $hc)
  if row.getNat == 394 then
    return ← `(tactic| measure_decoded_step 394 at 2847 encodedWidth 3 opcodeAST
      parse("subq %r10,%r8") using $hc)
  if row.getNat == 395 then
    return ← `(tactic| measure_decoded_step 395 at 2850 encodedWidth 3 opcodeAST
      parse("addq %r9,%r8") using $hc)
  if row.getNat == 396 then
    return ← `(tactic| measure_decoded_step 396 at 2853 encodedWidth 2 opcodeAST
      parse("jb measure_u2963") using $hc)
  if row.getNat == 397 then
    return ← `(tactic| measure_decoded_step 397 at 2855 encodedWidth 4 opcodeAST
      parse("cmpq $0xffffffffffffffef,%r8") using $hc)
  if row.getNat == 398 then
    return ← `(tactic| measure_decoded_step 398 at 2859 encodedWidth 2 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 399 then
    return ← `(tactic| measure_decoded_step 399 at 2861 encodedWidth 4 opcodeAST
      parse("leaq 0x10(%r8),%r9") using $hc)
  if row.getNat == 400 then
    return ← `(tactic| measure_decoded_step 400 at 2865 encodedWidth 4 opcodeAST
      parse("cmpq 0x8(%rcx),%r9") using $hc)
  if row.getNat == 401 then
    return ← `(tactic| measure_decoded_step 401 at 2869 encodedWidth 2 opcodeAST
      parse("ja measure_u2963") using $hc)
  if row.getNat == 402 then
    return ← `(tactic| measure_decoded_step 402 at 2871 encodedWidth 4 opcodeAST
      parse("movq %r9,0x10(%rcx)") using $hc)
  if row.getNat == 403 then
    return ← `(tactic| measure_decoded_step 403 at 2875 encodedWidth 4 opcodeAST
      parse("leaq (%rdi,%r8,1),%rcx") using $hc)
  if row.getNat == 404 then
    return ← `(tactic| measure_decoded_step 404 at 2879 encodedWidth 4 opcodeAST
      parse("movq %rax,(%rdi,%r8,1)") using $hc)
  if row.getNat == 405 then
    return ← `(tactic| measure_decoded_step 405 at 2883 encodedWidth 5 opcodeAST
      parse("movq %rdx,0x8(%rdi,%r8,1)") using $hc)
  if row.getNat == 406 then
    return ← `(tactic| measure_decoded_step 406 at 2888 encodedWidth 5 opcodeAST
      parse("movl $0x2,%eax") using $hc)
  if row.getNat == 407 then
    return ← `(tactic| measure_decoded_step 407 at 2893 encodedWidth 4 opcodeAST
      parse("addq $0x8,%rsi") using $hc)
  if row.getNat == 408 then
    return ← `(tactic| measure_decoded_step 408 at 2897 encodedWidth 3 opcodeAST
      parse("movq (%rsi),%rdx") using $hc)
  if row.getNat == 409 then
    return ← `(tactic| measure_decoded_step 409 at 2900 encodedWidth 4 opcodeAST
      parse("movq 0x8(%rsi),%rsi") using $hc)
  if row.getNat == 410 then
    return ← `(tactic| measure_decoded_step 410 at 2904 encodedWidth 4 opcodeAST
      parse("movq %rsi,0x18(%rbx)") using $hc)
  if row.getNat == 411 then
    return ← `(tactic| measure_decoded_step 411 at 2908 encodedWidth 4 opcodeAST
      parse("movq %rdx,0x10(%rbx)") using $hc)
  if row.getNat == 412 then
    return ← `(tactic| measure_decoded_step 412 at 2912 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 413 then
    return ← `(tactic| measure_decoded_step 413 at 2919 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 414 then
    return ← `(tactic| measure_decoded_step 414 at 2927 encodedWidth 4 opcodeAST
      parse("movq %rcx,0x20(%rbx)") using $hc)
  if row.getNat == 415 then
    return ← `(tactic| measure_decoded_step 415 at 2931 encodedWidth 4 opcodeAST
      parse("movq %rax,0x28(%rbx)") using $hc)
  if row.getNat == 416 then
    return ← `(tactic| measure_decoded_step 416 at 2935 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 417 then
    return ← `(tactic| measure_decoded_step 417 at 2943 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 418 then
    return ← `(tactic| measure_decoded_step 418 at 2951 encodedWidth 7 opcodeAST
      parse("movl $0x3,0x40(%rbx)") using $hc)
  if row.getNat == 419 then
    return ← `(tactic| measure_decoded_step 419 at 2958 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (372)))))] using $hc)
  if row.getNat == 420 then
    return ← `(tactic| measure_decoded_step 420 at 2963 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 421 then
    return ← `(tactic| measure_decoded_step 421 at 2971 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 422 then
    return ← `(tactic| measure_decoded_step 422 at 2979 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x28(%rbx)") using $hc)
  if row.getNat == 423 then
    return ← `(tactic| measure_decoded_step 423 at 2987 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 424 then
    return ← `(tactic| measure_decoded_step 424 at 2995 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x18(%rbx)") using $hc)
  if row.getNat == 425 then
    return ← `(tactic| measure_decoded_step 425 at 3003 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x10(%rbx)") using $hc)
  if row.getNat == 426 then
    return ← `(tactic| measure_decoded_step 426 at 3011 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 427 then
    return ← `(tactic| measure_decoded_step 427 at 3018 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 428 then
    return ← `(tactic| measure_decoded_step 428 at 3026 encodedWidth 7 opcodeAST
      parse("movl $0x8000,0x40(%rbx)") using $hc)
  if row.getNat == 429 then
    return ← `(tactic| measure_decoded_step 429 at 3033 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (297)))))] using $hc)
  if row.getNat == 430 then
    return ← `(tactic| measure_decoded_step 430 at 3038 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 431 then
    return ← `(tactic| measure_decoded_step 431 at 3040 encodedWidth 2 opcodeAST
      parse("xorl %edi,%edi") using $hc)
  if row.getNat == 432 then
    return ← `(tactic| measure_decoded_step 432 at 3042 encodedWidth 3 opcodeAST
      parse("xorq %rax,%rdi") using $hc)
  if row.getNat == 433 then
    return ← `(tactic| measure_decoded_step 433 at 3045 encodedWidth 3 opcodeAST
      parse("orq %rsi,%rdi") using $hc)
  if row.getNat == 434 then
    return ← `(tactic| measure_decoded_step 434 at 3048 encodedWidth 2 opcodeAST
      parse("jne measure_u3095") using $hc)
  if row.getNat == 435 then
    return ← `(tactic| measure_decoded_step 435 at 3050 encodedWidth 2 opcodeAST
      parse("xorl %ecx,%ecx") using $hc)
  if row.getNat == 436 then
    return ← `(tactic| measure_decoded_step 436 at 3052 encodedWidth 7 opcodeAST
      parse("movq $0x8,(%rbx)") using $hc)
  if row.getNat == 437 then
    return ← `(tactic| measure_decoded_step 437 at 3059 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 438 then
    return ← `(tactic| measure_decoded_step 438 at 3067 encodedWidth 4 opcodeAST
      parse("movq %rcx,0x10(%rbx)") using $hc)
  if row.getNat == 439 then
    return ← `(tactic| measure_decoded_step 439 at 3071 encodedWidth 4 opcodeAST
      parse("movq %rax,0x18(%rbx)") using $hc)
  if row.getNat == 440 then
    return ← `(tactic| measure_decoded_step 440 at 3075 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 441 then
    return ← `(tactic| measure_decoded_step 441 at 3083 encodedWidth 7 opcodeAST
      parse("movl $0x0,0x40(%rbx)") using $hc)
  if row.getNat == 442 then
    return ← `(tactic| measure_decoded_step 442 at 3090 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (240)))))] using $hc)
  if row.getNat == 443 then
    return ← `(tactic| measure_decoded_step 443 at 3095 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 444 then
    return ← `(tactic| measure_decoded_step 444 at 3103 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 445 then
    return ← `(tactic| measure_decoded_step 445 at 3111 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 446 then
    return ← `(tactic| measure_decoded_step 446 at 3118 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 447 then
    return ← `(tactic| measure_decoded_step 447 at 3126 encodedWidth 4 opcodeAST
      parse("movq %rcx,0x10(%rbx)") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step_chunk7 " row:num " using " hc:term : tactic => do
  if row.getNat == 448 then
    return ← `(tactic| measure_decoded_step 448 at 3130 encodedWidth 4 opcodeAST
      parse("movq %rdx,0x18(%rbx)") using $hc)
  if row.getNat == 449 then
    return ← `(tactic| measure_decoded_step 449 at 3134 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (91)))))] using $hc)
  if row.getNat == 450 then
    return ← `(tactic| measure_decoded_step 450 at 3227 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 451 then
    return ← `(tactic| measure_decoded_step 451 at 3235 encodedWidth 4 opcodeAST
      parse("movq %rax,0x28(%rbx)") using $hc)
  if row.getNat == 452 then
    return ← `(tactic| measure_decoded_step 452 at 3239 encodedWidth 7 opcodeAST
      parse("movl $0x3,0x40(%rbx)") using $hc)
  if row.getNat == 453 then
    return ← `(tactic| measure_decoded_step 453 at 3246 encodedWidth 2 opcodeAST
      [.instr (.regular .W64 .W64 (.jmp (.rel (.int64 (87)))))] using $hc)
  if row.getNat == 454 then
    return ← `(tactic| measure_decoded_step 454 at 3248 encodedWidth 2 opcodeAST
      parse("xorl %esi,%esi") using $hc)
  if row.getNat == 455 then
    return ← `(tactic| measure_decoded_step 455 at 3250 encodedWidth 3 opcodeAST
      parse("xorl %r8d,%r8d") using $hc)
  if row.getNat == 456 then
    return ← `(tactic| measure_decoded_step 456 at 3253 encodedWidth 3 opcodeAST
      parse("cmpq %rdi,%r8") using $hc)
  if row.getNat == 457 then
    return ← `(tactic| measure_decoded_step 457 at 3256 encodedWidth 3 opcodeAST
      parse("sbbq %rdx,%rsi") using $hc)
  if row.getNat == 458 then
    return ← `(tactic| measure_decoded_step 458 at 3259 encodedWidth 6 opcodeAST
      parse("jae measure_u3052") using $hc)
  if row.getNat == 459 then
    return ← `(tactic| measure_decoded_step 459 at 3265 encodedWidth 7 opcodeAST
      parse("movq $0x1,(%rbx)") using $hc)
  if row.getNat == 460 then
    return ← `(tactic| measure_decoded_step 460 at 3272 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x8(%rbx)") using $hc)
  if row.getNat == 461 then
    return ← `(tactic| measure_decoded_step 461 at 3280 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x10(%rbx)") using $hc)
  if row.getNat == 462 then
    return ← `(tactic| measure_decoded_step 462 at 3288 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x18(%rbx)") using $hc)
  if row.getNat == 463 then
    return ← `(tactic| measure_decoded_step 463 at 3296 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x20(%rbx)") using $hc)
  if row.getNat == 464 then
    return ← `(tactic| measure_decoded_step 464 at 3304 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x28(%rbx)") using $hc)
  if row.getNat == 465 then
    return ← `(tactic| measure_decoded_step 465 at 3312 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x30(%rbx)") using $hc)
  if row.getNat == 466 then
    return ← `(tactic| measure_decoded_step 466 at 3320 encodedWidth 8 opcodeAST
      parse("movq $0x0,0x38(%rbx)") using $hc)
  if row.getNat == 467 then
    return ← `(tactic| measure_decoded_step 467 at 3328 encodedWidth 7 opcodeAST
      parse("movl $0x1,0x40(%rbx)") using $hc)
  if row.getNat == 468 then
    return ← `(tactic| measure_decoded_step 468 at 3335 encodedWidth 7 opcodeAST
      parse("addq $0xd8,%rsp") using $hc)
  if row.getNat == 469 then
    return ← `(tactic| measure_decoded_step 469 at 3342 encodedWidth 1 opcodeAST
      parse("popq %rbx") using $hc)
  if row.getNat == 470 then
    return ← `(tactic| measure_decoded_step 470 at 3343 encodedWidth 2 opcodeAST
      parse("popq %r12") using $hc)
  if row.getNat == 471 then
    return ← `(tactic| measure_decoded_step 471 at 3345 encodedWidth 2 opcodeAST
      parse("popq %r13") using $hc)
  if row.getNat == 472 then
    return ← `(tactic| measure_decoded_step 472 at 3347 encodedWidth 2 opcodeAST
      parse("popq %r14") using $hc)
  if row.getNat == 473 then
    return ← `(tactic| measure_decoded_step 473 at 3349 encodedWidth 2 opcodeAST
      parse("popq %r15") using $hc)
  if row.getNat == 474 then
    return ← `(tactic| measure_decoded_step 474 at 3351 encodedWidth 1 opcodeAST
      parse("popq %rbp") using $hc)
  if row.getNat == 475 then
    return ← `(tactic| measure_decoded_step 475 at 3352 encodedWidth 1 opcodeAST
      parse("retq ") using $hc)
  Lean.Macro.throwError "measurement row is outside this decoding chunk"

macro "measure_step " row:num " using " hc:term : tactic => do
  if row.getNat < 64 then
    return ← `(tactic| measure_step_chunk0 $row using $hc)
  if row.getNat < 128 then
    return ← `(tactic| measure_step_chunk1 $row using $hc)
  if row.getNat < 192 then
    return ← `(tactic| measure_step_chunk2 $row using $hc)
  if row.getNat < 256 then
    return ← `(tactic| measure_step_chunk3 $row using $hc)
  if row.getNat < 320 then
    return ← `(tactic| measure_step_chunk4 $row using $hc)
  if row.getNat < 384 then
    return ← `(tactic| measure_step_chunk5 $row using $hc)
  if row.getNat < 448 then
    return ← `(tactic| measure_step_chunk6 $row using $hc)
  if row.getNat < 476 then
    return ← `(tactic| measure_step_chunk7 $row using $hc)
  Lean.Macro.throwError "measurement row index is out of range"

end SszX86.Measure

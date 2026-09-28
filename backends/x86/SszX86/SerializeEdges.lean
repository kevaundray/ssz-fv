import SszX86.SerializeStack

namespace SszX86.Serialize
open BoolCodec UintCodec
open Kraken.X64.Parser

/-- Reduce only the selected row, never every instruction in the image. -/
macro "serialize_edge_decoded " row:num " at " pc:num " encodedWidth " count:num
    " opcodeAST " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.Serialize.program) (n := $row)
     (by rw [SszX86.Serialize.program_length]; decide)
   have fetched := SszX86.Serialize.step_at _ _ $hc
     (($pc, $count, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Serialize.directives, SszX86.Serialize.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

macro "serialize_edge_step " row:num " using " hc:term : tactic => do
  if row.getNat == 0 then
    return ← `(tactic| serialize_edge_decoded 0 at 0 encodedWidth 2 opcodeAST parse("pushq %r15") using $hc)
  if row.getNat == 1 then
    return ← `(tactic| serialize_edge_decoded 1 at 2 encodedWidth 2 opcodeAST parse("pushq %r14") using $hc)
  if row.getNat == 2 then
    return ← `(tactic| serialize_edge_decoded 2 at 4 encodedWidth 2 opcodeAST parse("pushq %r13") using $hc)
  if row.getNat == 3 then
    return ← `(tactic| serialize_edge_decoded 3 at 6 encodedWidth 2 opcodeAST parse("pushq %r12") using $hc)
  if row.getNat == 4 then
    return ← `(tactic| serialize_edge_decoded 4 at 8 encodedWidth 1 opcodeAST parse("pushq %rbx") using $hc)
  if row.getNat == 5 then
    return ← `(tactic| serialize_edge_decoded 5 at 9 encodedWidth 4 opcodeAST parse("subq $0x60,%rsp") using $hc)
  if row.getNat == 6 then
    return ← `(tactic| serialize_edge_decoded 6 at 13 encodedWidth 3 opcodeAST parse("movq %r8,%r13") using $hc)
  if row.getNat == 7 then
    return ← `(tactic| serialize_edge_decoded 7 at 16 encodedWidth 3 opcodeAST parse("movq %rcx,%r14") using $hc)
  if row.getNat == 8 then
    return ← `(tactic| serialize_edge_decoded 8 at 19 encodedWidth 3 opcodeAST parse("movq %rdx,%r15") using $hc)
  if row.getNat == 9 then
    return ← `(tactic| serialize_edge_decoded 9 at 22 encodedWidth 3 opcodeAST parse("movq %rsi,%r12") using $hc)
  if row.getNat == 10 then
    return ← `(tactic| serialize_edge_decoded 10 at 25 encodedWidth 3 opcodeAST parse("movq %rdi,%rbx") using $hc)
  if row.getNat == 11 then
    return ← `(tactic| serialize_edge_decoded 11 at 28 encodedWidth 5 opcodeAST parse("leaq 0x18(%rsp),%rdi") using $hc)
  if row.getNat == 12 then
    return ← `(tactic| serialize_edge_decoded 12 at 33 encodedWidth 3 opcodeAST parse("movq %r9,%rcx") using $hc)
  if row.getNat == 13 then
    return ← `(tactic| serialize_edge_decoded 13 at 36 encodedWidth 6 opcodeAST parse("movl $0x1,%r8d") using $hc)
  if row.getNat == 14 then
    return ← `(tactic| serialize_edge_decoded 14 at 42 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-33535)))))] using $hc)
  if row.getNat == 91 then
    return ← `(tactic| serialize_edge_decoded 91 at 405 encodedWidth 5 opcodeAST
      [.instr (.regular .W64 .W64 (.call (.rel (.int64 (-30362)))))] using $hc)
  if row.getNat == 92 then
    return ← `(tactic| serialize_edge_decoded 92 at 410 encodedWidth 4 opcodeAST parse("addq $0x60,%rsp") using $hc)
  if row.getNat == 93 then
    return ← `(tactic| serialize_edge_decoded 93 at 414 encodedWidth 1 opcodeAST parse("popq %rbx") using $hc)
  if row.getNat == 94 then
    return ← `(tactic| serialize_edge_decoded 94 at 415 encodedWidth 2 opcodeAST parse("popq %r12") using $hc)
  if row.getNat == 95 then
    return ← `(tactic| serialize_edge_decoded 95 at 417 encodedWidth 2 opcodeAST parse("popq %r13") using $hc)
  if row.getNat == 96 then
    return ← `(tactic| serialize_edge_decoded 96 at 419 encodedWidth 2 opcodeAST parse("popq %r14") using $hc)
  if row.getNat == 97 then
    return ← `(tactic| serialize_edge_decoded 97 at 421 encodedWidth 2 opcodeAST parse("popq %r15") using $hc)
  if row.getNat == 98 then
    return ← `(tactic| serialize_edge_decoded 98 at 423 encodedWidth 1 opcodeAST parse("retq ") using $hc)
  Lean.Macro.throwUnsupported

macro "serialize_push " row:num " at " distance:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (serialize_edge_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.Serialize.activation_load (distance := $distance)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- PCs 0,2,4,6,8 execute the five original saves in their actual order. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 144) 144)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (savedState s, base + 9)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 40 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  serialize_push 0 at 8 using hc mapped hm
  serialize_push 1 at 16 using hc mapped hm
  serialize_push 2 at 24 using hc mapped hm
  serialize_push 3 at 32 using hc mapped hm
  serialize_push 4 at 40 using hc mapped hm
  simpa [savedState, savedMem, Width.bytesv, BitVec.sub_sub, stackReg] using next

/-- SUB96 reserves locals; the following eight instructions establish the
measurement ABI and retain all five wrapper arguments in their real registers. -/
theorem prologue_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (prologueState s, base + 42)) :
    Eventually (step e) P (savedState s, base + 9) := by
  have wrapped (value : Int) :
      BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
    simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
      (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))
  have lower : BitVec.ofInt 64 (s.regs.rsp.toBitVec.toInt - 136) =
      s.regs.rsp.toBitVec - 136#64 := by
    apply BitVec.eq_of_toInt_eq
    simp [BitVec.toInt_sub]
  have planReg : s.regs.rsp - 136 + 24 = s.regs.rsp - 112 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  have carry :
      ((s.regs.rsp.toBitVec - 136#64).unsigned !=
        (s.regs.rsp.toBitVec - 40#64).unsigned - (96#64).unsigned) =
        decide ((18446744073709551576 + s.regs.rsp.toNat) % 18446744073709551616 < 96) := by
    simpa [Udivti3.subFlags, StatusFlags.from_result, BitVec.sub_sub, BitVec.toNat_sub] using
      Udivti3.subFlags_cf (s.regs.rsp.toBitVec - 40#64) 96#64
  have stackReg : s.regs.rsp - 40 - 96 = s.regs.rsp - 136 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simp only [savedState]
  serialize_edge_step 5 using hc
  serialize_edge_step 6 using hc
  serialize_edge_step 7 using hc
  serialize_edge_step 8 using hc
  serialize_edge_step 9 using hc
  serialize_edge_step 10 using hc
  serialize_edge_step 11 using hc
  serialize_edge_step 12 using hc
  serialize_edge_step 13 using hc
  simpa [prologueState, Udivti3.subFlags, BitVec.take, BitVec.signed,
    UInt64.toBitVec_sub, wrapped, lower,
    Int.sub_sub, BitVec.sub_sub, stackReg, planReg, carry] using next

/-- CALL42 stores the real return PC47 and enters the linked Measure body. -/
theorem call42_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (callState s (base + 47).toBitVec, base + Int64.ofInt measureOffset)) :
    Eventually (step e) P (s, base + 42) := by
  serialize_edge_step 14 using hc
  apply Delimited.store_cps
  · have hmLoad := Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 hm (by decide)
    simp only [BitVec.add_zero, Width.bytes] at hmLoad ⊢
    with_unfolding_all exact hmLoad
  · simpa [callState, measureOffset, Effects.All, Int64.add_assoc] using next

/-- The actual original wrapper entry reaches the concrete measurement state.
The only memory premise is mapping of the original 144-byte wrapper activation;
no callee ownership or future execution is assumed. -/
theorem entry_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 144) 144)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (measureState s base, base + Int64.ofInt measureOffset)) :
    Eventually (step e) P (s, base) := by
  apply pushes_runs e base hc s hm P
  apply prologue_runs e base hc s P
  apply call42_runs e base hc (prologueState s)
  · have hm' := savedMem_mapped s (s.regs.rsp.toBitVec - 144) 144 hm
    have slot : (prologueState s).regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - 144 := by
      simp only [prologueState, UInt64.toBitVec_ofBitVec]
      bv_omega
    rw [slot]
    intro i hi
    exact hm' i (by omega)
  · simpa only [measureState_eq_call] using next

/-- CALL405 stores PC410 and enters the actual emitter, without postulating
anything about that callee's ownership or outcome. -/
theorem call405_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (callState s (base + 410).toBitVec, base + Int64.ofInt emitOffset)) :
    Eventually (step e) P (s, base + 405) := by
  serialize_edge_step 91 using hc
  apply Delimited.store_cps
  · have hmLoad := Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 hm (by decide)
    simp only [BitVec.add_zero, Width.bytes] at hmLoad ⊢
    with_unfolding_all exact hmLoad
  · simpa [callState, emitOffset, Effects.All, Int64.add_assoc] using next

/-- The epilogue leaves RBP and every unsaved register unchanged. -/
def returnedState (s original : MachineData) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 144)
      rbx := original.regs.rbx
      r12 := original.regs.r12
      r13 := original.regs.r13
      r14 := original.regs.r14
      r15 := original.regs.r15}
    status := Udivti3.addFlags 96 s.regs.rsp.toBitVec}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "serialize_pop " row:num " using " hc:term " word " hw:term : tactic => `(tactic|
  (serialize_edge_step $row using $hc
   simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
     SszX86.ofBytes_wordBytes, BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
     UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc]))

/-- Actual ADD96, five POPs, and the original RET423. The continuation begins
only after consuming the original caller's return address. -/
theorem epilogue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (ra : BitVec 64)
    (hs : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (returnLoad : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 136) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (returnedState s original, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 410) := by
  have returnLoad' : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 136#64) 8 =
      some (Int.ofBytes (wordBytes ra)) := by
    simpa only [show (136 : BitVec 64) = 136#64 by decide] using returnLoad
  serialize_edge_step 92 using hc
  serialize_pop 93 using hc word hs.rbx
  serialize_pop 94 using hc word hs.r12
  serialize_pop 95 using hc word hs.r13
  serialize_pop 96 using hc word hs.r14
  serialize_pop 97 using hc word hs.r15
  serialize_pop 98 using hc word returnLoad'
  have carry :
      ((s.regs.rsp.toBitVec + 96#64).unsigned !=
        (96#64).unsigned + s.regs.rsp.toBitVec.unsigned) =
        decide (Udivti3.radix ≤ 96 + s.regs.rsp.toNat) := by
    simpa [Udivti3.addFlags, StatusFlags.from_result, BitVec.add_comm] using
      Udivti3.addFlags_cf 96#64 s.regs.rsp.toBitVec
  simpa [returnedState, Udivti3.addFlags, BitVec.take, BitVec.signed,
    BitVec.add_comm, UInt64.add_comm, UInt64.add_assoc, Int.add_comm, Nat.add_comm, carry,
    returnLoad', Effects.All, SszX86.ofBytes_wordBytes,
    show (8 : UInt64) + 136 = 144 by decide] using next

/-- At the ABI boundary the final stack is original RSP+8; all five modified
callee-saved registers are restored, while unchanged RBP is merely preserved. -/
theorem returnedState_abi (s original : MachineData)
    (sp : s.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (rbp : s.regs.rbp = original.regs.rbp) :
    (returnedState s original).regs.rsp.toBitVec = original.regs.rsp.toBitVec + 8 ∧
      (returnedState s original).regs.rbx = original.regs.rbx ∧
      (returnedState s original).regs.r12 = original.regs.r12 ∧
      (returnedState s original).regs.r13 = original.regs.r13 ∧
      (returnedState s original).regs.r14 = original.regs.r14 ∧
      (returnedState s original).regs.r15 = original.regs.r15 ∧
      (returnedState s original).regs.rbp = original.regs.rbp := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rbp⟩
  simp only [returnedState, UInt64.toBitVec_ofBitVec, sp]
  bv_omega

end SszX86.Serialize

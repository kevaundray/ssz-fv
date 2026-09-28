import SszX86.NatMulMemoryStack
import SszX86.NatMulWordOwnership

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- The actual tail edge has restored the main saves and stack pointer; only
argument registers differ, and the six push stores remain in memory. -/
structure TailState (s t : MachineData) (operand : NatOperand) (factor : BitVec 64) : Prop where
  memory : t.dmem = pushedMem s
  output : t.regs.rdi = s.regs.rdi
  stack : t.regs.rsp = s.regs.rsp
  arena : t.regs.r8 = s.regs.r9
  pointer : t.regs.rsi.toBitVec = operand.pointer
  payload : t.regs.rdx.toBitVec = operand.payload
  factor : t.regs.rcx.toBitVec = factor
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  simd : t.zmms = s.zmms

theorem TailState.owned {s t : MachineData} {left right operand : NatOperand}
    {factor address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (ready : TailState s t operand factor) (stored : operand.At (widthLoad s.dmem))
    (protection : OperandProtected s address capacity used operand) :
    NatMulWord.Owned t operand factor address capacity used ra := by
  have low := owned.stack_low
  have header := pushed_header s left right address capacity used ra owned
  have initialFrame := pushed_model_frame s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) low
  refine {
    operand_pointer := ready.pointer
    operand_payload := ready.payload
    factor := ready.factor
    operand_at := ?_
    operand_owned := ?_
    output_bound := by simpa only [ready.output] using owned.output_bound
    output_mapped := ?_
    return_bound := by simpa only [ready.stack] using owned.return_bound
    return_load := ?_
    stack_low := by rw [ready.stack]; omega
    stack_mapped := ?_
    output_return := by simpa only [ready.output, ready.stack] using owned.output_return
    output_stack := ?_
    header_bound := by simpa only [ready.arena] using owned.header_bound
    address_load := by simpa only [ready.memory, ready.arena] using header.1
    capacity_load := by simpa only [ready.memory, ready.arena] using header.2.1
    used_load := by simpa only [ready.memory, ready.arena] using header.2.2
    arena_bound := owned.arena_bound
    used_bound := owned.used_bound
    arena_nonzero := owned.arena_nonzero
    free_mapped := ?_
    arena_output := by simpa only [ready.output] using owned.arena_output
    arena_stack := ?_
    arena_return := by simpa only [ready.stack] using owned.arena_return
    arena_header := by simpa only [ready.arena] using owned.arena_header
    header_output := by simpa only [ready.arena, ready.output] using owned.header_output
    header_stack := ?_
    cursor_return := by simpa only [ready.arena, ready.stack] using owned.cursor_return }
  · rw [ready.memory]
    exact operand_preserved s left right operand address capacity used ra owned _ initialFrame stored protection
  · cases operand with
    | small limb => trivial
    | large pointer words =>
      refine ⟨protection.bound, ?_, ?_, ?_, protection.arena⟩
      · simpa only [ready.output] using protection.output
      · rw [ready.stack]
        have apart := protection.activation
        unfold Body.Apart at *
        omega
      · simpa only [ready.arena] using protection.cursor
  · change Large.Mapped t.dmem t.regs.rdi.toBitVec 72
    rw [ready.memory, ready.output]
    exact pushed_mapped s _ _ owned.output_mapped
  · rw [ready.memory, ready.stack]
    exact initialFrame.return_slot owned
  · rw [ready.memory, ready.stack]
    have hm := Delimited.Reservation.mapped_subrange (pushedMem s)
      (s.regs.rsp.toBitVec-96) 96 32 64 (pushed_mapped s _ _ owned.stack_mapped) (by decide)
    have pointer : s.regs.rsp.toBitVec-96 + BitVec.ofNat 64 32 = s.regs.rsp.toBitVec-64 := by bv_omega
    rwa [pointer] at hm
  · rw [ready.output, ready.stack]
    have apart := owned.output_stack
    unfold Body.Apart at *
    omega
  · rw [ready.memory]
    exact pushed_mapped s _ _ owned.free_mapped
  · rw [ready.stack]
    have apart := owned.arena_stack
    unfold Body.Apart at *
    omega
  · rw [ready.arena, ready.stack]
    have apart := owned.header_stack
    unfold Body.Apart at *
    omega

/-- Compose the helper's original-return contract with the restored main tail
edge. The outcome equation is exactly run_right_one or run_left_one. -/
theorem TailState.post {s t : MachineData} {left right operand : NatOperand}
    {factor address capacity used ra : BitVec 64} {u : MachineState}
    (owned : Owned s left right address capacity used ra) (ready : TailState s t operand factor)
    (same : SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat =
      SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)
    (post : NatMulWord.Post t operand factor address capacity used ra u) :
    Post s left right address capacity used ra u := by
  have frame : Frame s u.1.dmem
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) := by
    intro a output activation scratch
    have helperOutside : Body.Outside a.toNat (t.regs.rsp.toNat-64) 64 := by
      rw [ready.stack]
      have low := owned.stack_low
      unfold Body.Outside at *
      omega
    have helperOutput :
        (match (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result with
        | .ok _ => Body.Outside a.toNat t.regs.rdi.toNat 16 ∧
            Body.Outside a.toNat (t.regs.rdi.toNat+64) 4
        | .error _ => Body.Outside a.toNat t.regs.rdi.toNat 68) := by
      rw [ready.output]
      cases resultEq : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result <;>
        simpa only [same, ResultOutside, resultEq] using output
    have helperScratch : ∀ r,
        (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r →
        Body.Outside a.toNat (t.regs.r8.toNat+16) 8 ∧
        Body.Outside a.toNat r.pointer
          (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length) := by
      simpa only [same, ready.arena] using scratch
    rw [post.frame a helperOutput helperOutside helperScratch, ready.memory]
    exact pushed_model_frame s _ owned.stack_low a output activation scratch
  have returned : Returned s ra u := by
    exact {
      pc := post.returned.pc
      sp := by simpa only [ready.stack] using post.returned.sp
      rbx := post.returned.rbx.trans ready.rbx
      rbp := post.returned.rbp.trans ready.rbp
      r12 := post.returned.r12.trans ready.r12
      r13 := post.returned.r13.trans ready.r13
      r14 := post.returned.r14.trans ready.r14
      r15 := post.returned.r15.trans ready.r15
      simd := post.returned.simd.trans ready.simd
      returnSlot := by simpa only [ready.stack] using post.returned.returnSlot }
  apply post_of_memory s left right address capacity used ra owned u
  · simpa only [same, ready.output] using post.observed
  · simpa only [same] using post.written
  · exact returned
  · exact frame
  · simpa only [same, ready.arena] using post.cursor

end SszX86.NatMul

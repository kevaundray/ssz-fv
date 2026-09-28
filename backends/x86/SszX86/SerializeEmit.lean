import SszX86.SerializeCall
import SszX86.SerializeFinish

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

structure BeforeEmit (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (t : MachineData) : Prop where
  anchors : AtWrapper s t
  resources : Resources s base desc value buffer address capacity used ra t.dmem
  «mapped» : BitVector.Mapping.Extends s.dmem t.dmem
  output : ∀ i < s.regs.r8.toNat,
    t.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i)
  frame : MemoryFrame s.dmem t.dmem (Writable s desc value address capacity used)

def emitState (t : MachineData) (base : Int64) : MachineData :=
  callState (emitArguments t) (base + 410).toBitVec

theorem emit_call_span (s t : MachineData) (_base : Int64) (anchors : AtWrapper s t)
    (a : BitVec 64) (inside : InSpan a (t.regs.rsp.toBitVec - 8) 8) :
    InSpan a (stackBase s) 384 := by
  have shift (p : BitVec 64) : p - 136 - 8 = p - 424 + 280 := by bv_omega
  have pointer : t.regs.rsp.toBitVec - 8 = stackBase s + 280 := by
    rw [anchors.stack]
    exact shift s.regs.rsp.toBitVec
  rw [pointer] at inside
  exact Emit.span_shift (stackBase s) 280 8 384 (by decide) inside

theorem emit_call_frame (s t : MachineData) (base : Int64) (anchors : AtWrapper s t) :
    MemoryFrame t.dmem (emitState t base).dmem (LaterWrites s) := by
  intro a outside
  exact callState_frame (emitArguments t) (base + 410).toBitVec a
    (fun inside => outside (Or.inr (Or.inr (emit_call_span s t base anchors a inside))))

theorem BeforeEmit.entry {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t) :
    EmitEntry s (emitState t base) base desc value buffer t.regs.r9.toNat := by
  have resources := before.resources.transport owned (emit_call_frame s t base before.anchors)
  refine {
    stack := ?_
    result := congrArg UInt64.toBitVec before.anchors.rbx
    descriptorPointer := congrArg UInt64.toBitVec before.anchors.r12
    valuePointer := congrArg UInt64.toBitVec before.anchors.r15
    output := congrArg UInt64.toBitVec before.anchors.r14
    length := rfl
    descriptor := resources.descriptor
    valueStored := resources.valueStored
    «mapped» := ?_
    table := resources.table
    returnSlot := callState_return_load _ _ }
  · simp only [emitState, callState, emitArguments, UInt64.toBitVec_ofBitVec,
      before.anchors.stack, wrapperSP, BitVec.sub_sub, BitVec.reduceAdd,
      show (144 : BitVec 64) = 144#64 by decide]
  · intro p n hm
    apply Large.mapped_store
    exact before.mapped p n hm

theorem emit_writes_later (s t : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer : BitVec 64) (n : Nat) (entry : EmitEntry s t base desc value buffer n)
    (fits : n ≤ s.regs.r8.toNat) (a : BitVec 64) (writes : Emit.Writable t n a) :
    LaterWrites s a := by
  rcases writes with output | result | status | scratch
  · rw [entry.output] at output
    obtain ⟨i, hi, equal⟩ := output
    exact Or.inr (Or.inl ⟨i, by omega, equal⟩)
  · rw [entry.result] at result
    obtain ⟨i, hi, equal⟩ := result
    exact Or.inl ⟨i, by omega, equal⟩
  · rw [entry.result] at status
    exact Or.inl (Emit.span_shift _ 64 4 80 (by decide) status)
  · rw [emit_stack_pointer s t entry.stack] at scratch
    exact Or.inr (Or.inr (Emit.span_shift _ 120 160 384 (by decide) scratch))

theorem emit_writes_final (s t : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (n : Nat)
    (entry : EmitEntry s t base desc value buffer n)
    (measured : ∃ operand, (SszNative.Serialize.measure desc value
      (arenaState address capacity used)).result = .ok operand)
    (success : (written s desc value address capacity used).outcome.result = .ok n)
    (encoding : (written s desc value address capacity used).writes = emit desc value)
    (valid : Emit.ValidCall desc value n n)
    (a : BitVec 64) (writes : Emit.Writable t n a) :
    Writable s desc value address capacity used a := by
  obtain ⟨operand, measured⟩ := measured
  rcases writes with output | result | status | scratch
  · right; left
    simpa only [entry.output, encoding, valid.emitted_size] using output
  · left
    simp only [ResultWrites, measured, success]
    exact Or.inl (by simpa only [entry.result] using result)
  · left
    simp only [ResultWrites, measured, success]
    exact Or.inr (by simpa only [entry.result] using status)
  · right; right; right; right
    rw [emit_stack_pointer s t entry.stack] at scratch
    exact Emit.span_shift _ 120 160 424 (by decide) scratch

/-- Successful emit is called only from a reached host-size/capacity success.
The emitter receives the measured prefix length; the original capacity tail is
separately framed against its actual writes. -/
theorem emit_runs (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (valid : Emit.ValidCall desc value t.regs.r9.toNat t.regs.r9.toNat)
    (fits : t.regs.r9.toNat ≤ s.regs.r8.toNat)
    (measured : ∃ operand, (SszNative.Serialize.measure desc value
      (arenaState address capacity used)).result = .ok operand)
    (success : (written s desc value address capacity used).outcome.result = .ok t.regs.r9.toNat)
    (encoding : (written s desc value address capacity used).writes = emit desc value) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 388) := by
  let entered := emitState t base
  have entry : EmitEntry s entered base desc value buffer t.regs.r9.toNat := before.entry owned
  have calleeOwned := owned.emit_owned entry valid fits
  have callFrame := emit_call_frame s t base before.anchors
  have callResources := before.resources.transport owned callFrame
  have callWritable : MemoryFrame t.dmem entered.dmem
      (Writable s desc value address capacity used) := by
    intro a outside
    apply callState_frame
    intro inside
    apply outside
    right; right; right; right
    obtain ⟨i, hi, equal⟩ := emit_call_span s t base before.anchors a inside
    exact ⟨i, by omega, equal⟩
  apply emit_arguments_cps e base closure.wrapper t
  apply call405_runs e base closure.wrapper (emitArguments t)
  · have hm := before.mapped (stackBase s) 424 owned.stackMapped
    have shift (p : BitVec 64) : p - 136 - 8 = p - 424 + 280 := by bv_omega
    have pointer : (emitArguments t).regs.rsp.toBitVec - 8 = stackBase s + 280 := by
      change t.regs.rsp.toBitVec - 8 = stackBase s + 280
      rw [before.anchors.stack]
      exact shift s.regs.rsp.toBitVec
    rw [pointer]
    exact Delimited.Reservation.mapped_subrange t.dmem (stackBase s) 424 280 8 hm (by decide)
  · apply eventually_trans (step e) _ _ _
      (Emit.program_correct e (base + Int64.ofInt emitOffset) closure.emit closure.emit_memcpy
        entered desc value buffer (base + 410).toBitVec t.regs.r9.toNat calleeOwned)
    rintro ⟨final, pc⟩ post
    have returned : pc = base + 410 := by simpa only [Int64.ofBitVec_toBitVec] using post.pc
    subst pc
    have anchors : AtWrapper s final := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, post.vector.trans before.anchors.vectors⟩
      · have sp := post.stack
        change final.regs.rsp.toBitVec = (t.regs.rsp.toBitVec - 8) + 8 at sp
        simpa only [BitVec.sub_add_cancel, before.anchors.stack] using sp
      all_goals apply UInt64.toBitVec_inj.1
      · exact post.rbx.trans (congrArg UInt64.toBitVec before.anchors.rbx)
      · exact post.rbp.trans (congrArg UInt64.toBitVec before.anchors.rbp)
      · exact post.r12.trans (congrArg UInt64.toBitVec before.anchors.r12)
      · exact post.r13.trans (congrArg UInt64.toBitVec before.anchors.r13)
      · exact post.r14.trans (congrArg UInt64.toBitVec before.anchors.r14)
      · exact post.r15.trans (congrArg UInt64.toBitVec before.anchors.r15)
    apply finish_runs e base closure.wrapper s final desc value buffer address capacity used ra
      owned anchors
    refine {
      resources := callResources.transport owned (fun a outside => post.memory.frame a
        (fun writes => outside (emit_writes_later s entered base desc value buffer
          t.regs.r9.toNat entry fits a writes)))
      observed := ?_
      outputFrame := ?_
      frame := ?_ }
    · simp only [success, ResultAt]
      refine ⟨?_, ?_⟩
      · have pointer : entered.regs.rdi.toNat = s.regs.rdi.toNat := by
          simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat entry.result
        simpa only [pointer] using post.memory.length
      · simp only [← UInt64.toNat_toBitVec]
        unfold widthLoad
        rw [width_address]
        simpa only [entry.result, Option.map_some, Int.toNat_zero,
          show (64 : BitVec 64) = 64#64 by decide] using
          congrArg (Option.map Int.toNat) post.memory.status
    · intro i inside
      rw [encoding]
      by_cases live : i < t.regs.r9.toNat
      · rw [applyWrites_prefix _ _ _ (by simpa only [valid.emitted_size] using live),
          Array.getElem?_eq_getElem]
        simpa only [entry.output] using post.memory.output i
          (by simpa only [valid.emitted_size] using live)
      · rw [applyWrites_tail _ _ _ (by rw [valid.emitted_size]; omega)]
        rw [post.memory.frame]
        · change (callState (emitArguments t) (base + 410).toBitVec).dmem.get?
              (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) = _
          rw [callState_frame]
          · exact before.output i inside
          · intro scratch
            obtain ⟨j, hj, equal⟩ := emit_call_span s t base before.anchors _ scratch
            exact owned.outputStack i inside j (by omega) equal
        · intro writes
          rcases writes with output | result | status | scratch
          · obtain ⟨j, hj, equal⟩ := output
            rw [entry.output] at equal
            have index := memmove_addr_injective s.regs.rcx.toBitVec s.regs.r8.toNat
              i j owned.outputBound inside (by omega) equal
            omega
          · obtain ⟨j, hj, equal⟩ := result
            rw [entry.result] at equal
            exact owned.outputResult i inside j (by omega) equal
          · obtain ⟨j, hj, equal⟩ := status
            rw [entry.result] at equal
            exact owned.outputResult i inside (64 + j) (by omega) (by
              rw [BitVec.ofNat_add]
              simpa only [BitVec.add_assoc, show (64 : BitVec 64) = 64#64 by decide] using equal)
          · rw [emit_stack_pointer s entered entry.stack] at scratch
            obtain ⟨j, hj, equal⟩ := Emit.span_shift (stackBase s) 120 160 432 (by decide) scratch
            exact owned.outputStack i inside j hj equal
    · intro a outside
      rw [post.memory.frame a (fun writes => outside
        (emit_writes_final s entered base desc value buffer address capacity used
          t.regs.r9.toNat entry measured success encoding valid a writes)), callWritable a outside]
      exact before.frame a outside

end SszX86.Serialize

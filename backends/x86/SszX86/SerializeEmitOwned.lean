import SszX86.SerializeCore

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

/-- The actual emitter entry after CALL405. These are intermediate state facts,
not original-entry premises or a promise that a future call succeeds. -/
structure EmitEntry (s t : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer : BitVec 64) (n : Nat) : Prop where
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 144
  result : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec
  descriptorPointer : t.regs.rsi.toBitVec = s.regs.rsi.toBitVec
  valuePointer : t.regs.rdx.toBitVec = s.regs.rdx.toBitVec
  output : t.regs.r8.toBitVec = s.regs.rcx.toBitVec
  length : t.regs.r9.toNat = n
  descriptor : Emit.DescAt t.dmem s.regs.rsi.toBitVec desc
  valueStored : Emit.ValueAt t.dmem s.regs.rdx.toBitVec buffer value
  «mapped» : BitVector.Mapping.Extends s.dmem t.dmem
  table : Emit.TableAt t.dmem (base + Int64.ofInt emitOffset)
  returnSlot : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes (base + 410).toBitVec))

theorem stack_subspan (s : MachineData) (off n : Nat) (within : off + n ≤ 424)
    (a : BitVec 64) (inside : InSpan a (stackBase s + BitVec.ofNat 64 off) n) :
    InSpan a (stackBase s) 424 :=
  Emit.span_shift (stackBase s) off n 424 within inside

theorem emit_stack_pointer (s t : MachineData)
    (stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 144) :
    t.regs.rsp.toBitVec - 160 = stackBase s + 120 := by
  rw [stack]
  simp only [stackBase]
  bv_omega

theorem emit_writes_reserved (s t : MachineData) (base : Int64)
    (desc : Desc) (value : Value) (buffer address capacity used : BitVec 64) (n : Nat)
    (anchors : EmitEntry s t base desc value buffer n) (fits : n ≤ s.regs.r8.toNat)
    (a : BitVec 64) (writes : Emit.Writable t n a) : Reserved s address capacity used a := by
  rcases writes with output | result | status | scratch
  · rw [anchors.output] at output
    obtain ⟨i, hi, equal⟩ := output
    exact Or.inr (Or.inl ⟨i, by omega, equal⟩)
  · rw [anchors.result] at result
    obtain ⟨i, hi, equal⟩ := result
    exact Or.inl ⟨i, by omega, equal⟩
  · rw [anchors.result] at status
    exact Or.inl (Emit.span_shift _ 64 4 80 (by decide) status)
  · rw [emit_stack_pointer s t anchors.stack] at scratch
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (stack_subspan s 120 160 (by decide) a scratch))))

/-- Successful measurement and host narrowing derive the emitter's logical call;
all physical requirements come from original ownership and reached-state facts. -/
theorem Owned.emit_owned {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {n : Nat}
    (owned : Owned s base desc value buffer address capacity used ra)
    (anchors : EmitEntry s t base desc value buffer n)
    (valid : Emit.ValidCall desc value n n) (fits : n ≤ s.regs.r8.toNat) :
    Emit.Owned t (base + Int64.ofInt emitOffset) desc value buffer
      (base + 410).toBitVec n := by
  have rsp := anchors.stack
  have low := owned.stackLow
  have upper := owned.returnBound
  have spNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 144 := by
    simp only [← UInt64.toNat_toBitVec] at low ⊢
    bv_omega
  have resultNat : t.regs.rdi.toNat = s.regs.rdi.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat anchors.result
  have descriptorNat : t.regs.rsi.toNat = s.regs.rsi.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat anchors.descriptorPointer
  have valueNat : t.regs.rdx.toNat = s.regs.rdx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat anchors.valuePointer
  have outputNat : t.regs.r8.toNat = s.regs.rcx.toNat := by
    simpa only [UInt64.toNat_toBitVec] using congrArg BitVec.toNat anchors.output
  have stackPointer := emit_stack_pointer s t anchors.stack
  have mappedStack : Large.Mapped t.dmem (stackBase s) 424 :=
    anchors.mapped _ _ owned.stackMapped
  have mappedResult : Large.Mapped t.dmem s.regs.rdi.toBitVec 80 :=
    anchors.mapped _ _ owned.resultMapped
  refine {
    valid := by simpa only [anchors.length] using valid
    physical := owned.physical
    descriptor := by simpa only [anchors.descriptorPointer] using anchors.descriptor
    valueStored := by simpa only [anchors.valuePointer] using anchors.valueStored
    descriptorBound := by simpa only [descriptorNat] using owned.descriptorBound
    valueBound := by simpa only [valueNat] using owned.valueBound
    outputBound := by rw [outputNat, anchors.length]; have := owned.outputBound; omega
    resultBound := by simpa only [resultNat] using owned.resultBound
    stackLow := by omega
    returnBound := by omega
    outputMapped := ?_
    lengthMapped := ?_
    statusMapped := ?_
    stackMapped := ?_
    returnSlot := anchors.returnSlot
    outputResult := ?_
    outputStack := ?_
    resultStack := ?_
    tailReadonly := ?_
    readonly := ?_
    table := anchors.table
    tableReadonly := ?_ }
  · rw [anchors.output]
    have hm := anchors.mapped _ _ owned.outputMapped
    intro i hi
    exact hm i (by omega)
  · rw [anchors.result]
    intro i hi
    exact mappedResult i (by omega)
  · rw [anchors.result]
    exact Delimited.Reservation.mapped_subrange t.dmem s.regs.rdi.toBitVec
      80 64 4 mappedResult (by decide)
  · rw [stackPointer]
    exact Delimited.Reservation.mapped_subrange t.dmem (stackBase s)
      424 120 160 mappedStack (by decide)
  · rw [anchors.output, anchors.result]
    intro i hi j hj
    exact owned.outputResult i (by omega) j hj
  · rw [anchors.output, stackPointer]
    intro i hi j hj equal
    apply owned.outputStack i (by omega) (120 + j) (by omega)
    calc
      s.regs.rcx.toBitVec + BitVec.ofNat 64 i =
          stackBase s + 120 + BitVec.ofNat 64 j := equal
      _ = stackBase s + BitVec.ofNat 64 (120 + j) := by
        simp only [BitVec.ofNat_add, BitVec.add_assoc, show (120 : BitVec 64) = 120#64 by decide]
  · rw [anchors.result, stackPointer]
    intro i hi j hj equal
    apply owned.resultStack i hi (120 + j) (by omega)
    calc
      s.regs.rdi.toBitVec + BitVec.ofNat 64 i =
          stackBase s + 120 + BitVec.ofNat 64 j := equal
      _ = stackBase s + BitVec.ofNat 64 (120 + j) := by
        simp only [BitVec.ofNat_add, BitVec.add_assoc, show (120 : BitVec 64) = 120#64 by decide]
  · intro i after inside
    rw [anchors.length] at inside
    omega
  · intro a borrowed writes
    have original : Emit.Borrowed s desc value buffer a := by
      simpa only [Emit.Borrowed, anchors.descriptorPointer, anchors.valuePointer] using borrowed
    exact owned.readonly a original
      (emit_writes_reserved s t base desc value buffer address capacity used n anchors fits a writes)
  · intro a inside writes
    exact owned.emitTableReadonly a inside
      (emit_writes_reserved s t base desc value buffer address capacity used n anchors fits a writes)

end SszX86.Serialize

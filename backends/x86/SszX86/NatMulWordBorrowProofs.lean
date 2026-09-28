import SszX86.NatMulWordBorrowMemory

namespace SszX86.NatMulWord
open SszNative UintCodec

private def returnedState (t : MachineData) (m : DataMem) : MachineData :=
  {t with dmem := m, regs := {t.regs with rsp := UInt64.ofBitVec (t.regs.rsp.toBitVec + 8)}}

theorem borrowed_post (s t : MachineData) (operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s operand 1 address capacity used ra)
    (frame : BorrowFrame s t) :
    Post s operand 1 address capacity used ra
      (returnedState t (successMem s.dmem s.regs.rdi.toBitVec
        operand.normalized.pointer operand.normalized.payload), Int64.ofBitVec ra) := by
  have publication := success_output_frame s.dmem s.regs.rdi.toBitVec
    operand.normalized.pointer operand.normalized.payload owned.output_bound
  have returnLoad := return_after_output s operand 1 address capacity used ra owned _ publication
  have input := operand_after_output s operand 1 address capacity used ra owned _ publication
  have result := NatOperand.normalized_at (widthLoad _) operand input
  have fields := NatAdd.success_reads s.dmem s.regs.rdi.toBitVec
    operand.normalized.pointer operand.normalized.payload
  have model := SszNative.NatMul.runWord_one operand address.toNat capacity.toNat used.toNat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [model]
    exact ⟨⟨fields.1, fields.2.1, result⟩, fields.2.2⟩
  · intro r allocated
    rw [model] at allocated
    cases allocated
  · refine ⟨rfl, ?_, frame.rbx, frame.rbp, frame.r12, frame.r13,
      frame.r14, frame.r15, frame.simd, returnLoad⟩
    simp only [returnedState, UInt64.toBitVec_ofBitVec, frame.stack]
  · rw [model]
    exact success_exact_frame s operand.normalized used.toNat owned.output_bound
  · rw [model]
    exact cursor_after_output s operand 1 address capacity used ra owned _ publication
  · exact input

theorem zero_post (s t : MachineData) (operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s operand 0 address capacity used ra)
    (frame : BorrowFrame s t) :
    Post s operand 0 address capacity used ra
      (returnedState t (zeroMem s.dmem s.regs.rdi.toBitVec), Int64.ofBitVec ra) := by
  have publication := zero_output_frame s.dmem s.regs.rdi.toBitVec owned.output_bound
  have returnLoad := return_after_output s operand 0 address capacity used ra owned _ publication
  have fields := zero_reads s.dmem s.regs.rdi.toBitVec
  have model := SszNative.NatMul.runWord_zero operand address.toNat capacity.toNat used.toNat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [model]
    exact ⟨⟨fields.1, fields.2.1, True.intro⟩, fields.2.2⟩
  · intro r allocated
    rw [model] at allocated
    cases allocated
  · refine ⟨rfl, ?_, frame.rbx, frame.rbp, frame.r12, frame.r13,
      frame.r14, frame.r15, frame.simd, returnLoad⟩
    simp only [returnedState, UInt64.toBitVec_ofBitVec, frame.stack]
  · rw [model]
    exact zero_exact_frame s used.toNat owned.output_bound
  · rw [model]
    exact cursor_after_output s operand 0 address capacity used ra owned _ publication
  · exact operand_after_output s operand 0 address capacity used ra owned _ publication

/-- Factor zero performs no scan, allocation or stack adjustment. -/
theorem mul_word_zero_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s operand 0 address capacity used ra) :
    Eventually (step e) (Post s operand 0 address capacity used ra) (s, base) := by
  apply entry_zero_cps e base hc s owned.factor
  intro flags
  apply zero_cps e base hc (entryState s flags) owned.output_mapped
  apply (ret_cps e base hc _ ra _ ?_ ?_).1
  · exact return_after_output s operand 0 address capacity used ra owned _
      (zero_output_frame s.dmem s.regs.rdi.toBitVec owned.output_bound)
  · exact zero_post s (entryState s flags) operand address capacity used ra owned
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem borrowed_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s operand 1 address capacity used ra) (frame : BorrowFrame s t)
    (pointer : t.regs.rsi.toBitVec = operand.normalized.pointer)
    (payload : t.regs.r9.toBitVec = operand.normalized.payload) :
    Eventually (step e) (Post s operand 1 address capacity used ra) (t, base + 84) ∧
    Eventually (step e) (Post s operand 1 address capacity used ra) (t, base + 373) := by
  have outputMapped : OutputMapped t := by
    unfold OutputMapped
    rw [frame.memory, frame.output]
    exact owned.output_mapped
  have returnLoad := return_after_output s operand 1 address capacity used ra owned _
    (success_output_frame s.dmem s.regs.rdi.toBitVec
      operand.normalized.pointer operand.normalized.payload owned.output_bound)
  apply borrowed_publish_cps e base hc t outputMapped
  · apply (ret_cps e base hc _ ra _ ?_ ?_).2.1
    · simpa only [frame.memory, frame.output, frame.stack, pointer, payload] using returnLoad
    · simpa only [returnedState, frame.memory, frame.output, pointer, payload]
        using borrowed_post s t operand address capacity used ra owned frame
  · apply (ret_cps e base hc _ ra _ ?_ ?_).2.2.1
    · simpa only [frame.memory, frame.output, frame.stack, pointer, payload] using returnLoad
    · simpa only [returnedState, frame.memory, frame.output, pointer, payload]
        using borrowed_post s t operand address capacity used ra owned frame

/-- Factor one normalizes the original raw representation and returns the exact
borrowed pointer, preserving all original limbs and the untouched envelope bytes. -/
theorem mul_word_one_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s operand 1 address capacity used ra) :
    Eventually (step e) (Post s operand 1 address capacity used ra) (s, base) := by
  apply entry_one_cps e base hc s owned.factor
  intro flags
  apply normalize_operand_cps e base hc (entryState s flags) operand
    owned.operand_pointer owned.operand_payload owned.operand_at
  intro t pc normalized pointer payload site
  have initialFrame : BorrowFrame s (entryState s flags) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have result := borrowed_return_cps e base hc s t operand address capacity used ra owned
    (initialFrame.trans normalized) pointer payload
  rcases site with rfl | rfl
  · exact result.1
  · exact result.2

end SszX86.NatMulWord

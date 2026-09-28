import SszX86.MeasureBitsVectorPost

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem single_unallocated_post (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (reason : Error)
    (call : NatArithmetic.Outcome NatOperand)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) = ⟨.error reason, used.toNat, [call]⟩)
    (unallocated : call.allocation = none)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (observed : ErrorAt (widthLoad t.dmem) s.regs.rbx.toNat reason)
    (frame : MemoryFrame s.dmem t.dmem (fun a => InSpan a s.regs.rbx.toBitVec 68)) :
    BodyPost s desc value buffer address capacity used t := by
  have resultFrame : MemoryFrame s.dmem t.dmem
      (ResultWrites s.regs.rbx.toBitVec (measure desc value (arenaState address capacity used))) := by
    rw [model]
    intro a outside
    exact frame a (fun written => outside (Or.inl written))
  have header := owned.publication_header t.dmem _ resultFrame
  refine ⟨stack, ?_, ?_, ⟨header.1, header.2.1⟩, ?_,
    owned.publication_descriptor t.dmem _ resultFrame,
    owned.publication_value t.dmem _ resultFrame, ?_, vectors⟩
  · simpa only [model, ResultAt] using observed
  · simpa only [model, UInt64.toNat_toBitVec] using header.2.2
  · rw [model]
    intro selected member reservation allocated
    have equal : selected = call := by simpa only [List.mem_singleton] using member
    subst selected
    rw [unallocated] at allocated
    cases allocated
  · intro a outside
    exact resultFrame a (fun written => outside (Or.inl written))

theorem vector_small_scope_post (s t : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (mismatch : expected.value ≠ bits.count.toNat) (small : bits.count.toNat < 2^64)
    (memory : t.dmem = scopeMem s.dmem s.regs.rbx.toBitVec expected.pointer expected.payload
      0#64 (bits.count.setWidth 64))
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms) :
    BodyPost s (.bitVector expected) (.bits bits) buffer address capacity used t := by
  let call := NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count
  have callModel := NatFromU128.result_model_small address capacity used bits.count small
  change NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count =
    NatArithmetic.unchanged used.toNat (.ok (.small (bits.count.setWidth 64))) at callModel
  have model : measure (.bitVector expected) (.bits bits) (arenaState address capacity used) =
      ⟨.error (.scope expected (.small (bits.count.setWidth 64))), used.toNat, [call]⟩ := by
    simp only [Serialize.measure, mismatch, ↓reduceIte, Serialize.bind, fromWide, arenaState, call,
      callModel, Except.mapError, unchanged, NatArithmetic.unchanged, List.append_nil]
  have pub := scope_frame s.dmem s.regs.rbx.toBitVec expected.pointer expected.payload
    0#64 (bits.count.setWidth 64)
  have expectedAfter : expected.At (widthLoad t.dmem) := by
    rw [memory]
    apply operand_frame _ _ _ pub expected _ owned.descriptor.2.2.2
    intro a borrowed written
    apply owned.readonly a (Or.inr (Or.inr (Or.inl borrowed)))
    exact Or.inl (by obtain ⟨i, hi, rfl⟩ := written; exact ⟨i, by omega, rfl⟩)
  apply single_unallocated_post s t _ _ buffer address capacity used _ call owned model
    (by dsimp only [call]; rw [callModel]; rfl) stack vectors
  · rw [memory]
    exact scope_reads _ _ expected (.small (bits.count.setWidth 64))
      (by simpa only [memory, NatOperand.pointer, NatOperand.payload] using expectedAfter) trivial
  · rw [memory]
    exact pub

theorem scratch_frame (m : DataMem) (out : BitVec 64) :
    MemoryFrame m (NatAdd.errorMem m out) (fun a => InSpan a out 68) := by
  intro a outside
  apply NatAdd.error_mem_frame
  intro i hi equal
  exact outside ⟨i, hi, equal⟩

theorem vector_scratch_post (s t : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (mismatch : expected.value ≠ bits.count.toNat) (large : ¬ bits.count.toNat < 2^64)
    (failed : Arena.reserve address.toNat capacity.toNat used.toNat 2 = none)
    (memory : t.dmem = NatAdd.errorMem s.dmem s.regs.rbx.toBitVec)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms) :
    BodyPost s (.bitVector expected) (.bits bits) buffer address capacity used t := by
  let call := NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count
  have callModel := NatFromU128.result_model_failure address capacity used bits.count large failed
  change NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count =
    NatArithmetic.unchanged used.toNat (.error .scratchExhausted) at callModel
  have model : measure (.bitVector expected) (.bits bits) (arenaState address capacity used) =
      ⟨.error (.arithmetic .scratchExhausted), used.toNat, [call]⟩ := by
    simp only [Serialize.measure, mismatch, ↓reduceIte, Serialize.bind, fromWide, arenaState, call,
      callModel, Except.mapError, NatArithmetic.unchanged]
  apply single_unallocated_post s t _ _ buffer address capacity used _ call owned model
    (by dsimp only [call]; rw [callModel]; rfl) stack vectors
  · rw [memory]
    exact NatAdd.error_reads s.dmem s.regs.rbx.toBitVec
  · rw [memory]
    exact scratch_frame _ _

end SszX86.Measure.Bits

import SszX86.MeasureBitsStored
import SszX86.BitVectorErrorsReadMemory

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- The assembly unconditionally loads all three words, even for None. Only the
low discriminant is constrained; inactive payload and high tag padding stay free. -/
structure OptionWords (s : MachineData) (limit : Option NatOperand)
    (tag pointer payload : BitVec 64) : Prop where
  tagLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (tag.toNat : Int)
  pointerLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (pointer.toNat : Int)
  payloadLoad : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 24) 8 = some (payload.toNat : Int)
  selected : tag.setWidth 8 &&& 1#8 = if limit.isSome then 1#8 else 0#8
  bounded : ∀ cap, limit = some cap → pointer = cap.pointer ∧ payload = cap.payload

theorem progressive_option_words (s : MachineData) (limit : Option NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList limit) (.bits bits) buffer address capacity used) :
    ∃ tag pointer payload, OptionWords s limit tag pointer payload := by
  have mappedTag := Large.mapped_load s.dmem s.regs.rsi.toBitVec 32 8 8 owned.descriptorMapped (by decide)
  obtain ⟨tag, tagLoad⟩ := BitVector.mapped_word s.dmem (s.regs.rsi.toBitVec + 8) 8 mappedTag
  cases limit with
  | none =>
    have mappedPointer := Large.mapped_load s.dmem s.regs.rsi.toBitVec 32 16 8 owned.descriptorMapped (by decide)
    have mappedPayload := Large.mapped_load s.dmem s.regs.rsi.toBitVec 32 24 8 owned.descriptorMapped (by decide)
    obtain ⟨pointer, pointerLoad⟩ := BitVector.mapped_word s.dmem (s.regs.rsi.toBitVec + 16) 8 mappedPointer
    obtain ⟨payload, payloadLoad⟩ := BitVector.mapped_word s.dmem (s.regs.rsi.toBitVec + 24) 8 mappedPayload
    have tag32 := BitVector.errors_load_low32 s.dmem (s.regs.rsi.toBitVec + 8) tag 0 tagLoad owned.descriptor.2
    have tag8 := congrArg (fun v : BitVec 32 => v.setWidth 8) tag32
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] at tag8
    refine ⟨tag, pointer, payload, tagLoad, pointerLoad, payloadLoad, ?_, ?_⟩
    · rw [tag8]
      rfl
    · intro cap impossible
      cases impossible
  | some cap =>
    have words := nat_loads s.dmem (s.regs.rsi.toBitVec + 16) cap owned.descriptor.2.2
    have tag32 := BitVector.errors_load_low32 s.dmem (s.regs.rsi.toBitVec + 8) tag 1 tagLoad owned.descriptor.2.1
    have tag8 := congrArg (fun v : BitVec 32 => v.setWidth 8) tag32
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] at tag8
    refine ⟨tag, cap.pointer, cap.payload, tagLoad, words.1, ?_, ?_, ?_⟩
    · have stored := words.2
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at stored
      with_unfolding_all exact stored
    · rw [tag8]
      rfl
    · intro other equal
      cases equal
      exact ⟨rfl, rfl⟩

end SszX86.Measure.Bits

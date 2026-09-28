import SszX86.MeasureBitsVectorBody
import SszX86.MeasureBitsListCount
import SszX86.MeasureBitsProgressiveCount

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

/-- Every actual BitVector body outcome, including wrong Value kind, padded
logical length comparison, Scope construction, and count-allocation failure. -/
theorem bitvector_body_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expected : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧ BodyPost s (.bitVector expected) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.bitVector expected))) :=
  Bits.vector_body e base hc s expected value buffer address capacity used owned

/-- The exact BitList879 entry: first count allocation, borrowed Nat comparison,
optional second allocation, and publication. Neither allocation is rolled back. -/
theorem bitlist_body_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (cap : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitList cap) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧ BodyPost s (.bitList cap) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.bitList cap))) := by
  change Eventually (step e) _ (s, base + 879)
  cases value with
  | bits bits =>
    apply Bits.list_tag_cps e base hc
    intro flags
    simp only [owned.tag, valueTag, Emit.valueTag, ↓reduceIte]
    have descriptorWords := Bits.nat_loads s.dmem (s.regs.rsi.toBitVec + 8) cap owned.descriptor.2
    apply Bits.list_load_cps e base hc (pointer := cap.pointer) (payload := cap.payload)
      (low := bits.count.setWidth 64) (high := (bits.count >>> 64).setWidth 64)
    · exact descriptorWords.1
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using descriptorWords.2
    · exact owned.valueStored.2.2.2.1
    · exact owned.valueStored.2.2.2.2.1
    exact Bits.list_count_cps e base hc helpers s _ cap bits buffer address capacity used owned
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | bool boolean | uint number | bytes data | seq values | union selector child =>
    apply Bits.list_wrong_type e base hc s cap _ buffer address capacity used owned
    simp only [valueTag, Emit.valueTag]
    decide

/-- The exact progressiveBitList929 entry for None and Some, arbitrary inactive
enum words, arbitrary original Nat padding, and every semantic/resource result. -/
theorem progressive_body_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (limit : Option NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList limit) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.progressiveBitList limit) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.progressiveBitList limit))) := by
  change Eventually (step e) _ (s, base + 929)
  cases value with
  | bits bits =>
    obtain ⟨tag, pointer, payload, words⟩ := Bits.progressive_option_words s limit bits
      buffer address capacity used owned
    apply Bits.progressive_tag_cps e base hc
    intro flags
    simp only [owned.tag, valueTag, Emit.valueTag, ↓reduceIte]
    apply Bits.progressive_load_cps e base hc (tag := tag) (pointer := pointer) (payload := payload)
      (low := bits.count.setWidth 64) (high := (bits.count >>> 64).setWidth 64)
    · exact words.tagLoad
    · exact words.pointerLoad
    · exact words.payloadLoad
    · exact owned.valueStored.2.2.2.1
    · exact owned.valueStored.2.2.2.2.1
    apply Bits.progressive_count_cps e base hc helpers s _ limit bits buffer address capacity used owned
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact words.selected
    · exact words.bounded
    · rfl
    · rfl
  | bool boolean | uint number | bytes data | seq values | union selector child =>
    apply Bits.progressive_wrong_type e base hc s limit _ buffer address capacity used owned
    simp only [valueTag, Emit.valueTag]
    decide

end SszX86.Measure

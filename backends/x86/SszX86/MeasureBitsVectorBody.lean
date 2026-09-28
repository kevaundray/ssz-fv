import SszX86.MeasureBitsVectorError
import SszX86.MeasureBitsWrongType
import SszX86.MeasureFinish

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- Actual BitVector82 through3335 for all represented lengths and all values.
Mismatch count allocation precedes Scope and may instead exhaust scratch. -/
theorem vector_body (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (expected : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.bitVector expected) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.bitVector expected))) := by
  change Eventually (step e) _ (s, base + 82)
  cases value with
  | bits bits =>
    apply vector_tag_cps e base hc
    intro flags
    simp only [owned.tag, valueTag, Emit.valueTag, ↓reduceIte]
    have descriptorWords := nat_loads s.dmem (s.regs.rsi.toBitVec + 8) expected owned.descriptor.2
    apply vector_load_cps e base hc (pointer := expected.pointer) (payload := expected.payload)
      (low := bits.count.setWidth 64) (high := (bits.count >>> 64).setWidth 64)
    · exact descriptorWords.1
    · simpa only [BitVec.add_assoc, BitVec.reduceAdd] using descriptorWords.2
    · exact owned.valueStored.2.2.2.1
    · exact owned.valueStored.2.2.2.2.1
    apply eventually_trans (step e)
      (VectorChecked (vectorLoaded {s with status := flags} expected.pointer expected.payload
        (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)) expected bits.count base) _ _
      (vector_check_runs e base hc _ expected bits.count rfl rfl rfl rfl owned.descriptor.2.2.2)
    rintro ⟨u, pc⟩ ⟨frame, endpoint⟩
    have originalFrame : VectorReadFrame (vectorInput s expected bits) u :=
      ⟨frame.memory, frame.vectors, frame.output, frame.stack, frame.descriptor,
        frame.input, frame.arena, frame.low, frame.high⟩
    change pc = _ at endpoint
    by_cases same : expected.value = bits.count.toNat
    · rw [ite_eq_left same] at endpoint
      subst pc
      have byteBound : bits.bytes.size < 2^64 := owned.physical
      have byteValue : (BitVec.ofNat 64 bits.bytes.size).toNat = bits.bytes.size := Nat.mod_eq_of_lt byteBound
      apply vector_size_cps e base hc (byteCount := BitVec.ofNat 64 bits.bytes.size)
      · simp only [originalFrame.memory, originalFrame.input, vectorInput, vectorLoaded, byteValue]
        with_unfolding_all exact owned.valueStored.2.2.1
      apply small_success_body_cps e base hc s _ (.bitVector expected) (.bits bits)
        buffer address capacity used (BitVec.ofNat 64 bits.bytes.size) owned
      · simp only [Serialize.measure, same, ↓reduceIte, unchanged, arenaState, count]
      · exact frame.memory
      · exact frame.output
      · exact frame.stack
      · exact frame.vectors
      · rfl
    · rw [ite_eq_right same] at endpoint
      subst pc
      exact vector_error_cps e base hc s u expected bits buffer address capacity used owned same originalFrame
  | bool boolean | uint number | bytes data | seq values | union selector child =>
    apply vector_wrong_type e base hc s expected _ buffer address capacity used owned
    simp only [valueTag, Emit.valueTag]
    decide

end SszX86.Measure.Bits

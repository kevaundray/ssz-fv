import SszArm.NatAddSmallCorrectFinish

namespace SszArm.NatAdd.SmallCorrect

open UintCodec SszNative
open NatCompare (Operand saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem operand_low (s : ArmState) (pointer payload : BitVec 64)
    (words : List (BitVec 64)) (input : Operand s pointer payload words)
    (nonempty : 0 < words.length) :
    if pointer = 0#64 then payload = words[0]?.getD 0#64 else
      payload ≠ 0#64 ∧ read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
  rcases input with ⟨zero, rfl⟩ | ⟨nonzero, length, source, stored⟩
  · simp [zero]
  · rw [if_neg nonzero]
    refine ⟨?_, ?_⟩
    · intro zero
      rw [zero] at length
      simp only [BitVec.toNat_ofNat] at length
      omega
    · simpa [List.getElem?_eq_getElem nonempty] using stored ⟨0, nonempty⟩

theorem words_positive (operand : NatOperand) (nonzero : operand.wordCount ≠ 0) :
    0 < operand.words.length := by
  have bound := Limbs.sigWords_le_length operand.words
  change Limbs.sigWords operand.words ≠ 0 at nonzero
  omega

/-- The input predicates justify both direct low loads and the conditional
saved-X10 stack write before the right load. The original arrays may alias. -/
theorem load_observations (s : ArmState) (left right : NatOperand)
    (owned : Owned s left right) (hl : left.wordCount ≠ 0) (hr : right.wordCount ≠ 0) :
    (if r (.GPR 1#5) s = 0#64 then r (.GPR 2#5) s = SszNative.NatAdd.lowWord left else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = SszNative.NatAdd.lowWord left) ∧
    (if r (.GPR 3#5) s = 0#64 then r (.GPR 4#5) s = SszNative.NatAdd.lowWord right else
      r (.GPR 4#5) s ≠ 0#64 ∧
        read_mem_bytes 8 (r (.GPR 3#5) s) (oneWordSaved s) = SszNative.NatAdd.lowWord right) := by
  have inputs := owned.operands
  constructor
  · exact operand_low s _ _ left.words inputs.1 (words_positive left hl)
  · have rightInput : Operand (oneWordSaved s) (r (.GPR 3#5) s)
        (r (.GPR 4#5) s) right.words := by
      by_cases smallLeft : r (.GPR 1#5) s = 0#64
      · simpa only [oneWordSaved, smallLeft, ↓reduceIte] using
          (NatCompare.saved_frame s 10#5 owned.stackBound).operand _ _ right.words inputs.2
      · simpa only [oneWordSaved, smallLeft, ↓reduceIte] using inputs.2
    exact operand_low (oneWordSaved s) _ _ right.words rightInput (words_positive right hr)

theorem load_prefix (s : ArmState) (base a b : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ZeroFrame s (oneWordLoadResult s base a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, one_word_load_memory s base a b stack⟩
  · by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]
  · by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]
  · by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]
  · by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]
  · intro reg lo hi
    have r2 : reg ≠ 2#5 := by bv_omega
    have r4 : reg ≠ 4#5 := by bv_omega
    have r8 : reg ≠ 8#5 := by bv_omega
    by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules, r2, r4, r8]
  · intro reg lo hi
    by_cases small : r (.GPR 1#5) s = 0#64 <;>
      simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]

theorem load_arena_register (s : ArmState) (base a b : BitVec 64) :
    r (.GPR 5#5) (oneWordLoadResult s base a b) = r (.GPR 5#5) s := by
  by_cases small : r (.GPR 1#5) s = 0#64 <;>
    simp [oneWordLoadResult, oneWordSaved, small, saved, state_simp_rules]

theorem small_of_pointer_zero (s : ArmState) (operand : NatOperand)
    (input : operand.At (widthLoad s)) (zero : operand.pointer = 0#64) :
    ∃ word, operand = .small word := by
  cases operand with
  | small word => exact ⟨word, rfl⟩
  | large pointer words =>
    have positive := input.1
    change pointer = 0#64 at zero
    rw [zero] at positive
    simp at positive

end SszArm.NatAdd.SmallCorrect

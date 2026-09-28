import SszX86.NatMulWordSmallComplete
import SszX86.NatMulWordBorrowProofs

namespace SszX86.NatMulWord
open SszNative

/-- Every raw inline operand follows the original complete word image. This
includes factor zero/one and both inline and allocated 128-bit products. -/
theorem mul_word_inline_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb factor address capacity used ra : BitVec 64)
    (owned : Owned s (.small limb) factor address capacity used ra) :
    Eventually (step e) (Post s (.small limb) factor address capacity used ra) (s, base) := by
  by_cases zero : factor = 0
  · subst factor
    exact mul_word_zero_correct e base hc s (.small limb) address capacity used ra owned
  by_cases one : factor = 1
  · subst factor
    exact mul_word_one_correct e base hc s (.small limb) address capacity used ra owned
  have scalar : (NatOperand.small limb).wordCount ≤ 1 := Limbs.sigWords_le_length [limb]
  apply entry_multiply_cps e base hc s
    (by simpa only [owned.factor, show (0 : BitVec 64) = 0#64 by decide] using zero)
    (by simpa only [owned.factor, show (1 : BitVec 64) = 1#64 by decide] using one)
  intro entryFlags
  apply pushes_cps e base hc (entryState s entryFlags) owned.stack_mapped
  intro stackFlags
  apply select_operand_cps e base hc (pushedState (entryState s entryFlags) stackFlags)
  · intro inline selectorFlags
    apply small_multiply_cps e base hc s _ (.small limb) factor address capacity used ra owned zero one scalar
    · refine ⟨?_, ?_, rfl, rfl, rfl⟩
      · rfl
      · exact UInt64.toBitVec_ofBitVec _
    · simpa only [pushedState, entryState, SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord,
        NatOperand.words, List.getElem?_cons_zero, Option.getD_some] using owned.operand_payload
    · exact owned.factor
  · intro large selectorFlags
    exact False.elim (large owned.operand_pointer)

end SszX86.NatMulWord

import SszArm.NatDivisionClassify
import SszArm.NatDivisionFastSource

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Classification retains the original Large descriptor and supplies exactly
the two-word view consumed by the selected real BL setup. Physical length is
not restricted to two: only the significant count selects this path. -/
theorem classified_large_fast (original s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (owned : Owned original (.large pointer words))
    (classified : Classified original s base (.large pointer words))
    (count : (SszNative.NatOperand.large pointer words).wordCount ≤ 2) :
    ∃ site : FastSite, read_pc s = base + BitVec.ofNat 64 site.start ∧
      Udivti3.numerator (fastPrepared site s base) =
        (SszNative.NatOperand.large pointer words).value := by
  have nonnull : pointer ≠ 0#64 := by
    have positive := owned.operandAt.1
    intro zero
    simp [zero] at positive
  have branch := classified.branch
  simp only [SszNative.NatOperand.pointer, nonnull, ↓reduceIte] at branch
  have small : SszNative.Limbs.sigWords words < 3 := by
    change SszNative.Limbs.sigWords words ≤ 2 at count
    omega
  simp only [SszNative.NatOperand.words, LargeClassified, small, ↓reduceIte] at branch
  have h1 : r (.GPR 1#5) s = pointer := classified.pointer
  have hwords := large_words s pointer words classified.input
  have join := operand_wide_join (.large pointer words) count
  by_cases empty : words.length = 0
  · have nil : words = [] := List.eq_nil_of_length_eq_zero empty
    refine ⟨.zero, ?_, ?_⟩
    · simpa [FastSite.start, empty] using branch
    · simp [fastPrepared, FastSite.setup, block, Op.effect, put, next,
        Udivti3.numerator, Udivti3.join, state_simp_rules,
        SszNative.NatOperand.value, SszNative.NatOperand.words,
        SszNative.Limbs.value, nil]
  · have positive : 0 < words.length := by omega
    simp only [empty, ↓reduceIte] at branch
    have low : r (.GPR 22#5) s = words[0]?.getD 0#64 := branch.1
    by_cases one : words.length < 2
    · have high : words[1]?.getD 0#64 = 0#64 := by
        rw [List.getElem?_eq_none (by omega)]
        rfl
      refine ⟨.low, ?_, ?_⟩
      · simpa [FastSite.start, one] using branch.2
      · have prepared : Udivti3.numerator (fastPrepared .low s base) =
          Udivti3.join (words[0]?.getD 0#64) 0#64 := by
          simp [fastPrepared, FastSite.setup, block, Op.effect, put, next,
            Udivti3.numerator, state_simp_rules, low]
        rw [prepared]
        simpa only [SszNative.NatOperand.words, high] using join
    · have atLeastTwo : 1 < words.length := by omega
      have high : read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0#64 := by
        have h := hwords ⟨1, atLeastTwo⟩
        simpa [List.getElem?_eq_getElem atLeastTwo] using h
      refine ⟨.wide, ?_, ?_⟩
      · simpa [FastSite.start, one] using branch.2
      · have prepared : Udivti3.numerator (fastPrepared .wide s base) =
          Udivti3.join (words[0]?.getD 0#64) (words[1]?.getD 0#64) := by
          simp [fastPrepared, FastSite.setup, block, Op.effect, put, next,
            Udivti3.numerator, state_simp_rules, low, h1, high]
        rw [prepared]
        exact join

end SszArm.NatDivision

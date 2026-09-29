import SszIndicesPowerSemanticDepth
import SszIndicesPaths

set_option autoImplicit false

namespace SszNative.Indices

/-- The source's explicit zero/one fast path agrees with pinned tree depth. -/
theorem leafDepth_refines (count : NatOperand) :
    leafDepth count = Ssz.depthFor count.value := by
  by_cases small : count.value ≤ 1
  · have bound : Ssz.depthFor count.value ≤ 0 :=
      Ssz.depthFor_le_of_le_two_pow (by simpa using small)
    simp only [leafDepth, one_word_le_iff count 1 (by decide), small, ↓reduceIte]
    omega
  · simpa only [leafDepth, one_word_le_iff count 1 (by decide), small, ↓reduceIte]
      using powerDepth_refines count

end SszNative.Indices

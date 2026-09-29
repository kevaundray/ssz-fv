import SszIndicesPowerSemantic
import SszMerkleAccumulatorDepth

set_option autoImplicit false

namespace SszNative.Indices

/-- The native bit-length subtraction computes the least enclosing tree depth.
This also covers zero, without restricting the represented natural's width. -/
theorem powerDepth_refines (count : NatOperand) :
    (bitLength count - if powerOfTwo count then 1 else 0) = Ssz.depthFor count.value := by
  rw [← MerkleAccumulator.capacityDepth_eq_depthFor count]
  simp only [MerkleAccumulator.capacityDepth, bitLength_value,
    Serialize.bitLength, MerkleAccumulator.bitLength, powerOfTwo_log2_iff]

end SszNative.Indices

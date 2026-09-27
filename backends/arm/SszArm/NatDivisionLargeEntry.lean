import SszArm.NatDivisionClassify

namespace SszArm.NatDivision

open SszNative.Limbs

theorem Owned.large_count_bound {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    sigWords words < 2^64 := by
  have physical := owned.operandAt.2.2.1
  have significant := sigWords_le_length words
  omega

/-- The checked allocation path is selected by the original significant count,
while the original pointer, physical length, and physical list remain intact. -/
theorem Classified.large_state {original current : ArmState} {base pointer : BitVec 64}
    {words : List (BitVec 64)} (classified : Classified original current base (.large pointer words))
    (owned : Owned original (.large pointer words)) (count : 2 < sigWords words) :
    read_pc current = base + 168#64 ∧
      r (.GPR 8#5) current = BitVec.ofNat 64 (sigWords words) ∧
      r (.GPR 22#5) current = BitVec.ofNat 64 (sigWords words + 1) ∧
      r (.GPR 23#5) current = BitVec.ofNat 64 (8 * (sigWords words - 1)) ∧
      r (.GPR 24#5) current = 8#64 := by
  have nonnull : pointer ≠ 0#64 := by
    have positive := owned.operandAt.1
    intro zero
    simp [zero] at positive
  have large : ¬ sigWords words < 3 := by omega
  simpa only [SszNative.NatOperand.pointer, SszNative.NatOperand.words,
    nonnull, LargeClassified, large, ↓reduceIte] using classified.branch

end SszArm.NatDivision

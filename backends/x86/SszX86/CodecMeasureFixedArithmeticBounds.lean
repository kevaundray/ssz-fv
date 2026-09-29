import SszX86.BitVectorRoundResources
import SszNatMul

namespace SszX86.CodecMeasureFixed
open SszNative

abbrev add_used_bounds := BitVector.add_used_bounds
abbrev divide8_used_bounds := BitVector.division_used_bounds

/-- Multiplication preserves cursor bounds without a canonical-input assumption
or a signed-capacity restriction. Failed outcomes leave the old cursor intact. -/
theorem mul_used_bounds (left right : NatOperand) (base capacity used : Nat)
    (bound : used ≤ capacity) :
    used ≤ (SszNative.NatMul.run left right base capacity used).used ∧
      (SszNative.NatMul.run left right base capacity used).used ≤ capacity := by
  rcases SszNative.NatMul.run_resources left right base capacity used with
      ⟨result, unchanged, valid⟩ | ⟨reservation, words, positive, reserved, committed⟩
  · rw [unchanged]
    exact ⟨Nat.le_refl _, bound⟩
  · obtain ⟨checks, exactReservation⟩ :=
      (Arena.reserve_eq_some_iff_checks base capacity used words.length positive reservation).1 reserved
    rw [committed]
    simp only [NatArithmetic.committed, exactReservation]
    have lower := Arena.used_le_start base used
    have upper := checks.2.2.2.2.2
    unfold Arena.finish at upper ⊢
    omega

end SszX86.CodecMeasureFixed

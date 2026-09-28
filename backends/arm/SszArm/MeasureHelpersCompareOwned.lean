import SszArm.MeasureHelpersNative
import SszArm.NatDivisionMemory

namespace SszArm.Measure.Helpers

open UintCodec (widthLoad)

def loweringWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16)]

theorem compare_operand_owned (s : ArmState) (operand : SszNative.NatOperand)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (input : operand.At (widthLoad s))
    (owned : NatDivision.OperandOwned (loweringWrites s) operand) :
    NatCompare.Owned s operand.pointer operand.payload := by
  refine ⟨stack, ?_⟩
  cases operand with
  | small word =>
    intro nonzero
    exact False.elim (nonzero rfl)
  | large pointer words =>
    obtain ⟨positive, aligned, physical, limbs⟩ := input
    have countBound : words.length < 2^64 := by omega
    simp only [SszNative.NatOperand.pointer, SszNative.NatOperand.payload,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
    intro nonzero nonempty
    rcases owned with empty | separate
    · have lengthZero : words.length = 0 := by omega
      exact False.elim (nonempty (by simp [lengthZero]))
    · have apart := separate ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [loweringWrites])
      dsimp at apart
      omega

end SszArm.Measure.Helpers

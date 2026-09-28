import SszArm.BitVectorRoundModel

namespace SszArm.BitVector

theorem division_error_model (s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (reason : SszNative.NatArithmetic.Failure)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .error reason) :
    (outcome s length data).result = .error (.arithmetic reason) ∧
      (outcome s length data).rounded = none := by
  simp only [outcome, SszNative.BitVector.run, division]
  exact ⟨True.intro, True.intro⟩

theorem division_zero_model (s : ArmState) (length quotient : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (zero : remainder = 0#64) :
    (outcome s length data).result = SszNative.BitVector.finish length quotient remainder data ∧
      (outcome s length data).rounded = none := by
  have zero' : remainder = (0 : BitVec 64) := zero
  simp only [outcome, SszNative.BitVector.run, division, zero', ↓reduceIte]
  exact ⟨True.intro, True.intro⟩

theorem round_error_model (s : ArmState) (length quotient : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes) (reason : SszNative.NatArithmetic.Failure)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0#64) (addition : (rounding s length quotient).result = .error reason) :
    (outcome s length data).result = .error (.arithmetic reason) := by
  have nonzero' : remainder ≠ (0 : BitVec 64) := nonzero
  dsimp only [rounding] at addition
  simp only [outcome, SszNative.BitVector.run, division, nonzero', ↓reduceIte, addition]

theorem round_success_model (s : ArmState) (length quotient expected : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0#64) (addition : (rounding s length quotient).result = .ok expected) :
    (outcome s length data).result = SszNative.BitVector.finish length expected remainder data := by
  have nonzero' : remainder ≠ (0 : BitVec 64) := nonzero
  dsimp only [rounding] at addition
  simp only [outcome, SszNative.BitVector.run, division, nonzero', ↓reduceIte, addition]

end SszArm.BitVector

import SszArm.BitVectorMemory

namespace SszArm.BitVector

open UintCodec (widthLoad)

/-- A complete copied private Error becomes the outer codec Error after writing
its Value/Error discriminant. Padding bytes are deliberately not observations. -/
theorem arithmetic_error_of_copy (s t : ArmState) (source out : Nat)
    (reason : SszNative.NatArithmetic.Failure)
    (stored : SszNative.NatArithmetic.errorAt (widthLoad s) source reason)
    (tag : widthLoad t out 8 = some 1)
    (copied : ∀ offset bytes, offset + bytes ≤ 68 →
      widthLoad t (out + 8 + offset) bytes = widthLoad s (source + offset) bytes) :
    SszNative.BitVector.failureAt (widthLoad t) out reason := by
  obtain ⟨textPointer, textLength, firstPointer, firstValue, secondPointer,
    secondValue, thirdPointer, thirdValue, status⟩ := stored
  have p0 := copied 0 8 (by decide)
  have p8 := copied 8 8 (by decide)
  have p16 := copied 16 8 (by decide)
  have p24 := copied 24 8 (by decide)
  have p32 := copied 32 8 (by decide)
  have p40 := copied 40 8 (by decide)
  have p48 := copied 48 8 (by decide)
  have p56 := copied 56 8 (by decide)
  have p64 := copied 64 4 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc] at p0 p8 p16 p24 p32 p40 p48 p56 p64
  refine ⟨tag, p0.trans textPointer, p8.trans textLength, ?_, ?_, ?_, p64.trans status⟩
  · exact Or.inl ⟨⟨p16.trans firstPointer, p24.trans firstValue⟩, by decide⟩
  · exact Or.inl ⟨⟨p32.trans secondPointer, p40.trans secondValue⟩, by decide⟩
  · exact Or.inl ⟨⟨p48.trans thirdPointer, p56.trans thirdValue⟩, by decide⟩

/-- Scope errors preserve the precise expected Nat representation, not only its
value. A later copy must separately preserve its referenced allocated limbs. -/
theorem scope_error_of_copy (s t : ArmState) (source out input : Nat)
    (expected : SszNative.NatOperand) (actual : BitVec 64) (data : Ssz.Bytes)
    (size : actual.toNat = data.size)
    (rejected : SszNative.NatNarrow.runExact expected actual = false)
    (stored : SszNative.NatNarrow.ExactResultAt (widthLoad s) source expected actual)
    (expectedAt : expected.At (widthLoad t))
    (tag : widthLoad t out 8 = some 1)
    (copied : ∀ offset bytes, offset + bytes ≤ 68 →
      widthLoad t (out + 8 + offset) bytes = widthLoad s (source + offset) bytes) :
    SszNative.BitVector.ResultAt (widthLoad t) out input data (.error (.scope expected data.size)) := by
  simp only [SszNative.NatNarrow.ExactResultAt, rejected, Bool.false_eq_true, ↓reduceIte] at stored
  obtain ⟨textPointer, textLength, pair, secondPointer, secondValue, thirdPointer,
    thirdValue, status⟩ := stored
  have p0 := copied 0 8 (by decide)
  have p8 := copied 8 8 (by decide)
  have p16 := copied 16 8 (by decide)
  have p24 := copied 24 8 (by decide)
  have p32 := copied 32 8 (by decide)
  have p40 := copied 40 8 (by decide)
  have p48 := copied 48 8 (by decide)
  have p56 := copied 56 8 (by decide)
  have p64 := copied 64 4 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc] at p0 p8 p16 p24 p32 p40 p48 p56 p64
  have expectedPair : SszNative.NatArithmetic.operandAt (widthLoad t) (out + 24) expected := by
    refine ⟨p16.trans pair.1, ?_, expectedAt⟩
    simpa only [Nat.add_assoc] using p24.trans pair.2.1
  refine ⟨⟨tag, p0.trans textPointer, p8.trans textLength, ?_, ?_, ?_, p64.trans status⟩,
    expectedPair⟩
  · exact SszNative.NatMemory.Pair.at (widthLoad t) expected.pointer expected.payload
      expected.value (out + 24) (SszNative.NatOperand.At.pair (widthLoad t) expected expectedAt)
      expectedPair.1 expectedPair.2.1
  · exact Or.inl ⟨⟨p32.trans secondPointer, by simpa only [size] using p40.trans secondValue⟩,
      by rw [← size]; exact actual.isLt⟩
  · exact Or.inl ⟨⟨p48.trans thirdPointer, p56.trans thirdValue⟩, by decide⟩

end SszArm.BitVector

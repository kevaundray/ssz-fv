import SszX86.BitVectorErrorCopy

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def arithmeticErrorImage (reason : NatArithmetic.Failure) (padding : BitVec 32) : ErrorImage :=
  { w0 := 1#64
    w1 := 0#64
    w2 := 0#64
    w3 := 0#64
    w4 := 0#64
    w5 := 0#64
    w6 := 0#64
    w7 := 0#64
    reason := (match reason with
      | .scratchExhausted => 32768#32
      | .badRepresentation => 32770#32)
    padding := padding }

private theorem error_observe (m : DataMem) (out : BitVec 64) (off count : Nat) :
    widthLoad m (out.toNat + off) count = observe m out off count := by
  simp only [widthLoad, observe, width_address]

private theorem error_observe_zero (m : DataMem) (out : BitVec 64) (count : Nat) :
    widthLoad m out.toNat count = observe m out 0 count := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

/-- Private arithmetic errors become outer Result errors, not SSZ failures.
The copied native padding is retained but has no invented semantic value. -/
theorem division_arithmetic_observed (m : DataMem) (out : BitVec 64)
    (reason : NatArithmetic.Failure) (padding : BitVec 32)
    (bound : out.toNat + 80 ≤ 2^64) :
    SszNative.BitVector.failureAt
      (widthLoad (divisionErrorMem m out (arithmeticErrorImage reason padding))) out.toNat reason := by
  cases reason <;>
    refine ⟨?_, ?_, ?_, Or.inl ⟨?_, by decide⟩, Or.inl ⟨?_, by decide⟩,
      Or.inl ⟨?_, by decide⟩, ?_⟩
  all_goals
    simp (disch := first | assumption | omega | decide) only
      [SszNative.NatMemory.smallAt, Nat.add_assoc, Nat.reduceAdd,
        error_observe, error_observe_zero, observe, arithmeticErrorImage, divisionErrorMem,
        load_store_offset_disjoint, load_store_same, Nat.reduceMul]
    decide

end SszX86.BitVector

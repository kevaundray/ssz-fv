import SszArm.MeasureBitVectorOwnership
import SszArm.MeasureUnallocatedPost

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem mismatch_outcome (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat) :
    let call := SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
      (arenaOf s args).used bits.count
    outcome s args (.bitVector cap) (.bits bits) =
      ⟨match call.result with
        | .ok actual => .error (.scope cap actual)
        | .error reason => .error (.arithmetic reason), call.used, [call]⟩ := by
  dsimp only
  cases result : (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
    (arenaOf s args).used bits.count).result <;>
    simp [outcome, SszNative.Serialize.measure, mismatch, SszNative.Serialize.fromWide,
      SszNative.Serialize.bind, SszNative.Serialize.unchanged, result, Except.mapError]

theorem mismatch_calls (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat) :
    (outcome s args (.bitVector cap) (.bits bits)).calls =
      [SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
        (arenaOf s args).used bits.count] := by
  rw [mismatch_outcome s args cap bits mismatch]

theorem mismatch_used (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat) :
    (outcome s args (.bitVector cap) (.bits bits)).used =
      (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
        (arenaOf s args).used bits.count).used := by
  rw [mismatch_outcome s args cap bits mismatch]

theorem mismatch_inline (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat) :
    propagated (outcome s args (.bitVector cap) (.bits bits)) = false := by
  rw [mismatch_outcome s args cap bits mismatch]
  cases result : (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
    (arenaOf s args).used bits.count).result <;> simp [propagated]

theorem small_outcome (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat) (small : bits.count.toNat < 2^64) :
    outcome s args (.bitVector cap) (.bits bits) =
      ⟨.error (.scope cap (.small (bits.count.setWidth 64))), (arenaOf s args).used,
        [SszNative.NatArithmetic.unchanged (arenaOf s args).used
          (.ok (.small (bits.count.setWidth 64)))]⟩ := by
  simp [outcome, SszNative.Serialize.measure, mismatch, SszNative.Serialize.fromWide,
    SszNative.Serialize.bind, SszNative.Serialize.unchanged, SszNative.NatArithmetic.fromWide,
    small, SszNative.NatArithmetic.unchanged, Except.mapError]

theorem operand_owned_subset {larger smaller : List Delimited.Span} (operand : NatOperand)
    (owned : NatDivision.OperandOwned larger operand)
    (subset : ∀ span ∈ smaller, span ∈ larger) : NatDivision.OperandOwned smaller operand := by
  cases operand with
  | small scalar => trivial
  | large pointer words =>
    rcases owned with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (subset span member))

theorem local_error_writes {s : ArmState} {args : Args} {cap : NatOperand} {bits : Packed}
    (low : 288 ≤ args.stack.toNat) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP)
    (mismatch : cap.value ≠ bits.count.toNat) (reason : SszNative.Serialize.Error)
    (failure : (outcome s args (.bitVector cap) (.bits bits)).result = .error reason) :
    Result.errorWrites s = bodyStackWrites args (outcome s args (.bitVector cap) (.bits bits)) ++
      resultWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]
    bv_omega
  simp [Result.errorWrites, bodyStackWrites, resultWrites, resultExtent, failure,
    mismatch_inline s args cap bits mismatch, mismatch_calls s args cap bits mismatch,
    output, position]

end SszArm.Measure.BitVector

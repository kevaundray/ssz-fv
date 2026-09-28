import SszArm.MeasureBitVectorFacts
import SszArm.MeasureBitsAllocConstructor
import SszArm.MeasureHelpersAllocInput
import SszArm.MeasureHelpersAllocation

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem count_pair (wide : BitVec 128) :
    ((wide >>> (64 : Nat)).setWidth 64 ++ wide.setWidth 64) = wide := by
  apply BitVec.eq_of_toNat_eq
  rw [NatToU128.append_toNat]
  bv_omega

theorem alloc_call_eq (s : ArmState) (args : Args) (bits : Packed)
    (arena : r (.GPR 20#5) s = args.arena)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64) :
    Bits.Alloc.outcome .scope s = SszNative.NatArithmetic.fromWide
      (arenaOf s args).base (arenaOf s args).capacity (arenaOf s args).used bits.count := by
  simp only [Bits.Alloc.outcome, Bits.Alloc.addressWord, Bits.Alloc.capacityWord,
    Bits.Alloc.usedWord, Bits.Alloc.wide, Bits.Alloc.Site.highReg, Bits.Alloc.Site.lowReg,
    arena, arenaOf]
  congr 1
  have pair : r (.GPR 9#5) s ++ r (.GPR 8#5) s = bits.count := by
    rw [high, low]
    exact count_pair bits.count
  with_unfolding_all exact pair

theorem alloc_writes_eq (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (arena : r (.GPR 20#5) s = args.arena)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (mismatch : cap.value ≠ bits.count.toNat) :
    Bits.Alloc.writesFor .scope s = allocationWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
  have callEq := alloc_call_eq s args bits arena low high
  have member : Bits.Alloc.outcome .scope s ∈ (outcome s args (.bitVector cap) (.bits bits)).calls := by
    rw [mismatch_calls s args cap bits mismatch, ← callEq]
    simp
  cases allocated : (Bits.Alloc.outcome .scope s).allocation with
  | none =>
    simp [Bits.Alloc.writesFor, allocationWrites, mismatch_calls s args cap bits mismatch,
      ← callEq, allocated]
  | some reservation =>
    have count := callsTwo_measure (arenaOf s args) (.bitVector cap) (.bits bits)
      (Bits.Alloc.outcome .scope s) member reservation allocated
    simp [Bits.Alloc.writesFor, allocationWrites, mismatch_calls s args cap bits mismatch,
      ← callEq, allocated, arena, count]

theorem error_writes_subset_local {s : ArmState} {args : Args} {cap : NatOperand} {bits : Packed}
    (owned : Owned s args (.bitVector cap) (.bits bits))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (mismatch : cap.value ≠ bits.count.toNat) (reason : SszNative.Serialize.Error)
    (failure : (outcome s args (.bitVector cap) (.bits bits)).result = .error reason) :
    ∀ span ∈ Result.errorWrites s, span ∈ localWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
  intro span member
  rw [local_error_writes owned.stackLow output stack mismatch reason failure] at member
  rcases List.mem_append.mp member with lowering | result
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr lowering)))
  · exact List.mem_append.mpr (Or.inr result)

end SszArm.Measure.BitVector

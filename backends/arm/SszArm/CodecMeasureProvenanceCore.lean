import SszArm.CodecStoragePlanOwned
import SszArm.CodecMeasureError
import SszArm.SerializeOwnershipResult
import SszArm.NatAddZeroOwned
import SszCodecMeasureResourcesCore

namespace SszArm.Codec.Measure.Provenance

open SszNative (NatOperand)
open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected)

/-- Fresh arithmetic limbs are confined to the original free suffix, including
when the original cursor is invalid (then a positive reservation cannot pass). -/
theorem add_buffer_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (left right : NatOperand) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (allocation : SszNative.Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).allocation =
      some allocation) :
    NatDivision.OperandOwned writes (.large (BitVec.ofNat 64 allocation.pointer)
      (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).written) := by
  obtain ⟨checks, pointer, _cursor, _length⟩ :=
    SszNative.NatAdd.allocation_geometry left right arena.base arena.capacity arena.used allocation allocated
  have low := SszNative.Arena.used_le_start arena.base arena.used
  have high := checks.2.2.2.2.2
  have positive : 0 < (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).written.length := by
    have count := SszNative.NatAdd.allocation_exact left right arena.base arena.capacity arena.used allocation allocated
    rcases count.2.2 with small | large
    · rw [small.2.2.2.2]
      simp
    · rw [large.2.2.2, SszNative.NatAdd.writtenWords_length]
      omega
  have pointerBound : allocation.pointer < 2^64 := by
    dsimp [SszNative.Arena.finish] at high
    omega
  change Protected writes (BitVec.ofNat 64 allocation.pointer).toNat _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
  apply Serialize.protected_subspan_of_bounds free
  · omega
  · dsimp [SszNative.Arena.finish] at high
    omega

 theorem add_result_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (left right result : NatOperand) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (leftOwned : NatDivision.OperandOwned writes left)
    (rightOwned : NatDivision.OperandOwned writes right)
    (success : (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).result = .ok result) :
    NatDivision.OperandOwned writes result := by
  by_cases leftZero : left.wordCount = 0
  · rw [SszNative.NatAdd.run_zero_left left right arena.base arena.capacity arena.used leftZero] at success
    cases success
    exact SszArm.NatAdd.normalized_owned writes right rightOwned
  · by_cases rightZero : right.wordCount = 0
    · rw [SszNative.NatAdd.run_zero_right left right arena.base arena.capacity arena.used leftZero rightZero] at success
      cases success
      exact SszArm.NatAdd.normalized_owned writes left leftOwned
    · by_cases small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · rw [SszNative.NatAdd.run_one_word left right arena.base arena.capacity arena.used leftZero rightZero small] at success
        exact SszArm.Measure.Helpers.fromWide_result_owned writes arena _ storage free result success
      · cases allocation : (SszNative.NatAdd.run left right arena.base arena.capacity arena.used).allocation with
        | some reservation =>
            have buffer := add_buffer_owned writes arena left right storage free reservation allocation
            have returned := (SszNative.NatAdd.allocation_exact left right arena.base arena.capacity arena.used reservation allocation).2.1
            rw [returned] at success
            cases success
            exact NatDivision.fromWords_owned writes _ _ buffer
        | none =>
            rw [SszNative.NatAdd.run_large left right arena.base arena.capacity arena.used leftZero rightZero small] at success allocation
            split at success
            · rename_i fits
              split at success
              · cases success
              · rename_i reservation reserved
                simp [fits, reserved, SszNative.NatArithmetic.committed] at allocation
            · cases success

end SszArm.Codec.Measure.Provenance

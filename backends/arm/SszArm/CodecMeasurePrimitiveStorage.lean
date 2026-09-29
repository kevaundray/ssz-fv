import SszArm.CodecMeasureContract
import SszArm.CodecStorageProjection

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative (NatOperand)
open SszNative.CodecMeasure (Plan)

/-- A primitive's native empty-child Plan is the recursive storage base case.
Result padding is neither inspected nor required to be initialized. -/
theorem primitive_plan_at (s : ArmState) (address : Nat) (size : NatOperand)
    (physical : Storage.Physical address 40 8)
    (backing : Storage.Backing (fun _ _ => True) size)
    (stored : SszArm.Measure.ResultAt (UintCodec.widthLoad s) address (.ok size)) :
    Storage.PlanAt s address (Plan.leaf size) := by
  rcases stored with ⟨pointer, length, operand, leading, _⟩
  have bound := physical.2.2.1
  change (Storage.Physical address 40 8 ∧ True) ∧
    (address + 8 ≤ 2^64 ∧ True ∧ UintCodec.widthLoad s address 8 = some 8) ∧
    (address + 8 + 8 ≤ 2^64 ∧ True ∧ UintCodec.widthLoad s (address + 8) 8 = some 0) ∧
    (address + 16 + 16 ≤ 2^64 ∧ True ∧ Storage.Backing (fun _ _ => True) size ∧
      SszNative.NatArithmetic.operandAt (UintCodec.widthLoad s) (address + 16) size) ∧
    (address + 32 + 8 ≤ 2^64 ∧ True ∧ UintCodec.widthLoad s (address + 32) 8 = some 0) ∧
    (none = (none : Option SszNative.Arena.Reservation) → ([] : List Plan) = []) ∧
    Storage.Physical 8 0 8 ∧ True
  exact ⟨⟨physical, trivial⟩, ⟨by omega, trivial, pointer⟩, ⟨by omega, trivial, length⟩,
    ⟨by omega, trivial, backing, operand⟩, ⟨by omega, trivial, leading⟩,
    (fun _ => rfl), by decide, trivial⟩

theorem primitive_result_at (s : ArmState) (address : Nat)
    (result : Except SszNative.Serialize.Error NatOperand)
    (physical : Storage.Physical address 40 8)
    (backing : ∀ size, result = .ok size → Storage.Backing (fun _ _ => True) size)
    (stored : SszArm.Measure.ResultAt (UintCodec.widthLoad s) address result) :
    ResultAt s address ((result.map Plan.leaf).mapError SszNative.Codec.Error.primitive) := by
  cases result with
  | error reason => exact stored
  | ok size =>
    exact ⟨primitive_plan_at s address size physical (backing size rfl) stored,
      stored.2.2.2.2⟩

theorem outcome_primitive (s : ArmState) (args : Args)
    (shape : SszNative.Serialize.Desc) (value : SszNative.Codec.Value) :
    outcome s args (.primitive shape) value =
      SszNative.CodecMeasure.primitive shape value (arenaOf s args) := by
  unfold outcome
  rw [SszNative.CodecMeasure.measure]
  rfl

end SszArm.Codec.Measure

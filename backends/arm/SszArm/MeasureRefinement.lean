import SszArm.MeasurePost
import SszArm.MeasureAllocationFacts

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Error)
open UintCodec (widthLoad)

def resultCode : Except Error NatOperand → Nat
  | .ok _ => 0
  | .error reason => errorCode reason

theorem ResultAt.status {observe : Nat → Nat → Option Nat} {address : Nat}
    {result : Except Error NatOperand} (stored : ResultAt observe address result) :
    observe (address + 64) 4 = some (resultCode result) := by
  cases result with
  | ok operand => exact stored.2.2.2.2
  | error reason => exact stored.2.2.2.2.2.2

/-- Status, exact logical result representation, and committed calls all belong
to one postcondition; no independently guessed native error decoding is needed. -/
theorem Post.status {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) :
    widthLoad t ((Args.ofEntry s).result.toNat + 64) 4 =
      some (resultCode (outcome s (Args.ofEntry s) desc value).result) :=
  post.result.status

/-- A successful result is exactly the size of the pinned SSZ encoding, even
when the returned Nat is borrowed, padded, or logically larger than usize. -/
theorem Post.success_encoding {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (physical : value.Physical) (operand : NatOperand)
    (success : (outcome s (Args.ofEntry s) desc value).result = .ok operand) :
    Ssz.serialize desc.erase value.erase = .ok (SszNative.Serialize.emit desc value) ∧
      (SszNative.Serialize.emit desc value).size = operand.value ∧
      SszNative.NatArithmetic.operandAt (widthLoad t) ((Args.ofEntry s).result.toNat + 16) operand := by
  have refinement := SszNative.Serialize.measure_refines desc value
    (arenaOf s (Args.ofEntry s)) physical
  change SszNative.Serialize.Measures (outcome s (Args.ofEntry s) desc value).result _ at refinement
  obtain correct | exhausted := refinement
  · have exactSize : SszNative.Serialize.expectedSize desc value = .ok operand.value := by
      simp only [success, Except.map, SszNative.Serialize.eraseResult] at correct
      exact (Except.ok.inj correct).symm
    obtain ⟨encoding, length⟩ := SszNative.Serialize.expected_encoding desc value
    refine ⟨?_, length operand.value exactSize, post.success_operand operand success⟩
    simpa only [exactSize, Except.map] using encoding
  · rw [success] at exhausted
    cases exhausted

/-- Includes semantic rejection and scratch exhaustion, without assuming any
successful expectedSize result at the machine entry. -/
theorem Post.pinned {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (physical : value.Physical) :
    ∃ result, ResultAt (widthLoad t) (Args.ofEntry s).result.toNat result ∧
      SszNative.Serialize.Measures result ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  simpa only [SszNative.Serialize.expectedSize_eq_pinned] using post.refines physical

theorem resultCode_scratch_iff (result : Except Error NatOperand) :
    resultCode result = 32768 ↔ result = .error (.arithmetic .scratchExhausted) := by
  cases result with
  | ok operand => simp [resultCode]
  | error reason =>
    cases reason with
    | arithmetic failure => cases failure <;> simp [resultCode, errorCode]
    | _ => simp [resultCode, errorCode]

/-- Scratch failure is the exact ordered allocator guard condition of the
accepted measurement model, not an assumption of sufficient scratch. -/
theorem Post.scratch_iff {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) :
    widthLoad t ((Args.ofEntry s).result.toNat + 64) 4 = some 32768 ↔
      SszNative.Serialize.MeasureExhausted desc value (arenaOf s (Args.ofEntry s)) := by
  rw [post.status, Option.some.injEq, resultCode_scratch_iff]
  exact SszNative.Serialize.measure_scratch_iff desc value (arenaOf s (Args.ofEntry s))

end SszArm.Measure

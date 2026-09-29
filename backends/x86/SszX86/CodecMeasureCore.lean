import SszX86.CodecError
import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative UintCodec

/-- Exact live Result<Plan> fields. The shared PlanFields predicate intentionally
does not claim anything about native padding, and the Nat observation retains
borrowed limbs rather than only the mathematical size. -/
def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except SszNative.Codec.Error SszNative.CodecMeasure.Plan → Prop
  | .ok plan => SszNative.CodecMeasure.PlanFields observe out plan ∧
      plan.size.At observe ∧ observe (out + 64) 4 = some 0
  | .error reason => Codec.ErrorAt observe out reason

/-- Exact primitive observations embed into the recursive result type. This
lemma changes only the observation interface, never the executed leaf path. -/
theorem primitive_resultAt (observe : Nat → Nat → Option Nat) (out : Nat)
    (result : Except SszNative.Serialize.Error NatOperand) :
    ResultAt observe out
      ((result.map SszNative.CodecMeasure.Plan.leaf).mapError SszNative.Codec.Error.primitive) ↔
      Measure.ResultAt observe out result := by
  cases result with
  | error reason => exact Codec.errorAt_primitive observe out reason
  | ok size =>
    simp only [Except.map, Except.mapError, ResultAt, Measure.ResultAt, Measure.PlanAt,
      SszNative.CodecMeasure.PlanFields, SszNative.CodecMeasure.Plan.leaf,
      SszNative.CodecMeasure.Plan.size, SszNative.CodecMeasure.Plan.leading,
      SszNative.CodecMeasure.Plan.children, SszNative.CodecMeasure.Plan.childrenPointer,
      SszNative.CodecMeasure.Plan.allocation, List.length_nil,
      NatArithmetic.operandAt, Nat.add_assoc]
    tauto

/-- Only actual initializer writes permit a Plan slot to change. In particular,
reserving an outer Plan array does not initialize its suffix or alignment gap. -/
def EffectWrites (effect : SszNative.CodecMeasure.Effect) (a : BitVec 64) : Prop :=
  match effect with
  | .primitive _ _ _ outcome => Measure.AllocationWrites outcome.calls a
  | .arithmetic _ _ _ outcome =>
      ∃ reservation, outcome.allocation = some reservation ∧
        Codec.InSpan a (BitVec.ofNat 64 reservation.pointer) (8 * outcome.written.length)
  | .reservePlans _ _ _ => False
  | .writePlan address _ _ => Codec.InSpan a (BitVec.ofNat 64 address) 40

def EffectsWrite (effects : List SszNative.CodecMeasure.Effect) (a : BitVec 64) : Prop :=
  ∃ effect ∈ effects, EffectWrites effect a

/-- Result fields and freshly initialized allocation fields extend the original
readonly graph. Uninitialized reserved slots and padding gaps are not added. -/
def ResultFootprint (readonly : Codec.Footprint) (out : BitVec 64)
    (effects : List SszNative.CodecMeasure.Effect) : Codec.Footprint :=
  fun a => readonly a ∨ Codec.InSpan a out 40 ∨ EffectsWrite effects a

/-- Full retained storage accompanies the observable result. Error results do
not assert a fictitious Plan; successful results relate every retained child. -/
def ActiveResultAt (m : DataMem) (r : Codec.Footprint) (out : BitVec 64) :
    Except SszNative.Codec.Error SszNative.CodecMeasure.Plan → Prop
  | .ok plan => Codec.PlanAt m r out plan
  | .error _ => True

/-- Historical limb and initialized Plan writes remain represented after every
later failure. Reservation events alone have no initialization assertion. -/
def EffectsAt (m : DataMem) (r : Codec.Footprint)
    (effects : List SszNative.CodecMeasure.Effect) : Prop :=
  ∀ effect ∈ effects,
    match effect with
    | .primitive _ _ _ outcome => Measure.CallsAt (widthLoad m) outcome.calls
    | .arithmetic _ _ _ outcome =>
        ∀ reservation, outcome.allocation = some reservation →
          NatMemory.wordsAt (widthLoad m) reservation.pointer outcome.written
    | .reservePlans _ _ _ => True
    | .writePlan address _ plan => Codec.PlanAt m r (BitVec.ofNat 64 address) plan

theorem EffectsWrite.append (before after : List SszNative.CodecMeasure.Effect)
    (a : BitVec 64) :
    EffectsWrite (before ++ after) a ↔ EffectsWrite before a ∨ EffectsWrite after a := by
  simp only [EffectsWrite, List.mem_append]
  constructor
  · rintro ⟨effect, member | member, written⟩
    · exact Or.inl ⟨effect, member, written⟩
    · exact Or.inr ⟨effect, member, written⟩
  · rintro (⟨effect, member, written⟩ | ⟨effect, member, written⟩)
    · exact ⟨effect, Or.inl member, written⟩
    · exact ⟨effect, Or.inr member, written⟩

theorem EffectsAt.append (m : DataMem) (r : Codec.Footprint)
    (before after : List SszNative.CodecMeasure.Effect) :
    EffectsAt m r (before ++ after) ↔ EffectsAt m r before ∧ EffectsAt m r after := by
  simp only [EffectsAt, List.forall_mem_append]

end SszX86.CodecMeasure

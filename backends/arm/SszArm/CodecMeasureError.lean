import SszArm.MeasureContract
import SszCodecError

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative (NatOperand)
open SszNative.Codec (Error)

/-- Native Reason discriminants, shared by measure and deserialize. -/
def errorCode : Error → Nat
  | .primitive reason => SszArm.Measure.errorCode reason
  | .scopeTooSmall _ _ => 4
  | .scopeUndivided _ _ => 5
  | .scopeWidthless => 6
  | .firstOffset _ _ => 7
  | .offsetUnordered => 8
  | .offsetPastScope => 9
  | .offsetUnaligned => 10
  | .offsetBelowTable => 11
  | .truncated => 12
  | .notABit _ => 13
  | .paddingBits => 15
  | .emptyEncoding => 16
  | .noDelimiter => 17
  | .trailingZeros => 18
  | .noSelector => 19
  | .unknownSelector _ => 20
  | .offsetOverflow _ => 21

def errorOperands : Error → NatOperand × NatOperand
  | .primitive reason => SszArm.Measure.errorOperands reason
  | .scopeTooSmall expected actual | .scopeUndivided expected actual
  | .firstOffset expected actual => (expected, actual)
  | .offsetOverflow size | .unknownSelector size | .notABit size => (size, .small 0)
  | _ => (.small 0, .small 0)

/-- The Result error payload uses an empty text slice at 0/8, two active Nat
arguments at 16/32, zero third argument at 48, and Reason at 64. Nat arguments
include their borrowed limb interpretation; padding at 68..72 is not asserted. -/
def ErrorAt (observe : Nat → Nat → Option Nat) (address : Nat) (reason : Error) : Prop :=
  observe address 8 = some 1 ∧ observe (address + 8) 8 = some 0 ∧
  SszNative.NatArithmetic.operandAt observe (address + 16) (errorOperands reason).1 ∧
  SszNative.NatArithmetic.operandAt observe (address + 32) (errorOperands reason).2 ∧
  observe (address + 48) 8 = some 0 ∧ observe (address + 56) 8 = some 0 ∧
  observe (address + 64) 4 = some (errorCode reason)

@[simp] theorem ErrorAt_primitive (observe : Nat → Nat → Option Nat)
    (address : Nat) (reason : SszNative.Serialize.Error) :
    ErrorAt observe address (.primitive reason) ↔
      SszArm.Measure.ErrorAt observe address reason := Iff.rfl

theorem ErrorAt.operands {observe : Nat → Nat → Option Nat}
    {address : Nat} {reason : Error} (stored : ErrorAt observe address reason) :
    (errorOperands reason).1.At observe ∧ (errorOperands reason).2.At observe :=
  ⟨stored.2.2.1.2.2, stored.2.2.2.1.2.2⟩

/-- A physical copy transports only the active record fields. Borrowed limb
preservation is required separately, so copying an error cannot manufacture
ownership or initialized Nat backing. -/
theorem ErrorAt.copy {before after : Nat → Nat → Option Nat}
    {source target : Nat} {reason : Error} (stored : ErrorAt before source reason)
    (copied : ∀ offset width : Nat, offset + width ≤ 68 →
      after (target + offset) width = before (source + offset) width)
    (left : (errorOperands reason).1.At after)
    (right : (errorOperands reason).2.At after) : ErrorAt after target reason := by
  rcases stored with ⟨text, textLength, first, second, thirdPointer, thirdPayload, code⟩
  rcases first with ⟨firstPointer, firstPayload, _⟩
  rcases second with ⟨secondPointer, secondPayload, _⟩
  refine ⟨?_, ?_, ⟨?_, ?_, left⟩, ⟨?_, ?_, right⟩, ?_, ?_, ?_⟩
  · simpa using (copied 0 8 (by decide)).trans (by simpa using text)
  · exact (copied 8 8 (by decide)).trans textLength
  · exact (copied 16 8 (by decide)).trans firstPointer
  · simpa only [Nat.add_assoc] using (copied 24 8 (by decide)).trans
      (by simpa only [Nat.add_assoc] using firstPayload)
  · exact (copied 32 8 (by decide)).trans secondPointer
  · simpa only [Nat.add_assoc] using (copied 40 8 (by decide)).trans
      (by simpa only [Nat.add_assoc] using secondPayload)
  · exact (copied 48 8 (by decide)).trans thirdPointer
  · exact (copied 56 8 (by decide)).trans thirdPayload
  · exact (copied 64 4 (by decide)).trans code

end SszArm.Codec.Measure

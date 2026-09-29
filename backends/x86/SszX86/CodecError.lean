import SszX86.MeasureCore
import SszCodecError

namespace SszX86.Codec
open SszNative
open SszNative.Codec (Error)

/-- Native `Reason` discriminants, including resource failures, not an SSZ
validation classification. All codec errors carry an empty text slice and at
most two original Nat operands. -/
def errorCode : Error → Nat
  | .primitive .wrongType => 1
  | .primitive (.limit _ _) => 2
  | .primitive (.scope _ _) => 3
  | .primitive (.arithmetic .scratchExhausted) => 32768
  | .primitive .outputTooSmall => 32769
  | .primitive (.arithmetic .badRepresentation) => 32770
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

def errorFirst : Error → NatOperand
  | .primitive (.limit expected _) | .primitive (.scope expected _)
  | .scopeTooSmall expected _ | .scopeUndivided expected _
  | .firstOffset expected _ => expected
  | .unknownSelector value | .offsetOverflow value | .notABit value => value
  | _ => .small 0

def errorSecond : Error → NatOperand
  | .primitive (.limit _ actual) | .primitive (.scope _ actual)
  | .scopeTooSmall _ actual | .scopeUndivided _ actual
  | .firstOffset _ actual => actual
  | _ => .small 0

/-- The 68 meaningful bytes of the native Error payload. The last four bytes
of the 72-byte Rust object remain arbitrary padding. Operand observations
include their borrowed limbs, including empty or redundantly padded Large Nats. -/
def ErrorAt (observe : Nat → Nat → Option Nat) (out : Nat) (reason : Error) : Prop :=
  Measure.SemanticErrorAt observe out (errorCode reason)
    (errorFirst reason) (errorSecond reason)

/-- `Result<Value, Error>` has a separate outer discriminant; the Plan and usize
results use the error reason's zero niche instead. -/
def DecodeErrorAt (observe : Nat → Nat → Option Nat) (out : Nat) (reason : Error) : Prop :=
  observe out 8 = some 1 ∧ ErrorAt observe (out + 8) reason

def ErrorBorrows (reason : Error) (address : BitVec 64) : Prop :=
  Emit.NatBorrowed (errorFirst reason) address ∨
    Emit.NatBorrowed (errorSecond reason) address

theorem errorCode_ne_zero (reason : Error) : errorCode reason ≠ 0 := by
  cases reason with
  | primitive reason =>
    cases reason with
    | arithmetic failure => cases failure <;> decide
    | wrongType | scope _ _ | limit _ _ | outputTooSmall => simp only [errorCode]; decide
  | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
  | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
  | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
  | emptyEncoding | noDelimiter | trailingZeros | noSelector => simp only [errorCode]; decide

theorem ErrorAt.tag {observe : Nat → Nat → Option Nat} {out : Nat} {reason : Error}
    (stored : ErrorAt observe out reason) :
    observe (out + 64) 4 = some (errorCode reason) :=
  stored.2.2.2.2.2.2

/-- Reusing a leaf contract retains exactly its original arithmetic and semantic
error payload rather than projecting only an error name. -/
theorem errorAt_primitive (observe : Nat → Nat → Option Nat) (out : Nat)
    (reason : SszNative.Serialize.Error) :
    ErrorAt observe out (.primitive reason) ↔ Measure.ErrorAt observe out reason := by
  cases reason with
  | wrongType | scope _ _ | limit _ _ | outputTooSmall => rfl
  | arithmetic failure =>
    cases failure <;>
      simp [ErrorAt, errorCode, errorFirst, errorSecond, Measure.ErrorAt,
        Measure.SemanticErrorAt, NatArithmetic.errorAt, NatArithmetic.operandAt,
        NatOperand.pointer, NatOperand.payload, NatOperand.At, Nat.add_assoc,
        and_assoc]

end SszX86.Codec

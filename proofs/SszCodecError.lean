import SszCodecTypes

set_option autoImplicit false

namespace SszNative.Codec

/-- Recursive codec errors retain original native operands. Primitive calls use
this boundary adapter without modifying their accepted error representation. -/
inductive Error where
  | primitive (reason : Serialize.Error)
  | offsetOverflow (size : NatOperand)
  | unknownSelector (selector : NatOperand)
  | scopeTooSmall (expected actual : NatOperand)
  | scopeUndivided (scope width : NatOperand)
  | scopeWidthless
  | firstOffset (expected actual : NatOperand)
  | offsetUnordered
  | offsetPastScope
  | offsetUnaligned
  | offsetBelowTable
  | truncated
  | notABit (value : NatOperand)
  | paddingBits
  | emptyEncoding
  | noDelimiter
  | trailingZeros
  | noSelector

def eraseResult {α : Type} : Except Error α → Except Serialize.Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error (.primitive reason) => Serialize.eraseResult (.error reason)
  | .error (.offsetOverflow size) => .ok (.error (.offsetOverflow size.value))
  | .error (.unknownSelector selector) => .ok (.error (.unknownSelector selector.value))
  | .error (.scopeTooSmall expected actual) =>
      .ok (.error (.scopeTooSmall expected.value actual.value))
  | .error (.scopeUndivided scope width) =>
      .ok (.error (.scopeUndivided scope.value width.value))
  | .error .scopeWidthless => .ok (.error .scopeWidthless)
  | .error (.firstOffset expected actual) =>
      .ok (.error (.firstOffset expected.value actual.value))
  | .error .offsetUnordered => .ok (.error .offsetUnordered)
  | .error .offsetPastScope => .ok (.error .offsetPastScope)
  | .error .offsetUnaligned => .ok (.error .offsetUnaligned)
  | .error .offsetBelowTable => .ok (.error .offsetBelowTable)
  | .error .truncated => .ok (.error .truncated)
  | .error (.notABit value) => .ok (.error (.notABit value.value))
  | .error .paddingBits => .ok (.error .paddingBits)
  | .error .emptyEncoding => .ok (.error .emptyEncoding)
  | .error .noDelimiter => .ok (.error .noDelimiter)
  | .error .trailingZeros => .ok (.error .trailingZeros)
  | .error .noSelector => .ok (.error .noSelector)

theorem eraseResult_primitive {α : Type} (result : Except Serialize.Error α) :
    eraseResult (result.mapError Error.primitive) = Serialize.eraseResult result := by
  cases result <;> rfl

theorem eraseResult_map {α β : Type} (result : Except Error α) (f : α → β) :
    eraseResult (result.map f) = (eraseResult result).map (fun result => result.map f) := by
  cases result with
  | ok value => rfl
  | error reason =>
    cases reason with
    | primitive reason => cases reason <;> rfl
    | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _
    | scopeUndivided _ _ | scopeWidthless | firstOffset _ _
    | offsetUnordered | offsetPastScope | offsetUnaligned | offsetBelowTable
    | truncated | notABit _ | paddingBits | emptyEncoding | noDelimiter
    | trailingZeros | noSelector => rfl

end SszNative.Codec

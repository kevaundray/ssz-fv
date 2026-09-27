import SszNatArithmetic

set_option autoImplicit false

namespace SszNative.NatArithmetic

/-- The private arithmetic Result niche layout, not Result<Value, Error>.
The error's empty text pointer is one; its length and three Nat arguments are zero. -/
def errorAt (observe : Nat → Nat → Option Nat) (out : Nat) (failure : Failure) : Prop :=
  observe out 8 = some 1 ∧ observe (out + 8) 8 = some 0 ∧
  observe (out + 16) 8 = some 0 ∧ observe (out + 24) 8 = some 0 ∧
  observe (out + 32) 8 = some 0 ∧ observe (out + 40) 8 = some 0 ∧
  observe (out + 48) 8 = some 0 ∧ observe (out + 56) 8 = some 0 ∧
  observe (out + 64) 4 = some (match failure with
    | .scratchExhausted => 32768
    | .badRepresentation => 32770)

/-- Preserve the algorithm's exact representation, including its borrowed pointer. -/
def operandAt (observe : Nat → Nat → Option Nat) (out : Nat)
    (operand : NatOperand) : Prop :=
  observe out 8 = some operand.pointer.toNat ∧
  observe (out + 8) 8 = some operand.payload.toNat ∧ operand.At observe

def AddResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except Failure NatOperand → Prop
  | .ok operand => operandAt observe out operand ∧ observe (out + 64) 4 = some 0
  | .error failure => errorAt observe out failure

def DivisionResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except Failure (NatOperand × BitVec 64) → Prop
  | .ok (operand, remainder) => operandAt observe out operand ∧
      observe (out + 16) 8 = some remainder.toNat ∧ observe (out + 64) 4 = some 0
  | .error failure => errorAt observe out failure

theorem operandAt.pair (observe : Nat → Nat → Option Nat) (out : Nat)
    (operand : NatOperand) (stored : operandAt observe out operand) :
    NatMemory.Pair observe operand.pointer operand.payload operand.value :=
  NatOperand.At.pair observe operand stored.2.2

end SszNative.NatArithmetic

import SszIndicesCore

set_option autoImplicit false

namespace SszNative.Indices

def wordPowerOfTwo (value : BitVec 64) : Bool :=
  value != 0 && (value &&& (value - 1)) == 0

/-- The native scan carries only the flag that a nonzero limb was already seen. -/
def powerScan (index : NatOperand) : Nat → Nat → Bool → Bool
  | _, 0, seen => seen
  | position, remaining + 1, seen =>
      let value := word index position
      if value == 0 then powerScan index (position + 1) remaining seen
      else if seen || !wordPowerOfTwo value then false
      else powerScan index (position + 1) remaining true

def powerOfTwo (index : NatOperand) : Bool :=
  powerScan index 0 index.wordCount false

/-- No logical-width restriction: the conversion inspects significant limbs. -/
def packingShift (width : NatOperand) : Option Nat :=
  if width.wordCount ≤ 1 then
    let bytes := word width 0
    if bytes.toNat ≤ 32 ∧ wordPowerOfTwo bytes = true then
      some (5 - bytes.toNat.log2)
    else none
  else none

end SszNative.Indices

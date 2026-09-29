import SszIndicesArithmetic

set_option autoImplicit false

namespace SszNative.Indices

def alternatingWord : BitVec 64 := 0x5555555555555555

def thresholdWord (bits position : Nat) : BitVec 64 :=
  alternatingWord &&& rangeWord position 0 bits

/-- Compare the borrowed limbs from most significant to least significant. -/
def thresholdCompareWords (chunk : NatOperand) (bits : Nat) : Nat → Ordering
  | 0 => .eq
  | count + 1 =>
      match compare (word chunk count).toNat (thresholdWord bits count).toNat with
      | .eq => thresholdCompareWords chunk bits count
      | order => order

def thresholdCompare (chunk : NatOperand) (bits words : Nat) : Ordering :=
  match compare (bitLength chunk) bits with
  | .eq => thresholdCompareWords chunk bits words
  | order => order

def progressiveDepth (chunk : NatOperand) (thresholdWords : Nat) : Nat :=
  let initial := depth chunk / 2 * 2
  if thresholdCompare chunk (initial + 1) thresholdWords = .lt then initial else initial + 2

/-- The pair of overflowing_sub calls, followed by the two disjoint spine masks.
Borrow is based on the subtraction, not on the masked output word. -/
def progressiveStep (chunk : NatOperand) (subtreeDepth position : Nat) (borrow : Bool) :
    BitVec 64 × Bool :=
  let source := word chunk position
  let offset := thresholdWord subtreeDepth position
  let difference := source - offset
  let first := decide (source.toNat < offset.toNat)
  let incoming : BitVec 64 := if borrow then 1 else 0
  let remainder := difference - incoming
  let second := decide (difference.toNat < incoming.toNat)
  let level := subtreeDepth / 2
  let leading := subtreeDepth + level + 2
  (remainder ||| rangeWord position (subtreeDepth + 1) (subtreeDepth + level + 1) |||
    rangeWord position leading (leading + 1), first || second)

def progressiveChunkIndex (chunk : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  let initial := depth chunk / 2 * 2
  match wordCount (initial + 1) with
  | .error reason => unchanged used (.error reason)
  | .ok thresholdWords =>
      let subtreeDepth := progressiveDepth chunk thresholdWords
      let level := subtreeDepth / 2
      if subtreeDepth + level < 2 ^ 128 ∧ subtreeDepth + level + 2 < 2 ^ 128 then
        let leading := subtreeDepth + level + 2
        if leading + 1 < 2 ^ 128 then
          match wordCount (leading + 1) with
          | .error reason => unchanged used (.error reason)
          | .ok words => makeNatState words base capacity used false (progressiveStep chunk subtreeDepth)
        else unchanged used (.error scratch)
      else unchanged used (.error scratch)

end SszNative.Indices

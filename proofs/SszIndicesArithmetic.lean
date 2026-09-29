import SszIndicesArithmeticPower
import SszNatShift

set_option autoImplicit false

namespace SszNative.Indices

/-- Stateful ascending initialization models FnMut without recomputing prefixes. -/
def fillWords {σ : Type} (fill : Nat → σ → BitVec 64 × σ) :
    Nat → Nat → σ → List (BitVec 64) × σ
  | _, 0, state => ([], state)
  | position, remaining + 1, state =>
      let next := fill position state
      let rest := fillWords fill (position + 1) remaining next.2
      (next.1 :: rest.1, rest.2)

/-- Reservation precedes every initializer. Unlike Nat::from_words, Large is
retained even when its final limb is zero. The arithmetic event exposes every
written limb and the exact committed cursor. -/
def makeNatState {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) : Outcome NatOperand :=
  match words with
  | 0 => unchanged used (.ok (.small 0))
  | 1 => unchanged used (.ok (.small (fill 0 state).1))
  | count + 2 =>
      match Arena.reserve base capacity used (count + 2) with
      | none => arithmetic used (NatArithmetic.unchanged used (.error .scratchExhausted))
      | some reservation =>
          let written := (fillWords fill 0 (count + 2) state).1
          arithmetic used ⟨.ok (.large (BitVec.ofNat 64 reservation.pointer) written),
            reservation.used, some reservation, written⟩

def makeNat (words base capacity used : Nat) (fill : Nat → BitVec 64) : Outcome NatOperand :=
  makeNatState words base capacity used () (fun position _ => (fill position, ()))

def shiftXor (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) : Outcome NatOperand :=
  match wordCount (bitLength index - shift) with
  | .error reason => unchanged used (.error reason)
  | .ok count => makeNat (max count (if flip then 1 else 0)) base capacity used
      (fun i => shiftedWord index shift i ^^^ (if flip && i == 0 then 1 else 0))

def belowCount (index : NatOperand) (bits : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      if word index count &&& rangeWord count 0 bits == 0 then belowCount index bits count
      else count + 1

def below (index : NatOperand) (bits base capacity used : Nat) : Outcome NatOperand :=
  if bits ≥ bitLength index then unchanged used (.ok index) else
    match wordCount bits with
    | .error reason => unchanged used (.error reason)
    | .ok count => makeNat (belowCount index bits count) base capacity used
        (fun i => word index i &&& rangeWord i 0 bits)

def sibling (index : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  shiftXor index 0 true base capacity used

def parent (index : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  arithmetic used (NatShift.shr index 1 base capacity used)

def child (index : NatOperand) (right : Bool) (base capacity used : Nat) : Outcome NatOperand :=
  if index.wordCount = 0 then unchanged used (.ok (.small (if right then 1 else 0)))
  else if bitLength index + 1 < 2 ^ 128 then
    match wordCount (bitLength index + 1) with
    | .error reason => unchanged used (.error reason)
    | .ok count => makeNat count base capacity used (fun i =>
        (word index i <<< 1) |||
          (if i = 0 then (if right then 1#64 else 0#64) else word index (i - 1) >>> 63))
  else unchanged used (.error scratch)

def concatWord (outer inner : NatOperand) (innerDepth position : Nat) : BitVec 64 :=
  let offset := innerDepth / 64
  let bits := innerDepth % 64
  let upper := if offset ≤ position then
      let j := position - offset
      let low := word outer j <<< bits
      if bits ≠ 0 ∧ j ≠ 0 then low ||| (word outer (j - 1) >>> (64 - bits)) else low
    else 0
  upper ||| (word inner position &&& rangeWord position 0 innerDepth)

def concat (outer inner : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  match checkedDepth outer with
  | .error reason => unchanged used (.error reason)
  | .ok _ =>
      match checkedDepth inner with
      | .error reason => unchanged used (.error reason)
      | .ok innerDepth =>
          if innerDepth = 0 then unchanged used (.ok outer)
          else if outer.wordCount ≤ 1 ∧ word outer 0 = 1 then unchanged used (.ok inner)
          else if bitLength outer + innerDepth < 2 ^ 128 then
            match wordCount (bitLength outer + innerDepth) with
            | .error reason => unchanged used (.error reason)
            | .ok count =>
                if innerDepth / 64 < 2 ^ 64 then
                  makeNat count base capacity used (concatWord outer inner innerDepth)
                else unchanged used (.error scratch)
          else unchanged used (.error scratch)

def rebase (index : NatOperand) (bits base capacity used : Nat) : Outcome NatOperand :=
  if bits + 1 < 2 ^ 128 then
    match wordCount (bits + 1) with
    | .error reason => unchanged used (.error reason)
    | .ok count => makeNat count base capacity used (fun i =>
        (word index i &&& rangeWord i 0 bits) ||| rangeWord i bits (bits + 1))
  else unchanged used (.error scratch)

def nextPow2 (count : NatOperand) (base capacity used : Nat) : Outcome NatOperand :=
  if count.wordCount ≤ 1 ∧ (word count 0).toNat ≤ 1 then unchanged used (.ok (.small 1))
  else if powerOfTwo count then unchanged used (.ok count)
  else arithmetic used (NatShift.shl (.small 1) (bitLength count) base capacity used)

/-- One overflowing_add, with its carry threaded into the next initializer. -/
def ceilStep (value : NatOperand) (shift position : Nat) (carry : Bool) : BitVec 64 × Bool :=
  let source := shiftedWord value shift position
  let increment : BitVec 64 := if carry then 1 else 0
  (source + increment, decide (2 ^ 64 ≤ source.toNat + increment.toNat))

def ceilShift (value : NatOperand) (shift base capacity used : Nat) : Outcome NatOperand :=
  if word value 0 &&& lowMask shift == 0 then
    arithmetic used (NatShift.shr value shift base capacity used)
  else
    match wordCount (bitLength value - shift) with
    | .error reason => unchanged used (.error reason)
    | .ok 0 => unchanged used (.ok (.small 1))
    | .ok (count + 1) =>
        if allWords (fun i => shiftedWord value shift i == -1) (count + 1) then
          if count + 2 < 2 ^ 64 then
            makeNatState (count + 2) base capacity used true (ceilStep value shift)
          else unchanged used (.error scratch)
        else makeNatState (count + 1) base capacity used true (ceilStep value shift)

end SszNative.Indices

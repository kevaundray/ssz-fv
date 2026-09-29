import SszIndicesCore

set_option autoImplicit false

namespace SszNative.Indices

/-- The borrowed width is returned unchanged, including zero and noncanonical limbs. -/
def itemLength : Codec.Desc → NatOperand
  | .primitive .bool => .small 1
  | .primitive (.uint width) => width
  | _ => .small 32

/-- A physical ordinal conversion, not a bound on logical declaration metadata. -/
def ordinalToUsize (ordinal : NatOperand) : Option Nat :=
  if ordinal.wordCount ≤ 1 then some (word ordinal 0).toNat else none

def positionCount : Codec.Desc → Except Error (Option NatOperand)
  | .progressiveList _ _ | .primitive (.progressiveBitList _) => .ok none
  | .vector _ count | .list _ count
  | .primitive (.byteVector count) | .primitive (.byteList count)
  | .primitive (.bitVector count) | .primitive (.bitList count) => .ok (some count)
  | _ => .error .notSteppable

def fieldType (fields : List (String × Codec.Desc)) (ordinal : NatOperand) :
    Except Error Codec.Desc :=
  match ordinalToUsize ordinal with
  | none => .error (.noSuchField ordinal)
  | some position =>
      match fields[position]? with
      | none => .error (.noSuchField ordinal)
      | some field => .ok field.2

def elementType : Codec.Desc → PathStep → Except Error Codec.Desc
  | .container fields, .position ordinal
  | .progressiveContainer _ fields, .position ordinal => fieldType fields ordinal
  | .primitive (.bitVector _), _ | .primitive (.bitList _), _
  | .primitive (.progressiveBitList _), _ => .ok (.primitive .bool)
  | .primitive (.byteVector _), _ | .primitive (.byteList _), _ =>
      .ok (.primitive (.uint (.small 1)))
  | .vector element _, _ | .list element _, _ | .progressiveList element _, _ =>
      .ok element
  | _, _ => .error .notSteppable

/-- Source enumeration retains the physical position while decrementing only on
present bits. No allocation is performed by the search itself. -/
def activeOrdinal : List Bool → Nat → Nat → Option Nat
  | [], _, _ => none
  | false :: rest, remaining, position => activeOrdinal rest remaining (position + 1)
  | true :: _, 0, position => some position
  | true :: rest, remaining + 1, position => activeOrdinal rest remaining (position + 1)

def activePosition (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) : Outcome (Option NatOperand) :=
  match ordinalToUsize ordinal with
  | none => unchanged used (.ok none)
  | some remaining =>
      match activeOrdinal active remaining 0 with
      | none => unchanged used (.ok none)
      | some position =>
          bind (arithmetic used (NatArithmetic.fromWide base capacity used
            (BitVec.ofNat 128 position))) fun result used =>
              unchanged used (.ok (some result))

def layoutPosition (active : List Bool) (ordinal : NatOperand)
    (base capacity used : Nat) : Outcome NatOperand :=
  bind (activePosition active ordinal base capacity used) fun result used =>
    unchanged used (match result with
      | none => .error (.noSuchField ordinal)
      | some position => .ok position)

def mixesIn : Codec.Desc → PathStep → Bool
  | .list _ _, .length | .primitive (.byteList _), .length
  | .primitive (.bitList _), .length | .progressiveList _ _, .length
  | .primitive (.progressiveBitList _), .length => true
  | .progressiveContainer _ _, .activeFields => true
  | .compatibleUnion _, .selector => true
  | _, _ => false

/-- Ordered first-match selection compares values, not operand tags or pointers.
Duplicate selectors and invalid option declarations are deliberately retained. -/
def unionOption : List (NatOperand × Codec.Desc) → NatOperand → Option Codec.Desc
  | [], _ => none
  | (selector, child) :: rest, ordinal =>
      if Limbs.nativeCmp selector.words ordinal.words = .eq then some child
      else unionOption rest ordinal

end SszNative.Indices

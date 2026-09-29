import SszIndicesDescriptor
import SszIndicesArithmetic
import SszIndicesArithmeticPower
import SszIndicesProgressive
import SszNatShift
import SszNatMul
import SszNatDivision

set_option autoImplicit false

namespace SszNative.Indices

/-- Source chunk-count dispatch. The fallback product is allocated before the
ceiling shift; no mathematical ceilDiv implementation replaces that order. -/
def chunkCount (shape : Codec.Desc) (base capacity used : Nat) : Outcome NatOperand :=
  match shape with
  | .primitive .bool | .primitive (.uint _) | .compatibleUnion _ =>
      unchanged used (.ok (.small 1))
  | .primitive (.bitVector count) | .primitive (.bitList count) =>
      ceilShift count 8 base capacity used
  | .primitive (.byteVector count) | .primitive (.byteList count) =>
      ceilShift count 5 base capacity used
  | .vector element count | .list element count =>
      let width := itemLength element
      match packingShift width with
      | some shift => ceilShift count shift base capacity used
      | none =>
          bind (arithmetic used (NatMul.run count width base capacity used))
            fun product used => ceilShift product 5 base capacity used
  | .container fields =>
      arithmetic used (NatArithmetic.fromWide base capacity used
        (BitVec.ofNat 128 fields.length))
  | _ => unchanged used (.error .noChunkCount)

/-- Mul, division, and stop addition are three distinct attempts. Failure in a
later attempt retains earlier allocations and successful intermediate values. -/
def unpackedPosition (position width : NatOperand) (base capacity used : Nat) :
    Outcome ChunkPosition :=
  bind (arithmetic used (NatMul.run position width base capacity used)) fun product used =>
    bind (divide used (NatDivision.run product 32 base capacity used)) fun divided used =>
      let start := NatOperand.small divided.2
      bind (arithmetic used (NatAdd.run start width base capacity used)) fun stop used =>
        unchanged used (.ok ⟨divided.1, start, stop⟩)

def sequencePosition (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) : Outcome ChunkPosition :=
  match shape with
  | .primitive (.bitVector _) | .primitive (.bitList _)
  | .primitive (.progressiveBitList _) =>
      bind (arithmetic used (NatShift.shr position 8 base capacity used)) fun chunk used =>
        unchanged used (.ok ⟨chunk, .small 0, .small 0⟩)
  | _ =>
      match packingShift width with
      | some shift =>
          let start := (word position 0 &&& lowMask shift) <<< (5 - shift)
          bind (arithmetic used (NatShift.shr position shift base capacity used))
            fun chunk used => unchanged used
              (.ok ⟨chunk, .small start, .small (start + (1 <<< (5 - shift)))⟩)
      | none => unpackedPosition position width base capacity used

/-- Element lookup is first even for a non-position step. For bounded sequences,
the logical bound is checked before shifts, multiplication, or division. -/
def chunkPosition (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) : Outcome ChunkPosition :=
  bind (unchanged used (elementType shape step)) fun element used =>
    let width := itemLength element
    match shape, step with
    | .progressiveContainer active _, .position ordinal =>
        bind (layoutPosition active ordinal base capacity used) fun position used =>
          unchanged used (.ok ⟨position, .small 0, width⟩)
    | .container _, .position ordinal => unchanged used (.ok ⟨ordinal, .small 0, width⟩)
    | _, .position position =>
        bind (unchanged used (positionCount shape)) fun count used =>
          if count.any (fun count => decide (Limbs.nativeCmp position.words count.words ≠ .lt)) then
            unchanged used (.error (.noSuchPosition position))
          else sequencePosition shape position width base capacity used
    | _, _ => unchanged used (.error .notSteppable)

def leafDepth (count : NatOperand) : Nat :=
  if count.wordCount ≤ 1 ∧ (word count 0).toNat ≤ 1 then 0
  else bitLength count - if powerOfTwo count then 1 else 0

def isBoundedList : Codec.Desc → Bool
  | .list _ _ | .primitive (.byteList _) | .primitive (.bitList _) => true
  | _ => false

def resolvePosition (shape : Codec.Desc) (ordinal : NatOperand)
    (base capacity used : Nat) : Outcome (NatOperand × Option Codec.Desc) :=
  let step := PathStep.position ordinal
  match shape with
  | .compatibleUnion variants =>
      unchanged used (match unionOption variants ordinal with
        | none => .error (.noSuchOption ordinal)
        | some child => .ok (.small 2, some child))
  | .progressiveContainer _ _ | .progressiveList _ _
  | .primitive (.progressiveBitList _) =>
      bind (chunkPosition shape step base capacity used) fun placed used =>
        bind (progressiveChunkIndex placed.chunk base capacity used) fun index used =>
          unchanged used ((elementType shape step).map (fun child => (index, some child)))
  | _ =>
      bind (chunkPosition shape step base capacity used) fun placed used =>
        bind (chunkCount shape base capacity used) fun count used =>
          bind (rebase placed.chunk
            (leafDepth count + if isBoundedList shape then 1 else 0) base capacity used)
            fun index used =>
              unchanged used ((elementType shape step).map (fun child => (index, some child)))

def resolveStep (shape : Codec.Desc) (step : PathStep)
    (base capacity used : Nat) : Outcome (NatOperand × Option Codec.Desc) :=
  match shape with
  | .primitive .bool | .primitive (.uint _) => unchanged used (.error .noParts)
  | _ =>
      match step with
      | .position ordinal => resolvePosition shape ordinal base capacity used
      | .length | .activeFields | .selector =>
          if mixesIn shape step then unchanged used (.ok (.small 3, none))
          else unchanged used (.error .noMixin)

/-- Recursion is structural in the supplied path, not a host depth/fuel bound.
Relative indices are computed on descent; concatenation allocates on unwind. -/
def generalizedIndex (shape : Codec.Desc) (path : List PathStep)
    (base capacity used : Nat) : Outcome NatOperand :=
  match path with
  | [] => unchanged used (.ok (.small 1))
  | step :: rest =>
      bind (resolveStep shape step base capacity used) fun resolved used =>
        match resolved.2 with
        | none =>
            if rest.isEmpty then unchanged used (.ok resolved.1)
            else unchanged used (.error .noPartsMixin)
        | some child =>
            bind (generalizedIndex child rest base capacity used) fun inner used =>
              concat resolved.1 inner base capacity used

end SszNative.Indices

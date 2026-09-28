import SszArm.DispatchEntry
import SszArm.BitVectorProofs

namespace SszArm.Dispatch.BitVector

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- The original private ABI passes the arena descriptor in X4. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState := NatDivision.arenaOf s

def outcome (s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes) :
    SszNative.BitVector.Outcome := SszNative.BitVector.run length data (arenaOf s)

/-- Body and nested-helper writable bytes, expressed at the original SP. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 80), ((r (.GPR 31#5) s).toNat - 448, 352)]

def savedSpan (s : ArmState) : Span := ((r (.GPR 31#5) s).toNat - 96, 96)

def bodyWrites (s : ArmState) (result : SszNative.BitVector.Outcome) : List Span :=
  localWrites s ++
    (if result.writes = [] then [] else [((r (.GPR 4#5) s).toNat + 16, 8)]) ++
    result.writes

/-- The six save pairs are the only extra writes introduced by function entry. -/
def writesFor (s : ArmState) (result : SszNative.BitVector.Outcome) : List Span :=
  bodyWrites s result ++ [savedSpan s]

def availableSpan (s : ArmState) : Span :=
  ((arenaOf s).base + (arenaOf s).used, (arenaOf s).capacity - (arenaOf s).used)

/-- Original function-entry ownership only. No dispatched state, helper state,
branch outcome or future ownership is assumed. Nat limbs retain their exact
physical representation, including arbitrary redundant high zero words. All
readonly regions may alias each other and the used arena prefix. -/
structure Owned (s : ArmState) (operand : SszNative.NatOperand) (data : Ssz.Bytes) : Prop where
  tag : read_mem_bytes 8 (r (.GPR 1#5) s) s = 4#64
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  descriptorBound : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64
  descriptor : SszNative.NatArithmetic.operandAt (widthLoad s)
    ((r (.GPR 1#5) s).toNat + 8) operand
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  stackLow : 448 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 448, 448)]
    (r (.GPR 0#5) s).toNat 80
  arenaBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaUsed : (arenaOf s).used ≤ (arenaOf s).capacity
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s ++ [savedSpan s]) (r (.GPR 4#5) s).toNat 24
  availableLocal : Protected (localWrites s ++ [savedSpan s, ((r (.GPR 4#5) s).toNat, 24)])
    (availableSpan s).1 (availableSpan s).2
  availableInput : Protected [availableSpan s] (r (.GPR 2#5) s).toNat data.size
  availableDescriptor : Protected [availableSpan s] (r (.GPR 1#5) s).toNat 24
  availableOperand : NatDivision.OperandOwned [availableSpan s] operand
  fresh : ∀ span ∈ (outcome s operand data).writes,
    Protected (localWrites s ++ [savedSpan s, ((r (.GPR 4#5) s).toNat, 24)]) span.1 span.2
  inputOwned : Protected (writesFor s (outcome s operand data)) (r (.GPR 2#5) s).toNat data.size
  descriptorOwned : Protected (writesFor s (outcome s operand data)) (r (.GPR 1#5) s).toNat 24
  operandOwned : NatDivision.OperandOwned (writesFor s (outcome s operand data)) operand
  activationOwned : Protected (bodyWrites s (outcome s operand data)) (savedSpan s).1 96

/-- Return to the actual original LR, with the original stack and caller ABI. -/
structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

/-- The accepted native postcondition is retained verbatim; original-entry
observations additionally expose exact buffers, cursor, readonly representation,
borrowed source (including empty input), original ABI and physical byte frame. -/
structure Post (s t : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes) : Prop where
  native : SszArm.BitVector.Post (entered s .bitVector) t length data
  returned : Returned s t
  result : SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat data (outcome s length data).result
  written : (outcome s length data).writtenAt (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = (outcome s length data).used
  arenaBase : read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
  frame : MemoryFrame (writesFor s (outcome s length data)) s t
  operand : NatDivision.OperandPreserved s t length
  input : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  inputBytes : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptorBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 24 → t.mem a = s.mem a

end SszArm.Dispatch.BitVector

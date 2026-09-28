import SszArm.BitVectorImpl
import SszArm.NatDivisionContract
import SszArm.NatAddContract
import SszArm.NatExactContract
import SszArm.NatToU128Contract
import SszArm.ByteViewMemory
import SszArm.MemcpyProofs
import SszBitVectorMemory

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- X19 is the arena argument saved by the common deserialize prologue. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 19#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) s).toNat⟩

def outcome (s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes) :
    SszNative.BitVector.Outcome :=
  SszNative.BitVector.run length data (arenaOf s)

/-- The nested division frame extends eighty bytes below body SP. The writable
body temporaries stop before the saved x19--x30 activation at SP+272. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 80), ((r (.GPR 31#5) s).toNat - 80, 352)]

/-- Both actual allocation extents survive a later failure. Alignment padding is
not a writable span. The arena descriptor contributes only its cursor word. -/
def writesFor (s : ArmState) (result : SszNative.BitVector.Outcome) : List Span :=
  localWrites s ++
    (if result.writes = [] then [] else [((r (.GPR 19#5) s).toNat + 16, 8)]) ++
    result.writes

def availableSpan (s : ArmState) : Span :=
  ((arenaOf s).base + (arenaOf s).used, (arenaOf s).capacity - (arenaOf s).used)

/-- Physical postdispatch-entry obligations. Readonly input, descriptor and Nat
limbs may overlap each other or used scratch. The public scratch ABI separates
the available suffix, not the entire capacity, from live inputs and activation. -/
structure Owned (s : ArmState) (operand : SszNative.NatOperand) (data : Ssz.Bytes) : Prop where
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  descriptorBound : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64
  descriptor : SszNative.NatArithmetic.operandAt (widthLoad s)
    ((r (.GPR 1#5) s).toNat + 8) operand
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  stackLow : 80 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 368 ≤ 2^64
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 80, 448)]
    (r (.GPR 0#5) s).toNat 80
  arenaBound : (r (.GPR 19#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaUsed : (arenaOf s).used ≤ (arenaOf s).capacity
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s) (r (.GPR 19#5) s).toNat 24
  availableLocal : Protected (localWrites s ++
    [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
    (availableSpan s).1 (availableSpan s).2
  availableInput : Protected [availableSpan s] (r (.GPR 2#5) s).toNat data.size
  availableDescriptor : Protected [availableSpan s] (r (.GPR 1#5) s).toNat 24
  availableOperand : NatDivision.OperandOwned [availableSpan s] operand
  fresh : ∀ span ∈ (outcome s operand data).writes,
    Protected (localWrites s ++
      [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
      span.1 span.2
  inputOwned : Protected (writesFor s (outcome s operand data))
    (r (.GPR 2#5) s).toNat data.size
  descriptorOwned : Protected (writesFor s (outcome s operand data))
    (r (.GPR 1#5) s).toNat 24
  operandOwned : NatDivision.OperandOwned (writesFor s (outcome s operand data)) operand
  activationOwned : Protected (writesFor s (outcome s operand data))
    ((r (.GPR 31#5) s).toNat + 272) 96

/-- The original common return restores the saved caller activation, not the
callee-saved register values already repurposed at postdispatch entry. -/
structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s + 368#64
  registers : ∀ reg offset, (reg, offset) ∈ BoolCodec.savedRegisters →
    r (.GPR reg) t = read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  activation : BoolCodec.ActivationPreserved s t

/-- Exact native observation, including both allocations, the committed cursor,
original borrowed bytes and original noncanonical physical Nat representation. -/
structure Post (s t : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes) : Prop where
  returned : Returned s t
  result : SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat data (outcome s length data).result
  written : (outcome s length data).writtenAt (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) t).toNat =
    (outcome s length data).used
  arenaBase : read_mem_bytes 8 (r (.GPR 19#5) s) t =
    read_mem_bytes 8 (r (.GPR 19#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s
  frame : MemoryFrame (writesFor s (outcome s length data)) s t
  operand : NatDivision.OperandPreserved s t length
  input : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  inputBytes : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptorBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 24 → t.mem a = s.mem a

theorem Owned.physical {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : data.size < 2^64 := by
  rw [← owned.length]
  exact (r (.GPR 3#5) s).isLt

/-- Erasure keeps host scratch exhaustion distinct from pinned SSZ errors. -/
theorem Post.refines {s t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (post : Post s t length data) :
    (SszNative.BitVector.Exhausted length (arenaOf s) →
      SszNative.BitVector.failureAt (widthLoad t) (r (.GPR 0#5) s).toNat .scratchExhausted) ∧
    (¬ SszNative.BitVector.Exhausted length (arenaOf s) →
      SszNative.BitView.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.bitVector length.value) data)) := by
  have erased := SszNative.BitVector.ResultAt.erased (widthLoad t)
    (r (.GPR 0#5) s).toNat (r (.GPR 2#5) s).toNat data
    (outcome s length data).result post.result
  change match (outcome s length data).erase data with
    | .ok value => _
    | .error reason => _ at erased
  constructor
  · intro exhausted
    have scratch := (SszNative.BitVector.run_scratch_iff length data (arenaOf s)).2 exhausted
    simpa only [outcome, scratch] using erased
  · intro exhausted
    rcases SszNative.BitVector.run_refines length data (arenaOf s) owned.physical with spec | scratch
    · simpa only [outcome, spec] using erased
    · exact False.elim (exhausted
        ((SszNative.BitVector.run_scratch_iff length data (arenaOf s)).1 scratch))

end SszArm.BitVector

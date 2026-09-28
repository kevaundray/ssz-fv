import SszArm.DispatchEntry
import SszArm.BitListProofs

namespace SszArm.DispatchBitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open Dispatch (bodySP)
open BitList (Variant optionAddress)

def dispatchKind : Variant → Dispatch.Kind
  | .list => .bitList
  | .progressive => .progressiveBitList

/-- The actual descriptor discriminant and payload at original X1. -/
structure Tagged (s : ArmState) (kind : Variant) (limit : Option Nat) : Prop where
  tag : read_mem_bytes 8 (r (.GPR 1#5) s) s = (dispatchKind kind).tag
  payload : BitList.Descriptor s kind limit

def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 4#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s).toNat⟩

def outcome (s : ArmState) (limit : Option Nat) (data : Ssz.Bytes) :=
  SszNative.Delimited.run limit data (arenaOf s)

def saveSpan (s : ArmState) : Span := ((r (.GPR 31#5) s).toNat - 96, 96)

/-- Physical addresses calculated from original SP, not a future machine state.
The progressive helper may reuse the restored old activation. -/
def stackWrites (s : ArmState) : Variant → List Span
  | .list => [((bodySP s).toNat - 112, 112), ((bodySP s).toNat + 144, 24)]
  | .progressive => [((bodySP s).toNat + 256, 112)]

def localWrites (s : ArmState) (kind : Variant) : List Span :=
  ((r (.GPR 0#5) s).toNat, 80) :: stackWrites s kind

def bodyWrites (s : ArmState) (kind : Variant) : Option SszNative.Arena.Reservation → List Span
  | none => localWrites s kind
  | some reservation => localWrites s kind ++
      [((r (.GPR 4#5) s).toNat + 16, 8), (reservation.pointer, 16)]

def writesFor (s : ArmState) (kind : Variant) (allocation : Option SszNative.Arena.Reservation) : List Span :=
  saveSpan s :: bodyWrites s kind allocation

def availableSpan (s : ArmState) : Span :=
  ((arenaOf s).base + (arenaOf s).used, (arenaOf s).capacity - (arenaOf s).used)

/-- Original private-function ABI storage only. Readonly spans and arbitrary
physical cap limbs may alias each other or the used arena prefix. -/
structure Owned (s : ArmState) (kind : Variant) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  descriptorBound : (r (.GPR 1#5) s).toNat + kind.descriptorBytes ≤ 2^64
  descriptor : Tagged s kind limit
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  stackLow : 480 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((bodySP s).toNat - 112, 480)] (r (.GPR 0#5) s).toNat 80
  arenaBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaUsed : (arenaOf s).used ≤ (arenaOf s).capacity
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (saveSpan s :: localWrites s kind) (r (.GPR 4#5) s).toNat 24
  availableLocal : Protected (localWrites s kind ++
    [((bodySP s).toNat + 272, 96), ((r (.GPR 4#5) s).toNat, 24)])
    (availableSpan s).1 (availableSpan s).2
  availableInput : Protected [availableSpan s] (r (.GPR 2#5) s).toNat data.size
  availableDescriptor : Protected [availableSpan s] (r (.GPR 1#5) s).toNat kind.descriptorBytes
  availableLimbs : ∀ cap, limit = some cap → NatOwned [availableSpan s]
    (read_mem_bytes 8 (optionAddress s kind + 8#64) s)
    (read_mem_bytes 8 (optionAddress s kind + 16#64) s)
  fresh : ∀ reservation, SszNative.Delimited.allocation data (arenaOf s) = some reservation →
    Protected (localWrites s kind ++ [((r (.GPR 4#5) s).toNat, 24)]) reservation.pointer 16
  inputOwned : Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
    (r (.GPR 2#5) s).toNat data.size
  descriptorOwned : Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
    (r (.GPR 1#5) s).toNat kind.descriptorBytes
  limbsOwned : ∀ cap, limit = some cap →
    NatOwned (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
      (read_mem_bytes 8 (optionAddress s kind + 8#64) s)
      (read_mem_bytes 8 (optionAddress s kind + 16#64) s)
  activationOwned : kind = .list →
    Protected (bodyWrites s kind (SszNative.Delimited.allocation data (arenaOf s)))
      ((bodySP s).toNat + 272) 96

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg displacement, (reg, displacement) ∈ BoolCodec.savedRegisters →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

/-- Original observed native result, full prepared allocation, exact cursor,
readonly physical representations, and original caller return/ABI frame. -/
structure Post (s t : ArmState) (kind : Variant) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  returned : Returned s t
  result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat (optionAddress s kind).toNat data (outcome s limit data)
  prepared : (outcome s limit data).PreparedAt (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = (outcome s limit data).used
  arenaBase : read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t = read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s
  frame : MemoryFrame (writesFor s kind (outcome s limit data).allocation) s t
  input : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  inputBytes : ∀ a : BitVec 64, (r (.GPR 2#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 2#5) s).toNat + data.size → t.mem a = s.mem a
  descriptorBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + kind.descriptorBytes → t.mem a = s.mem a
  capBytes : ∀ cap, limit = some cap → ∀ a : BitVec 64,
    let pointer := read_mem_bytes 8 (optionAddress s kind + 8#64) s
    let payload := read_mem_bytes 8 (optionAddress s kind + 16#64) s
    pointer ≠ 0#64 → pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * payload.toNat → t.mem a = s.mem a
  activation : kind = .list → ∀ reg displacement, (reg, displacement) ∈ BoolCodec.savedRegisters →
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 displacement) t = r (.GPR reg) s

end SszArm.DispatchBitList

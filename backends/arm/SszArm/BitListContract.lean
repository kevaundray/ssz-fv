import SszArm.BitListImpl
import SszArm.DelimitedProofs
import SszArm.BitVectorMemory

namespace SszArm.BitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)

inductive Variant where
  | list | progressive
  deriving DecidableEq

def Variant.entry : Variant → Nat
  | .list => listEntry
  | .progressive => progressiveEntry

def Variant.descriptorBytes : Variant → Nat
  | .list => 24
  | .progressive => 32

/-- In the list descriptor the cap occupies the same pair offsets as Some,
although the preceding word is the descriptor discriminant rather than Some. -/
def optionAddress (s : ArmState) : Variant → BitVec 64
  | .list => r (.GPR 1#5) s
  | .progressive => r (.GPR 1#5) s + 8#64

def Descriptor (s : ArmState) : Variant → Option Nat → Prop
  | .list, some cap => SszNative.NatMemory.Pair (widthLoad s)
      (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
      (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s) cap
  | .list, none => False
  | .progressive, limit => SszNative.NatMemory.OptionAt (widthLoad s)
      (optionAddress s .progressive).toNat limit

def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 19#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) s).toNat⟩

def outcome (s : ArmState) (limit : Option Nat) (data : Ssz.Bytes) :=
  SszNative.Delimited.run limit data (arenaOf s)

/-- The tail helper may overwrite the already-restored old activation. The
ordinary call instead uses fresh stack below body SP and its 24-byte Some. -/
def stackWrites (s : ArmState) : Variant → List Span
  | .list => [((r (.GPR 31#5) s).toNat - 112, 112),
      ((r (.GPR 31#5) s).toNat + 144, 24)]
  | .progressive => [((r (.GPR 31#5) s).toNat + 256, 112)]

def localWrites (s : ArmState) (kind : Variant) : List Span :=
  ((r (.GPR 0#5) s).toNat, 80) :: stackWrites s kind

def writesFor (s : ArmState) (kind : Variant) : Option SszNative.Arena.Reservation → List Span
  | none => localWrites s kind
  | some reservation => localWrites s kind ++
      [((r (.GPR 19#5) s).toNat + 16, 8), (reservation.pointer, 16)]

def availableSpan (s : ArmState) : Span :=
  ((arenaOf s).base + (arenaOf s).used, (arenaOf s).capacity - (arenaOf s).used)

/-- Only original physical input and scratch ownership is assumed. Readonly
inputs, descriptor, and cap limbs are allowed to alias each other and used arena. -/
structure Owned (s : ArmState) (kind : Variant) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  length : (r (.GPR 3#5) s).toNat = data.size
  inputBound : (r (.GPR 2#5) s).toNat + data.size ≤ 2^64
  input : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 2#5) s).toNat data
  descriptorBound : (r (.GPR 1#5) s).toNat + kind.descriptorBytes ≤ 2^64
  descriptor : Descriptor s kind limit
  outputBound : (r (.GPR 0#5) s).toNat + 80 ≤ 2^64
  stackLow : 112 ≤ (r (.GPR 31#5) s).toNat
  stackHigh : (r (.GPR 31#5) s).toNat + 368 < 2^64
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 112, 480)]
    (r (.GPR 0#5) s).toNat 80
  arenaBound : (r (.GPR 19#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaUsed : (arenaOf s).used ≤ (arenaOf s).capacity
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s kind) (r (.GPR 19#5) s).toNat 24
  availableLocal : Protected (localWrites s kind ++
    [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
    (availableSpan s).1 (availableSpan s).2
  availableInput : Protected [availableSpan s] (r (.GPR 2#5) s).toNat data.size
  availableDescriptor : Protected [availableSpan s] (r (.GPR 1#5) s).toNat kind.descriptorBytes
  availableLimbs : ∀ cap, limit = some cap → NatOwned [availableSpan s]
    (read_mem_bytes 8 (optionAddress s kind + 8#64) s)
    (read_mem_bytes 8 (optionAddress s kind + 16#64) s)
  fresh : ∀ reservation, SszNative.Delimited.allocation data (arenaOf s) = some reservation →
    Protected (localWrites s kind ++ [((r (.GPR 19#5) s).toNat, 24)]) reservation.pointer 16
  inputOwned : Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
    (r (.GPR 2#5) s).toNat data.size
  descriptorOwned : Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
    (r (.GPR 1#5) s).toNat kind.descriptorBytes
  limbsOwned : ∀ cap, limit = some cap →
    NatOwned (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
      (read_mem_bytes 8 (optionAddress s kind + 8#64) s)
      (read_mem_bytes 8 (optionAddress s kind + 16#64) s)
  activationOwned : kind = .list →
    Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
      ((r (.GPR 31#5) s).toNat + 272) 96

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s + 368#64
  registers : ∀ reg displacement, (reg, displacement) ∈ BoolCodec.savedRegisters →
    r (.GPR reg) t = read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 displacement) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

structure Post (s t : ArmState) (kind : Variant) (limit : Option Nat) (data : Ssz.Bytes) : Prop where
  returned : Returned s t
  result : SszNative.Delimited.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat (optionAddress s kind).toNat data (outcome s limit data)
  prepared : (outcome s limit data).PreparedAt (widthLoad t)
  cursor : (read_mem_bytes 8 (r (.GPR 19#5) s + 16#64) t).toNat = (outcome s limit data).used
  arenaBase : read_mem_bytes 8 (r (.GPR 19#5) s) t = read_mem_bytes 8 (r (.GPR 19#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 19#5) s + 8#64) s
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
  activation : kind = .list → BoolCodec.ActivationPreserved s t

theorem Owned.physical {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : data.size < 2^64 := by
  rw [← owned.length]
  exact (r (.GPR 3#5) s).isLt

end SszArm.BitList

import SszArm.IndicesStorage
import SszArm.NatAddMemory
import SszNatShiftResources

set_option autoImplicit false

namespace SszArm.Indices.NatShr

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

/-- The actual shr ABI passes the arena in x6 after the aligned x4/x5 u128. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 6#5) s) s).toNat,
    (read_mem_bytes 8 (r (.GPR 6#5) s + 8#64) s).toNat,
    (read_mem_bytes 8 (r (.GPR 6#5) s + 16#64) s).toNat⟩

def outcome (s : ArmState) (operand : NatOperand) (bits : BitVec 128) :
    SszNative.NatArithmetic.Outcome NatOperand :=
  SszNative.NatShift.shr operand bits.toNat
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used

/-- Only active success fields are writable; error initialization writes the
full initialized 68-byte payload. Both paths use one lowered spill slot. -/
def localWrites (s : ArmState) (result : SszNative.NatArithmetic.Outcome NatOperand) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16)] ++
    match result.result with
    | .ok _ => [((r (.GPR 0#5) s).toNat, 16), ((r (.GPR 0#5) s).toNat + 64, 4)]
    | .error _ => [((r (.GPR 0#5) s).toNat, 68)]

def writesFor (s : ArmState) (result : SszNative.NatArithmetic.Outcome NatOperand) : List Span :=
  match result.allocation with
  | none => localWrites s result
  | some reservation => localWrites s result ++
      [((r (.GPR 6#5) s).toNat + 16, 8)] ++
      Storage.mutableSpan reservation.pointer (8 * result.written.length)

/-- Entry ownership contains only input observations and source-derived writable
geometry. It never assumes a later execution, a helper return, or a caller frame.
The logical Nat is unrestricted, including empty and padded Large inputs. -/
structure Owned (s : ArmState) (operand : NatOperand) (bits : BitVec 128) : Prop where
  pointer : r (.GPR 1#5) s = operand.pointer
  payload : r (.GPR 2#5) s = operand.payload
  shiftLow : r (.GPR 4#5) s = bits.setWidth 64
  shiftHigh : r (.GPR 5#5) s = (bits >>> 64).setWidth 64
  operandAt : operand.At (widthLoad s)
  inputBacking : Codec.Storage.Backing (Protected (writesFor s (outcome s operand bits))) operand
  outputPhysical : Codec.Storage.Physical (r (.GPR 0#5) s).toNat 72 8
  stackBound : 16 ≤ (r (.GPR 31#5) s).toNat
  stackPhysical : Codec.Storage.Physical ((r (.GPR 31#5) s).toNat - 16) 16 16
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
    (r (.GPR 0#5) s).toNat 72
  arenaPhysical : Codec.Storage.Physical (r (.GPR 6#5) s).toNat 24 8
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s (outcome s operand bits)) (r (.GPR 6#5) s).toNat 24
  fresh : ∀ reservation, (outcome s operand bits).allocation = some reservation →
    Protected (localWrites s (outcome s operand bits) ++ [((r (.GPR 6#5) s).toNat, 24)])
      reservation.pointer (8 * (outcome s operand bits).written.length)

structure Post (s t : ArmState) (operand : NatOperand) (bits : BitVec 128) : Prop where
  returned : Returned s t
  result : (Storage.natResult (r (.GPR 0#5) s).toNat
    ((outcome s operand bits).result.mapError SszNative.Indices.Error.arithmetic)).At t
  written : NatAdd.WrittenAt (widthLoad t) (outcome s operand bits)
  cursor : (read_mem_bytes 8 (r (.GPR 6#5) s + 16#64) t).toNat =
    (outcome s operand bits).used
  frame : MemoryFrame (writesFor s (outcome s operand bits)) s t
  input : NatAdd.OperandPreserved s t operand
  arenaBase : read_mem_bytes 8 (r (.GPR 6#5) s) t = read_mem_bytes 8 (r (.GPR 6#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 6#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 6#5) s + 8#64) s

/-- The source model's no-allocation path never adds a zero-sized mutable span. -/
theorem unallocated_writes (s : ArmState) (operand : NatOperand) (bits : BitVec 128)
    (none : (outcome s operand bits).allocation = Option.none) :
    writesFor s (outcome s operand bits) = localWrites s (outcome s operand bits) := by
  simp only [writesFor, none]

/-- Physical input storage supplies the host bound, not operand.value. -/
theorem Owned.word_count {s : ArmState} {operand : NatOperand} {bits : BitVec 128}
    (owned : Owned s operand bits) : operand.words.length < 2^64 := by
  cases operand with
  | small word => simp [SszNative.NatOperand.words]
  | large pointer words =>
      have bounded := owned.inputBacking.1
      change words.length < 2^64
      omega

end SszArm.Indices.NatShr

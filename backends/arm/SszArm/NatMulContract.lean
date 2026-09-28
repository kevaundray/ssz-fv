import SszArm.NatAddMemory
import SszArm.NatMulWordContract
import SszArm.NatMulImpl
import SszArm.NatMulWordImpl
import SszArm.BitVectorProgram

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)
open NatAdd (OperandOwned OperandPreserved WrittenAt)

def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState := NatAdd.arenaOf s

def outcome (s : ArmState) (left right : SszNative.NatOperand) :
    SszNative.NatArithmetic.Outcome SszNative.NatOperand :=
  SszNative.NatMul.run left right (arenaOf s).base (arenaOf s).capacity (arenaOf s).used

def localWrites (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : List Span :=
  [((r (.GPR 31#5) s).toNat - 144, 144)] ++
    match result.result with
    | .ok _ => [((r (.GPR 0#5) s).toNat, 16), ((r (.GPR 0#5) s).toNat + 64, 4)]
    | .error _ => [((r (.GPR 0#5) s).toNat, 68)]

def writesFor (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : List Span :=
  match result.allocation with
  | none => localWrites s result
  | some reservation => localWrites s result ++
      [((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * result.written.length)]

structure Owned (s : ArmState) (left right : SszNative.NatOperand) : Prop where
  leftPointer : r (.GPR 1#5) s = left.pointer
  leftPayload : r (.GPR 2#5) s = left.payload
  rightPointer : r (.GPR 3#5) s = right.pointer
  rightPayload : r (.GPR 4#5) s = right.payload
  leftAt : left.At (widthLoad s)
  rightAt : right.At (widthLoad s)
  outputBound : (r (.GPR 0#5) s).toNat + 72 ≤ 2^64
  stackBound : 144 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 144, 144)]
    (r (.GPR 0#5) s).toNat 72
  arenaBound : (r (.GPR 5#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s (outcome s left right)) (r (.GPR 5#5) s).toNat 24
  fresh : ∀ reservation, (outcome s left right).allocation = some reservation →
    Protected (localWrites s (outcome s left right) ++ [((r (.GPR 5#5) s).toNat, 24)])
      reservation.pointer (8 * (outcome s left right).written.length)
  leftOwned : OperandOwned (writesFor s (outcome s left right)) left
  rightOwned : OperandOwned (writesFor s (outcome s left right)) right

structure Post (s t : ArmState) (left right : SszNative.NatOperand) : Prop where
  returned : Returned s t
  result : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (outcome s left right).result
  written : WrittenAt (widthLoad t) (outcome s left right)
  cursor : (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t).toNat = (outcome s left right).used
  frame : MemoryFrame (writesFor s (outcome s left right)) s t
  left : OperandPreserved s t left
  right : OperandPreserved s t right
  arenaBase : read_mem_bytes 8 (r (.GPR 5#5) s) t = read_mem_bytes 8 (r (.GPR 5#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s

theorem Post.arithmetic {s t : ArmState} {left right result : SszNative.NatOperand}
    (post : Post s t left right) (success : (outcome s left right).result = .ok result) :
    SszNative.NatArithmetic.operandAt (widthLoad t) (r (.GPR 0#5) s).toNat result ∧
      widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 ∧
      result.value = left.value * right.value := by
  have stored := post.result
  rw [success] at stored
  exact ⟨stored.1, stored.2, SszNative.NatMul.run_value left right
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used result success⟩

end SszArm.NatMul

import SszArm.NatAddMemory
import SszNatMul

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)
open NatAdd (OperandOwned OperandPreserved WrittenAt)

def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 4#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s).toNat⟩

def outcome (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64) :
    SszNative.NatArithmetic.Outcome SszNative.NatOperand :=
  SszNative.NatMul.runWord operand factor (arenaOf s).base (arenaOf s).capacity (arenaOf s).used

def localWrites (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : List Span :=
  [((r (.GPR 31#5) s).toNat - 48, 48)] ++
    match result.result with
    | .ok _ => [((r (.GPR 0#5) s).toNat, 16), ((r (.GPR 0#5) s).toNat + 64, 4)]
    | .error _ => [((r (.GPR 0#5) s).toNat, 68)]

def writesFor (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : List Span :=
  match result.allocation with
  | none => localWrites s result
  | some reservation => localWrites s result ++
      [((r (.GPR 4#5) s).toNat + 16, 8), (reservation.pointer, 8 * result.written.length)]

structure Owned (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64) : Prop where
  pointer : r (.GPR 1#5) s = operand.pointer
  payload : r (.GPR 2#5) s = operand.payload
  factorRegister : r (.GPR 3#5) s = factor
  operandAt : operand.At (widthLoad s)
  outputBound : (r (.GPR 0#5) s).toNat + 72 ≤ 2^64
  stackBound : 48 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 48, 48)]
    (r (.GPR 0#5) s).toNat 72
  arenaBound : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64
  arenaStorage : (arenaOf s).base + (arenaOf s).capacity ≤ 2^64
  arenaNonnull : 0 < (arenaOf s).capacity → 0 < (arenaOf s).base
  arenaLocal : Protected (localWrites s (outcome s operand factor))
    (r (.GPR 4#5) s).toNat 24
  fresh : ∀ reservation, (outcome s operand factor).allocation = some reservation →
    Protected (localWrites s (outcome s operand factor) ++ [((r (.GPR 4#5) s).toNat, 24)])
      reservation.pointer (8 * (outcome s operand factor).written.length)
  inputOwned : OperandOwned (writesFor s (outcome s operand factor)) operand

structure Post (s t : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64) : Prop where
  returned : Returned s t
  result : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (outcome s operand factor).result
  written : WrittenAt (widthLoad t) (outcome s operand factor)
  cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat =
    (outcome s operand factor).used
  frame : MemoryFrame (writesFor s (outcome s operand factor)) s t
  input : OperandPreserved s t operand
  arenaBase : read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s
  arenaCapacity : read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t =
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s

theorem Post.arithmetic {s t : ArmState} {operand result : SszNative.NatOperand}
    {factor : BitVec 64} (post : Post s t operand factor)
    (success : (outcome s operand factor).result = .ok result) :
    SszNative.NatArithmetic.operandAt (widthLoad t) (r (.GPR 0#5) s).toNat result ∧
      widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 ∧
      result.value = operand.value * factor.toNat := by
  have stored := post.result
  rw [success] at stored
  exact ⟨stored.1, stored.2, SszNative.NatMul.runWord_value operand factor
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used result success⟩

end SszArm.NatMulWord

import SszX86.EmitBoolMemory

namespace SszX86.Emit
open BoolCodec UintCodec SszNative.Serialize

structure BoolOwned (s : MachineData) (value : Bool) : Prop where
  tag : s.regs.rcx.toBitVec = 0#64
  capacity : 1 ≤ s.regs.r9.toNat
  payload : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 1) 1 = some (if value then 1 else 0)
  output : Large.Mapped s.dmem s.regs.r14.toBitVec 1
  result : Large.Mapped s.dmem s.regs.rbx.toBitVec 8
  apart : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec 1 8

/-- The whole actual Bool body, including both guards, the borrowed byte read,
exact writes and jump to1593. Capacity and tag facts are current-state facts. -/
theorem bool_body (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (value : Bool) (owned : BoolOwned s value) :
    Eventually (step e) (fun t => t.2 = base + 1593 ∧
      BodyPost s (emit .bool (.bool value)) t.1) (s, base + 190) := by
  apply bool_value_guard e base hcode s _ owned.tag
  intro af0
  apply bool_capacity_guard e base hcode
  · intro zero
    have impossible := congrArg BitVec.toNat zero
    change s.regs.r9.toNat = 0 at impossible
    have := owned.capacity
    omega
  intro af1
  let current := boolCapacityTested (boolValueTested s af0) af1
  apply bool_payload_load e base hcode current value _ owned.payload
  apply bool_stores e base hcode current value _ owned.output owned.result
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  have post := bool_written_post (boolCapacityTested (boolValueTested s af0) af1) value owned.apart
  exact ⟨post.stack, post.result, post.length, post.output, post.frame, post.vector⟩

end SszX86.Emit

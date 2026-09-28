import SszX86.MeasureBitsSpills
import SszX86.MeasureBitsListPost
import SszX86.MeasureBitsContinue

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem count_pair_at_call (s before : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used ra : BitVec 64) (actual : NatOperand)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used before)
    (counted : (countCall bits address capacity used).result = .ok actual) :
    NatMemory.Pair (widthLoad (callState before ra).dmem) actual.pointer actual.payload actual.value := by
  apply NatOperand.At.pair
  apply operand_frame before.dmem (callState before ra).dmem _ (call_frame before ra)
    actual _ (resources.operand owned actual counted)
  intro a borrowed
  have allocated := from_wide_borrowed address capacity used bits.count actual counted a borrowed
  simpa only [resources.stack] using
    first_allocation_stack_safe s desc bits buffer address capacity used owned a allocated

theorem bound_pair_at_call (s before : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used ra : BitVec 64) (cap : NatOperand)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used before)
    (stored : cap.At (widthLoad before.dmem))
    (borrowed : ∀ a, Emit.NatBorrowed cap a → BodyBorrowed s desc (.bits bits) buffer a) :
    NatMemory.Pair (widthLoad (callState before ra).dmem) cap.pointer cap.payload cap.value := by
  apply NatOperand.At.pair
  apply operand_frame before.dmem (callState before ra).dmem _ (call_frame before ra) cap _ stored
  intro a inside work
  exact owned.readonly a (borrowed a inside)
    (Or.inr (Or.inr (Or.inr (by simpa only [resources.stack] using work))))

theorem compare_count_prefix (s before : MachineData) (after : MachineState)
    (desc : Desc) (bits : Packed) (buffer address capacity used ra : BitVec 64) (ord : Ordering)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used before)
    (returned : NatCompare.Returned (callState before ra) ra ord after) :
    CountPrefix s bits address capacity used after.1 := by
  obtain ⟨pc, result, memory, vectors, sp, registers⟩ := returned
  apply resources.stack_extension owned
  · rw [memory]
    simpa only [resources.stack] using call_frame before ra
  · rw [memory]
    exact mapped_extension_store _ _ _ _
  · apply UInt64.eq_of_toBitVec_eq
    simpa only [callState, UInt64.toBitVec_ofBitVec, BitVec.sub_add_cancel] using sp
  · exact UInt64.eq_of_toBitVec_eq (registers .rbx (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact vectors

theorem compare_spill_read (before : MachineData) (after : MachineState)
    (ra : BitVec 64) (ord : Ordering) (off : Nat) (v : BitVec 64)
    (within : 8 ≤ off ∧ off + 8 ≤ 24)
    (stored : Mem.loadInt before.dmem (before.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 = some (v.toNat : Int))
    (returned : NatCompare.Returned (callState before ra) ra ord after) :
    Mem.loadInt after.1.dmem (after.1.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 = some (v.toNat : Int) := by
  obtain ⟨pc, result, memory, vectors, sp, registers⟩ := returned
  have same : after.1.regs.rsp.toBitVec = before.regs.rsp.toBitVec := by
    simpa only [callState, UInt64.toBitVec_ofBitVec, BitVec.sub_add_cancel] using sp
  rw [memory, same, call_spill_read before ra off within]
  exact stored

end SszX86.Measure.Bits

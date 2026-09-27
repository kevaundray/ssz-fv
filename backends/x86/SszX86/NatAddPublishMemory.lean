import SszX86.NatAddWorkMemory
import SszX86.NatAddOutputMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Publication changes only the actual 68-byte native Result extent. -/
def PublishFrame (s : MachineData) (before after : DataMem) : Prop :=
  ∀ a : BitVec 64, Body.Outside a.toNat s.regs.rdi.toNat 68 → after.get? a = before.get? a

theorem success_publish_frame (s : MachineData) (m : DataMem) (pointer payload : BitVec 64)
    (bound : s.regs.rdi.toNat+68 ≤ 2^64) :
    PublishFrame s m (successMem m s.regs.rdi.toBitVec pointer payload) := by
  intro a outside
  apply success_mem_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 68 i bound outside hi

theorem error_publish_frame (s : MachineData) (m : DataMem)
    (bound : s.regs.rdi.toNat+68 ≤ 2^64) :
    PublishFrame s m (errorMem m s.regs.rdi.toBitVec) := by
  intro a outside
  apply error_mem_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 68 i bound outside hi

theorem count_error_publish_frame (s : MachineData) (m : DataMem)
    (bound : s.regs.rdi.toNat+68 ≤ 2^64) :
    PublishFrame s m (countErrorMem m s.regs.rdi.toBitVec) := by
  intro a outside
  apply count_error_mem_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 68 i bound outside hi

theorem WorkFrame.publish {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (publish : PublishFrame s before after) : WorkFrame s after outcome := by
  intro a output scratch
  exact (publish a output).trans (work a output scratch)

theorem PublishFrame.cursor {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {before after : DataMem} (publish : PublishFrame s before after) :
    widthLoad after (s.regs.r9.toNat+16) 8 = widthLoad before (s.regs.r9.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply publish
  have bound := owned.header_bound
  have apart := owned.header_output
  have addressNat : (BitVec.ofNat 64 (s.regs.r9.toNat+16) + BitVec.ofNat 64 i).toNat =
      s.regs.r9.toNat+16+i := by bv_omega
  rw [addressNat]
  unfold Body.Outside Body.Apart at *
  omega

theorem PublishFrame.written {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {before after : DataMem} (publish : PublishFrame s before after)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (stored : NatMemory.wordsAt (widthLoad before) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written) :
    NatMemory.wordsAt (widthLoad after) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written := by
  intro index
  have unchanged : widthLoad after (r.pointer+8*index.val) 8 =
      widthLoad before (r.pointer+8*index.val) 8 := by
    unfold widthLoad
    congr 1
    apply memmove_loadInt_congr
    intro i hi
    apply publish
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apart := owned.arena_output
    have usedBound := owned.used_bound
    have ix := index.isLt
    have addressNat : (BitVec.ofNat 64 (r.pointer+8*index.val) + BitVec.ofNat 64 i).toNat =
        r.pointer+8*index.val+i := by bv_omega
    rw [addressNat]
    unfold Body.Outside Body.Apart at *
    omega
  exact unchanged.trans (stored index)

end SszX86.NatAdd

import SszX86.NatAddMemoryFinish
import SszX86.NatAddPublishMemory
import SszX86.NatAddAllocatedAt
import SszNatAddMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem result_at (s : MachineData) (m : DataMem) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (work : WorkFrame s m (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (written : ∀ r,
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad m) r.pointer
        (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written)
    (result : NatOperand)
    (success : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .ok result) :
    result.At (widthLoad m) := by
  have frame := work.to_frame owned.stack_low
  exact SszNative.NatAdd.run_result_at (widthLoad m) left right address.toNat capacity.toNat used.toNat result
    (operand_preserved s left right left address capacity used ra owned m frame owned.left_at owned.left_owned)
    (operand_preserved s left right right address capacity used ra owned m frame owned.right_at owned.right_owned)
    (fun r allocated => allocated_at s left right address capacity used ra owned m r allocated (written r allocated))
    success

/-- Exact successful publication followed by the six restores and RET. -/
theorem success_memory_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (work : WorkFrame s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (written : ∀ r,
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad t.dmem) r.pointer
        (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48) (simd : t.zmms = s.zmms)
    (result : NatOperand)
    (success : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .ok result) :
    Eventually (step e) (Post s left right address capacity used ra)
      ({t with dmem := successMem t.dmem s.regs.rdi.toBitVec result.pointer result.payload}, base+612) := by
  have pub := success_publish_frame s t.dmem result.pointer result.payload owned.output_bound
  have finalWork := work.publish pub
  have finalWritten := fun r allocated => pub.written owned r allocated (written r allocated)
  have finalCursor := (pub.cursor owned).trans cursor
  have stored := result_at s _ left right address capacity used ra owned finalWork finalWritten result success
  have fields := success_reads t.dmem s.regs.rdi.toBitVec result.pointer result.payload
  apply finish_memory_cps e base hc s _ left right address capacity used ra owned finalWork
  · rw [success]
    exact ⟨⟨fields.1, fields.2.1, stored⟩, fields.2.2⟩
  · exact finalWritten
  · exact finalCursor
  · exact sp
  · exact simd

/-- Arena failure stores the exact arithmetic error niche, then returns. -/
theorem error_memory_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (work : WorkFrame s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (empty : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = none)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48) (simd : t.zmms = s.zmms)
    (failure : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .error .scratchExhausted) :
    Eventually (step e) (Post s left right address capacity used ra)
      ({t with dmem := errorMem t.dmem s.regs.rdi.toBitVec}, base+612) := by
  have pub := error_publish_frame s t.dmem owned.output_bound
  apply finish_memory_cps e base hc s _ left right address capacity used ra owned (work.publish pub)
  · rw [failure]
    exact error_reads t.dmem s.regs.rdi.toBitVec
  · intro r allocated
    rw [empty] at allocated
    cases allocated
  · exact (pub.cursor owned).trans cursor
  · exact sp
  · exact simd

/-- Count-overflow uses its own linked store order and the same exact error. -/
theorem count_error_memory_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (work : WorkFrame s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (empty : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = none)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48) (simd : t.zmms = s.zmms)
    (failure : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result = .error .scratchExhausted) :
    Eventually (step e) (Post s left right address capacity used ra)
      ({t with dmem := countErrorMem t.dmem s.regs.rdi.toBitVec}, base+612) := by
  have pub := count_error_publish_frame s t.dmem owned.output_bound
  apply finish_memory_cps e base hc s _ left right address capacity used ra owned (work.publish pub)
  · rw [failure]
    exact count_error_reads t.dmem s.regs.rdi.toBitVec
  · intro r allocated
    rw [empty] at allocated
    cases allocated
  · exact (pub.cursor owned).trans cursor
  · exact sp
  · exact simd

end SszX86.NatAdd

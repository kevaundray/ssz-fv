import SszX86.NatMulMemoryZero
import SszX86.NatMulMemoryCompose
import SszX86.NatMulMemoryResult

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- A nonallocating publication inherits the original cursor and exact frame
from the prologue. This includes zero and every pre-reservation error branch. -/
theorem post_unallocated (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (t : MachineState)
    (unallocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = none)
    (observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result)
    (publish : PublishFrame s (pushedMem s) t.1.dmem
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result)
    (returned : Returned s ra t) : Post s left right address capacity used ra t := by
  have frame := (pushed_model_frame s
    (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) owned.stack_low).publish publish
  have cursor := (SszNative.NatMul.no_allocation_resources left right address.toNat capacity.toNat
    used.toNat unallocated).1
  have header := (pushed_header s left right address capacity used ra owned).2.2
  apply post_of_memory s left right address capacity used ra owned t observed
  · intro r allocated
    rw [unallocated] at allocated
    cases allocated
  · exact returned
  · exact frame
  · rw [publish.cursor owned, cursor]
    change widthLoad (pushedMem s) (s.regs.r9.toBitVec.toNat+16) 8 = some used.toNat
    change Mem.loadInt (pushedMem s) (s.regs.r9.toBitVec+16#64) 8 = some (used.toNat : Int) at header
    simp only [widthLoad, width_address, header, Option.map_some, Int.toNat_natCast]

theorem zero_post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (t : MachineState) (zero : left.wordCount = 0 ∨ right.wordCount = 0)
    (memory : t.1.dmem = zeroMem (pushedMem s) s.regs.rdi.toBitVec)
    (returned : Returned s ra t) : Post s left right address capacity used ra t := by
  have model := SszNative.NatMul.run_zero left right address.toNat capacity.toNat used.toNat zero
  apply post_unallocated s left right address capacity used ra owned t
  · rw [model]
    rfl
  · rw [memory, model]
    exact zero_reads _ _
  · rw [memory, model]
    exact zero_publish_frame s _ owned.output_bound
  · exact returned

theorem error_post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (t : MachineState)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error .scratchExhausted)
    (memory : t.1.dmem = errorMem (pushedMem s) s.regs.rdi.toBitVec)
    (returned : Returned s ra t) : Post s left right address capacity used ra t := by
  apply post_unallocated s left right address capacity used ra owned t
  · exact (failure_resources left right address capacity used .scratchExhausted failed).2.1
  · rw [memory, failed]
    exact error_reads _ _
  · rw [memory, failed]
    exact error_publish_frame s _ _ owned.output_bound
  · exact returned

theorem count_error_post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (t : MachineState)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result =
      .error .scratchExhausted)
    (memory : t.1.dmem = countErrorMem (pushedMem s) s.regs.rdi.toBitVec)
    (returned : Returned s ra t) : Post s left right address capacity used ra t := by
  apply post_unallocated s left right address capacity used ra owned t
  · exact (failure_resources left right address capacity used .scratchExhausted failed).2.1
  · rw [memory, failed]
    exact count_error_reads _ _
  · rw [memory, failed]
    exact count_error_publish_frame s _ _ owned.output_bound
  · exact returned

/-- The final original return is composed with the actual complete loop buffer,
cursor store, and publication stores; no initialized-result premise is needed. -/
theorem allocated_post (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (work : WorkFrame s m (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written)
    (cursor : widthLoad m (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used)
    (result : NatOperand)
    (success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result)
    (t : MachineState)
    (memory : t.1.dmem = successMem m s.regs.rdi.toBitVec result.pointer result.payload)
    (returned : Returned s ra t) : Post s left right address capacity used ra t := by
  have publish := success_publish_frame s m result.pointer result.payload result owned.output_bound
  have finalFrame : Frame s t.1.dmem
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) := by
    rw [memory]
    apply (work.to_frame owned.stack_low).publish
    simpa only [success] using publish
  apply post_of_memory s left right address capacity used ra owned t
  · rw [memory, success]
    exact allocated_publish_observed s left right address capacity used ra owned m r allocated
      written result success
  · intro actual actualAllocated
    have same : actual = r := Option.some.inj (actualAllocated.symm.trans allocated)
    subst actual
    rw [memory]
    exact publish.written owned r allocated written
  · exact returned
  · exact finalFrame
  · rw [memory, publish.cursor owned]
    exact cursor

end SszX86.NatMul

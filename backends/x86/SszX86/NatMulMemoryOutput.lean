import SszX86.NatMulMemory
import SszX86.NatAddOutputMemory

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- Publication reuses the accepted Nat arithmetic memory layout and store order. -/
abbrev pairMem := NatAdd.pairMem
abbrev successMem := NatAdd.successMem
abbrev errorMem := NatAdd.errorMem
abbrev countErrorMem := NatAdd.countErrorMem

def PublishFrame (s : MachineData) (before after : DataMem)
    (result : Except NatArithmetic.Failure NatOperand) : Prop :=
  ∀ a : BitVec 64, ResultOutside result s.regs.rdi.toNat a.toNat →
    after.get? a = before.get? a

private theorem store_region_frame (m : DataMem) (out a : BitVec 64)
    (off count : Nat) (value : Int) (bound : out.toNat + 72 ≤ 2^64)
    (inside : off + count ≤ 72) (outside : Body.Outside a.toNat (out.toNat+off) count) :
    (Mem.storeInt m (out + BitVec.ofNat 64 off) count value).get? a = m.get? a := by
  apply memmove_store_lookup_outside
  intro i hi equal
  have byte : i < count := by simpa only [Int.toBytes_length] using hi
  have natural : ((out + BitVec.ofNat 64 off) + BitVec.ofNat 64 i).toNat = out.toNat+off+i := by
    bv_omega
  have same := congrArg BitVec.toNat equal
  rw [natural] at same
  unfold Body.Outside at outside
  omega

theorem success_publish_frame (s : MachineData) (m : DataMem) (pointer payload : BitVec 64)
    (result : NatOperand) (bound : s.regs.rdi.toNat + 72 ≤ 2^64) :
    PublishFrame s m (successMem m s.regs.rdi.toBitVec pointer payload) (.ok result) := by
  intro a outside
  obtain ⟨pair, status⟩ := outside
  change Body.Outside a.toNat s.regs.rdi.toBitVec.toNat 16 at pair
  change s.regs.rdi.toBitVec.toNat + 72 ≤ 2^64 at bound
  unfold successMem NatAdd.successMem NatAdd.pairMem
  rw [store_region_frame _ s.regs.rdi.toBitVec a 64 4 0 bound (by decide) status]
  rw [store_region_frame _ s.regs.rdi.toBitVec a 8 8 payload.toInt bound (by decide)
    (by unfold Body.Outside at *; omega)]
  exact store_region_frame _ s.regs.rdi.toBitVec a 0 8 pointer.toInt bound (by decide)
    (by unfold Body.Outside at *; omega)

theorem error_publish_frame (s : MachineData) (m : DataMem)
    (reason : NatArithmetic.Failure) (bound : s.regs.rdi.toNat + 72 ≤ 2^64) :
    PublishFrame s m (errorMem m s.regs.rdi.toBitVec) (.error reason) := by
  intro a outside
  change s.regs.rdi.toBitVec.toNat + 72 ≤ 2^64 at bound
  apply NatAdd.error_mem_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 68 i (by omega) outside hi

theorem count_error_publish_frame (s : MachineData) (m : DataMem)
    (reason : NatArithmetic.Failure) (bound : s.regs.rdi.toNat + 72 ≤ 2^64) :
    PublishFrame s m (countErrorMem m s.regs.rdi.toBitVec) (.error reason) := by
  intro a outside
  change s.regs.rdi.toBitVec.toNat + 72 ≤ 2^64 at bound
  apply NatAdd.count_error_mem_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 68 i (by omega) outside hi

theorem success_reads (m : DataMem) (out pointer payload : BitVec 64) :
    widthLoad (successMem m out pointer payload) out.toNat 8 = some pointer.toNat ∧
      widthLoad (successMem m out pointer payload) (out.toNat + 8) 8 = some payload.toNat ∧
      widthLoad (successMem m out pointer payload) (out.toNat + 64) 4 = some 0 :=
  NatAdd.success_reads m out pointer payload

theorem error_reads (m : DataMem) (out : BitVec 64) :
    NatArithmetic.errorAt (widthLoad (errorMem m out)) out.toNat .scratchExhausted :=
  NatAdd.error_reads m out

theorem count_error_reads (m : DataMem) (out : BitVec 64) :
    NatArithmetic.errorAt (widthLoad (countErrorMem m out)) out.toNat .scratchExhausted :=
  NatAdd.count_error_reads m out

theorem Frame.publish {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (frame : Frame s before outcome)
    (publish : PublishFrame s before after outcome.result) : Frame s after outcome := by
  intro a output activation scratch
  exact (publish a output).trans (frame a output activation scratch)

theorem PublishFrame.cursor {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {before after : DataMem} {result : Except NatArithmetic.Failure NatOperand}
    (publish : PublishFrame s before after result) :
    widthLoad after (s.regs.r9.toNat+16) 8 = widthLoad before (s.regs.r9.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply publish
  apply ResultOutside.of_outside
  have bound := owned.header_bound
  have apart := owned.header_output
  have natural : (BitVec.ofNat 64 (s.regs.r9.toNat+16) + BitVec.ofNat 64 i).toNat =
      s.regs.r9.toNat+16+i := by bv_omega
  rw [natural]
  unfold Body.Outside Body.Apart at *
  omega

theorem PublishFrame.written {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {before after : DataMem} {result : Except NatArithmetic.Failure NatOperand}
    (publish : PublishFrame s before after result) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (stored : NatMemory.wordsAt (widthLoad before) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written) :
    NatMemory.wordsAt (widthLoad after) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written := by
  intro index
  have unchanged : widthLoad after (r.pointer+8*index.val) 8 =
      widthLoad before (r.pointer+8*index.val) 8 := by
    unfold widthLoad
    congr 1
    apply memmove_loadInt_congr
    intro i hi
    apply publish
    apply ResultOutside.of_outside
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apart := owned.arena_output
    have usedBound := owned.used_bound
    have ix := index.isLt
    have natural : (BitVec.ofNat 64 (r.pointer+8*index.val) + BitVec.ofNat 64 i).toNat =
        r.pointer+8*index.val+i := by bv_omega
    rw [natural]
    unfold Body.Outside Body.Apart at *
    omega
  exact unchanged.trans (stored index)

/-- An exhausted call cannot overwrite even one arena or cursor byte. -/
theorem Post.failure_frame {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s left right address capacity used ra t) (reason : NatArithmetic.Failure)
    (failed : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .error reason)
    (a : BitVec 64) (output : Body.Outside a.toNat s.regs.rdi.toNat 68)
    (activation : Body.Outside a.toNat (s.regs.rsp.toNat-96) 96) :
    t.1.dmem.get? a = s.dmem.get? a := by
  apply post.frame a
  · simpa only [failed, ResultOutside] using output
  · exact activation
  · intro r allocated
    have none := (failure_resources left right address capacity used reason failed).2.1
    rw [none] at allocated
    cases allocated

end SszX86.NatMul

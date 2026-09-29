import SszX86.NatMulNormalizeResult
import SszX86.NatMulZeroReturn

namespace SszX86.NatMul
open SszNative
open UintCodec

def resultLoadState (s : MachineData) (out dst : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec out, rdx := UInt64.ofBitVec dst}}

theorem result_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out dst : BitVec 64)
    (output : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (out.toNat : Int))
    (pointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (dst.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (resultLoadState s out dst, base + 674)) :
    Eventually (step e) P (s, base + 664) := by
  natmul_step 5 row 25 using hc
  natmul_load output
  natmul_step 5 row 26 using hc
  natmul_load pointer
  exact next

theorem result_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (work : WorkFrame s t.dmem (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat))
    (written : NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).used)
    (outputMapped : Large.Mapped t.dmem s.regs.rdi.toBitVec 72)
    (counter : t.regs.rbp.toBitVec =
      BitVec.ofNat 64 (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length - 1)
    (output : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 24#64) 8 = some (s.regs.rdi.toNat : Int))
    (pointer : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8#64) 8 = some (r.pointer : Int))
    (stack : t.regs.rsp = s.regs.rsp - 88) (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 664) := by
  let words := (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written
  let result := NatOperand.fromWords (BitVec.ofNat 64 r.pointer) words
  have natural := allocated_pointer_nat s left right address capacity used ra owned r allocated
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have lengthBound : words.length < 2^64 := by dsimp only [words]; omega
  have success : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).result = .ok result :=
    allocation_result left right address capacity used r allocated
  apply result_load_cps e base hc t s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer) output
  · simpa only [natural] using pointer
  apply normalize_result_cps e base hc
    (resultLoadState t s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer)) words lengthBound counter
  · simpa only [resultLoadState, UInt64.toNat_ofBitVec, natural] using written
  intro u memory sameStack sameOutput sameSimd resultPointer resultPayload
  have outputEq : u.regs.rax = s.regs.rdi := by
    simpa only [resultLoadState, UInt64.ofBitVec_toBitVec] using sameOutput
  have normalizedPointer : u.regs.rdx.toBitVec = result.pointer := resultPointer
  have normalizedPayload : u.regs.rcx.toBitVec = result.payload := resultPayload
  have publishedWork : WorkFrame s
      (successMem t.dmem s.regs.rdi.toBitVec result.pointer result.payload)
      (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat) := by
    apply work.publish
    rw [success]
    exact success_publish_frame s t.dmem result.pointer result.payload result owned.output_bound
  apply result_publish_cps e base hc u
  · simpa only [memory, resultLoadState, outputEq] using outputMapped
  apply return_cps e base hc s _ ra
  · exact sameStack.trans stack
  · simpa only [memory, resultLoadState, outputEq, normalizedPointer, normalizedPayload] using publishedWork.saved owned
  · exact sameSimd.trans simd
  · simpa only [memory, resultLoadState, outputEq, normalizedPointer, normalizedPayload] using
      (publishedWork.to_frame owned.stack_low).return_slot owned
  intro final finalMemory returned
  apply allocated_post s left right address capacity used ra owned t.dmem r allocated work written cursor
    result success _
  · simpa only [memory, resultLoadState, outputEq, normalizedPointer, normalizedPayload] using finalMemory
  · exact returned

end SszX86.NatMul

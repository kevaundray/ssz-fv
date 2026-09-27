import SszX86.NatAddNormalizeResultPhase
import SszX86.NatAddReturn
import SszX86.NatAddCommitMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Final normalization scans the complete allocated list; success publication
retains the exact from_words representation while preserving every written limb. -/
theorem large_result_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra) (r : Arena.Reservation)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatAdd.writtenWords left right))
    (work : WorkFrame s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (stored : NatMemory.wordsAt (widthLoad t.dmem) r.pointer (SszNative.NatAdd.writtenWords left right))
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec-48)
    (out : t.regs.rdi = s.regs.rdi) (simd : t.zmms = s.zmms) (hm : OutputMapped t)
    (count : t.regs.rax.toBitVec = BitVec.ofNat 64 (SszNative.NatAdd.count left right))
    (pointer : t.regs.r10.toBitVec = BitVec.ofNat 64 r.pointer)
    (first : t.regs.r9.toBitVec = (SszNative.NatAdd.writtenWords left right)[0]?.getD 0) :
    Eventually (step e) (Post s left right address capacity used ra) (t,base+1325) := by
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have pointerNat := allocated_pointer_nat s left right address capacity used ra owned r allocated
  have lengthBound : (SszNative.NatAdd.writtenWords left right).length+1 < 2^64 := by
    rw [model] at bounds
    dsimp only [NatArithmetic.committed] at bounds
    omega
  have pointerRegister : t.regs.r10.toNat = r.pointer := by
    change t.regs.r10.toBitVec.toNat = r.pointer
    rw [pointer, pointerNat]
  apply normalize_result_cps e base hc t (SszNative.NatAdd.writtenWords left right)
    (SszNative.NatAdd.count left right) (SszNative.NatAdd.writtenWords_length left right)
    lengthBound count first
  · rw [pointerRegister]
    exact stored
  · intro u memory stack output simdSame resultPointer resultPayload
    have hm' : OutputMapped u := by
      change Large.Mapped u.dmem u.regs.rdi.toBitVec 68
      rw [memory, output]
      exact hm
    apply large_publish_cps e base hc u hm'
    rw [pointer] at resultPointer resultPayload
    have finalOut : u.regs.rdi.toBitVec = s.regs.rdi.toBitVec := by rw [output, out]
    rw [finalOut, resultPointer, resultPayload]
    have work' : WorkFrame s u.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) := by
      rw [memory]
      exact work
    refine success_memory_finish_cps e base hc s u left right address capacity used ra owned work' ?_ ?_
      ((congrArg UInt64.toBitVec stack).trans sp) (simdSame.trans simd) _ ?_
    · intro r' allocated'
      rw [model] at allocated'
      have same : r = r' := Option.some.inj allocated'
      cases same
      rw [memory, model]
      exact stored
    · rw [memory]
      exact cursor
    · rw [model]
      rfl

end SszX86.NatAdd

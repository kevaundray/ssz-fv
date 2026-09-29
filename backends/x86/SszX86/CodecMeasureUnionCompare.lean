import SszX86.CodecMeasureDecode
import SszX86.CodecStoragePlan
import SszX86.NatCompareProofs
import SszX86.CodecPlanSingletonMemory
import SszX86.EmitBitsMemory

namespace SszX86.CodecMeasure
open SszNative UintCodec

def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)},
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

/-- The selector scan's real CALL writes PC252 and enters the linked full Nat
comparator. Borrowed zero-padded or empty Large representations remain exact. -/
theorem union_compare_call (e : Executable) (base : Int64) (code : CodeAt e base)
    (helper : NatCompare.CodeAt e (base + Int64.ofInt natCompareOffset))
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rdi.toBitVec = left.pointer)
    (leftPayload : s.regs.rsi.toBitVec = left.payload)
    (rightPointer : s.regs.rdx.toBitVec = right.pointer)
    (rightPayload : s.regs.rcx.toBitVec = right.payload)
    (leftStored : left.At (widthLoad s.dmem)) (rightStored : right.At (widthLoad s.dmem))
    (leftSafe : ∀ a, Emit.NatBorrowed left a →
      ¬ Emit.InSpan a (s.regs.rsp.toBitVec - 8) 8)
    (rightSafe : ∀ a, Emit.NatBorrowed right a →
      ¬ Emit.InSpan a (s.regs.rsp.toBitVec - 8) 8)
    (mapped : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old) :
    Eventually (step e)
      (NatCompare.Returned (callState s (base + 252).toBitVec) (base + 252).toBitVec
        (compare left.value right.value)) (s, base + 247) := by
  have memoryFrame := Emit.Bits.store_frame s.dmem (s.regs.rsp.toBitVec - 8) 8
    (base + 252).toBitVec.toInt
  have leftAfter := Codec.operand_frame left leftStored memoryFrame leftSafe
  have rightAfter := Codec.operand_frame right rightStored memoryFrame rightSafe
  have leftPair := NatOperand.At.pair _ left leftAfter
  have rightPair := NatOperand.At.pair _ right rightAfter
  codec_measure_step 0 row 60 using code
  apply Delimited.store_cps
  · simpa using mapped
  · simp only [Effects.All]
    have run := NatCompare.program_correct e (base + Int64.ofInt natCompareOffset) helper
      (callState s (base + 252).toBitVec) left.value right.value (base + 252).toBitVec
      (by simpa only [callState, leftPointer, leftPayload] using leftPair)
      (by simpa only [callState, rightPointer, rightPayload] using rightPair)
      (by
        simpa only [callState, UInt64.toBitVec_ofBitVec, SszX86.ofBytes_wordBytes] using
          CodecPlanSingleton.stored_word s.dmem (s.regs.rsp.toBitVec - 8) (base + 252).toBitVec)
    simpa [callState, natCompareOffset, Int64.add_assoc] using run

/-- Equality observed by TEST AL is numerical equality, not pointer or raw limb
list identity. This is why duplicate selectors choose their first match. -/
theorem union_compare_equal {s : MachineData} {ra : BitVec 64} {left right : NatOperand}
    {t : MachineState} (returned : NatCompare.Returned s ra (compare left.value right.value) t) :
    t.1.regs.rax.toBitVec.setWidth 8 = 0 ↔ left.value = right.value := by
  rw [returned.2.1]
  by_cases equal : left.value = right.value
  · simp [equal, NatABI.orderingByte]
  · have notEqual : compare left.value right.value ≠ Ordering.eq := by
      intro same
      exact equal (Nat.compare_eq_eq.mp same)
    cases order : compare left.value right.value <;>
      simp_all [NatABI.orderingByte]

end SszX86.CodecMeasure

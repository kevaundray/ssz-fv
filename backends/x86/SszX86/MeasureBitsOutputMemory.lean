import SszX86.MeasureBitsOutput
import SszX86.MeasureBitsPropagate
import SszX86.MeasureOutputMemory

namespace SszX86.Measure.Bits
open SszNative UintCodec

/-- The vector-specific store order, including its two early expected words. -/
def scopeMem (m : DataMem) (out ep ev ap av : BitVec 64) : DataMem :=
  scopeTailMem
    (Mem.storeInt (Mem.storeInt m (out + 24#64) 8 ev.toInt) (out + 16#64) 8 ep.toInt)
    out ap av

theorem limit_reads (m : DataMem) (out : BitVec 64) (expected actual : NatOperand)
    (he : expected.At (widthLoad
      (limitMem m out expected.pointer expected.payload actual.pointer actual.payload)))
    (ha : actual.At (widthLoad
      (limitMem m out expected.pointer expected.payload actual.pointer actual.payload))) :
    SemanticErrorAt (widthLoad
      (limitMem m out expected.pointer expected.payload actual.pointer actual.payload))
      out.toNat 2 expected actual := by
  unfold SemanticErrorAt NatArithmetic.operandAt
  refine ⟨?_, ?_, ⟨?_, ?_, he⟩, ⟨?_, ?_, ha⟩, ?_, ?_, ?_⟩
  all_goals unfold limitMem
  all_goals measure_result_reads

theorem scope_reads (m : DataMem) (out : BitVec 64) (expected actual : NatOperand)
    (he : expected.At (widthLoad
      (scopeMem m out expected.pointer expected.payload actual.pointer actual.payload)))
    (ha : actual.At (widthLoad
      (scopeMem m out expected.pointer expected.payload actual.pointer actual.payload))) :
    SemanticErrorAt (widthLoad
      (scopeMem m out expected.pointer expected.payload actual.pointer actual.payload))
      out.toNat 3 expected actual := by
  unfold SemanticErrorAt NatArithmetic.operandAt
  refine ⟨?_, ?_, ⟨?_, ?_, he⟩, ⟨?_, ?_, ha⟩, ?_, ?_, ?_⟩
  all_goals unfold scopeMem scopeTailMem
  all_goals measure_result_reads

theorem limit_frame (m : DataMem) (out ep ev ap av : BitVec 64) :
    MemoryFrame m (limitMem m out ep ev ap av) (fun a => InSpan a out 68) := by
  intro a outside
  have apart : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [limitMem, BoolCodec.store_frame (limit := 68)]

theorem scope_frame (m : DataMem) (out ep ev ap av : BitVec 64) :
    MemoryFrame m (scopeMem m out ep ev ap av) (fun a => InSpan a out 68) := by
  intro a outside
  have apart : ∀ i < 68, a ≠ out + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [scopeMem, scopeTailMem, BoolCodec.store_frame (limit := 68)]

/-- The propagated result's footprint includes exactly the additional dword,
not a hypothetical shorter error object. -/
theorem propagated_frame (s : MachineData) (v : ErrorTail) :
    MemoryFrame s.dmem (propagatedMem s v) (fun a => InSpan a s.regs.rbx.toBitVec 72) := by
  intro a outside
  have apart : ∀ i < 72, a ≠ s.regs.rbx.toBitVec + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | omega | decide) only
    [propagatedMem, BoolCodec.store_frame (limit := 72)]

def scratchTail (padding : BitVec 32) : ErrorTail :=
  ⟨0, 0, 0, 0, 0, 0, padding⟩

theorem propagated_scratch_reads (s : MachineData) (padding : BitVec 32)
    (tag : s.regs.rcx.toBitVec = 1#64) (textLength : s.regs.rax.toBitVec = 0#64)
    (reason : s.regs.rdx.toBitVec.setWidth 32 = 32768#32) :
    ErrorAt (widthLoad (propagatedMem s (scratchTail padding))) s.regs.rbx.toNat
      (.arithmetic .scratchExhausted) := by
  change NatArithmetic.errorAt (widthLoad (propagatedMem s (scratchTail padding)))
    s.regs.rbx.toNat .scratchExhausted
  unfold NatArithmetic.errorAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [propagatedMem, scratchTail, tag, textLength, reason, ← UInt64.toNat_toBitVec]
  all_goals measure_result_reads

end SszX86.Measure.Bits

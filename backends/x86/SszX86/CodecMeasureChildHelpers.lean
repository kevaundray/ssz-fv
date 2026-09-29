import SszX86.CodecMeasureChildCall

namespace SszX86.CodecMeasureChild
open UintCodec

/-- Classification is called only after the recursive measurement returned
successfully; this is the actual CALL at local PC270, not a semantic callback. -/
theorem classifier_call (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 275).toBitVec, base + Int64.ofInt isFixedOffset)) :
    Eventually (step e) P (s, base + 270) := by
  codec_measure_child_step 67 using code
  apply Delimited.store_cps
  · simpa using mapped
  · simpa [callState, Effects.All, isFixedOffset, Int64.add_assoc] using next

/-- Variable children add the four-byte head before adding their body size. -/
theorem leading_add_call (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 324).toBitVec, base + Int64.ofInt natAddOffset)) :
    Eventually (step e) P (s, base + 319) := by
  codec_measure_child_step 82 using code
  apply Delimited.store_cps
  · simpa using mapped
  · simpa [callState, Effects.All, natAddOffset, Int64.add_assoc] using next

/-- The common size addition updates leading for an inline child and bodies for
a variable child; the selected accumulator pointer is the actual R15 value. -/
theorem size_add_call (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 391).toBitVec, base + Int64.ofInt natAddOffset)) :
    Eventually (step e) P (s, base + 386) := by
  codec_measure_child_step 99 using code
  apply Delimited.store_cps
  · simpa using mapped
  · simpa [callState, Effects.All, natAddOffset, Int64.add_assoc] using next

end SszX86.CodecMeasureChild

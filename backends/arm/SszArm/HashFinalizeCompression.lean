import SszArm.HashFinalizeFrame

namespace SszArm.Hash.Finalize

open Delimited (Protected)

/-- Only the buffer, chaining words and logical length remain live after consumption begins. -/
structure BufferAt (s t : ArmState) (buf : Vector UInt8 64)
    (words : Vector UInt32 8) (byteLen : UInt64) : Prop where
  buffer : BytesAt t (statePtr s) ⟨buf.toArray⟩
  chaining : ChainingAt t (statePtr s + 64#64) words
  length : read_mem_bytes 8 (statePtr s + 104#64) t = byteLen.toBitVec

theorem compression_call (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (buf : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (code : CodeAt s base) (data : DataAt s base)
    (owned : FinalizeOwned s base value) (compression : CompressionCorrect base)
    (aligned : CheckSPAlignment s) (live : Live s t) (stored : BufferAt s t buf words byteLen)
    (pc : read_pc t = base + compressOffset)
    (state : r (.GPR 0#5) t = statePtr s + 64#64)
    (input : r (.GPR 1#5) t = statePtr s) :
    ∃ fuel, Live s (run fuel t) ∧
      BufferAt s (run fuel t) buf (SszNative.HashStream.compressBuffer words buf) byteLen ∧
      read_pc (run fuel t) = r (.GPR 30#5) t := by
  have g := geometry owned
  have physical := g.stateBound
  have low := g.stackLow
  have apart := g.stateStack
  have spNat := g.bodySP_nat
  have at64 : (statePtr s + 64#64).toNat = (statePtr s).toNat + 64 := by bv_omega
  have contained := g.compression_contained live.sp state
  have rounds := protected_narrow_writes owned.roundsOwned contained
  have callOwned : CompressionOwned t base words ⟨buf.toArray⟩ := by
    constructor
    · exact vectorByteArray_size buf
    · simpa only [state] using stored.chaining
    · simpa only [input] using stored.buffer
    · rw [state, at64]; omega
    · rw [input]; omega
    · rw [live.sp]; exact g.bodySP_low
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp only [stackSpan, state, live.sp, at64]
      omega
    · simpa only [input] using g.compression_input live.sp state
    · exact rounds
  have currentCode := live.toActivation.code code
  have currentData := live.toActivation.data data owned
  obtain ⟨fuel, returned, result, frame⟩ := compression t words ⟨buf.toArray⟩
    currentCode.compress currentData.rounds currentData.roundsBound pc live.error
    (live.toActivation.aligned aligned) callOwned
  refine ⟨fuel, live.returned g returned frame contained
    (g.compression_saved live.sp state), ?_, returned.pc⟩
  constructor
  · exact bytesAt_frame frame (by rw [vectorByteArray_size]; omega)
      (by simpa only [vectorByteArray_size] using g.compression_input live.sp state) stored.buffer
  · simpa only [state, SszNative.HashStream.compressBuffer] using result
  · rw [read_frame _ 8 frame (by bv_omega) (g.compression_length live.sp state)]
    exact stored.length

end SszArm.Hash.Finalize

import SszArm.HashFinalizeBranches
import SszArm.HashFinalizeDelimiter

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

theorem prepare_step (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (owned : FinalizeOwned s base value) (aligned : CheckSPAlignment s)
    (activation : Activation s t)
    (output : r (.GPR 0#5) t = outputPtr s)
    (pointer : r (.GPR 1#5) t = statePtr s)
    (buffer : BytesAt t (statePtr s) ⟨(SszNative.HashStream.delimiterBuffer value).toArray⟩)
    (chaining : ChainingAt t (statePtr s + 64#64) value.chaining)
    (count : read_mem_bytes 8 (statePtr s + 96#64) t = BitVec.ofNat 64 value.buffered.val)
    (length : read_mem_bytes 8 (statePtr s + 104#64) t = value.byteLen.toBitVec) :
    Live s (prepareState t) ∧
    BufferAt s (prepareState t) (SszNative.HashStream.delimiterBuffer value) value.chaining value.byteLen ∧
    r (.GPR 0#5) (prepareState t) = BitVec.ofNat 64 (value.buffered.val + 1) ∧
    r (.GPR 8#5) (prepareState t) = BitVec.ofNat 64 value.buffered.val := by
  have g := geometry owned
  have physical := g.stateBound
  have ta := activation.aligned aligned
  obtain ⟨resultCount, loaded, outputReg, stateReg, memory⟩ := prepare_observe t ta
  have nextCount : preparedCount t = BitVec.ofNat 64 (value.buffered.val + 1) := by
    simp only [preparedCount, pointer, count, BitVec.ofNat_add]
    rfl
  have at96 : (statePtr s + 96#64).toNat = (statePtr s).toNat + 96 := by bv_omega
  have storeBound : (statePtr s + 96#64).toNat + 8 ≤ 2^64 := by rw [at96]; omega
  let writes : List Span := [((statePtr s + 96#64).toNat, 8)]
  have frame : MemoryFrame writes t (prepareState t) := by
    intro address outside
    rw [memory, pointer]
    exact BoolCodec.write_mem_bytes_frame _ _ 8 _ _ storeBound
      (outside ((statePtr s + 96#64).toNat, 8) (by simp [writes]))
  have contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    exact g.state_subspan _ 8 (by rw [at96]; omega) (by rw [at96]; omega)
  have savedOwned : Protected writes (bodySP s).toNat 32 := by
    apply g.saved_protected
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right; left
    simp only [at96]
    constructor <;> omega
  have bufferOwned : Protected writes (statePtr s).toNat 64 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    left
    simp only [at96]
    omega
  have chainOwned : Protected writes (statePtr s + 64#64).toNat 32 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    left
    simp only [at96]
    bv_omega
  have lengthOwned : Protected writes (statePtr s + 104#64).toNat 8 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right
    simp only [at96]
    bv_omega
  refine ⟨⟨activation.advance g (prepare_scalar t ta) ?_ (prepare_sp t ta)
    frame contained savedOwned, outputReg.trans output, stateReg.trans pointer⟩,
    ⟨?_, ?_, ?_⟩, resultCount.trans nextCount, ?_⟩
  · intro reg lo hi h19 h20
    simp only [List.mem_cons, List.mem_singleton]
    bv_omega
  · exact bytesAt_frame frame (by simpa using (show (statePtr s).toNat + 64 ≤ 2^64 by omega))
      (by simpa using bufferOwned) buffer
  · exact chaining.frame frame (by bv_omega) chainOwned
  · rw [read_frame _ 8 frame (by bv_omega) lengthOwned]
    exact length
  · simpa only [pointer, count] using loaded

end SszArm.Hash.Finalize

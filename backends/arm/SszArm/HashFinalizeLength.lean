import SszArm.HashFinalizeControl
import SszArm.HashFinalizeShift

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

theorem length_observe (t : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment t)
    (pc : read_pc t = base + finalizeOffset + 188#64) :
    read_pc (lengthCallState t) = base + compressOffset ∧
    r (.GPR 30#5) (lengthCallState t) = base + finalizeOffset + 216#64 ∧
    r (.GPR 0#5) (lengthCallState t) = r (.GPR 20#5) t + 64#64 ∧
    r (.GPR 1#5) (lengthCallState t) = r (.GPR 20#5) t ∧
    (lengthCallState t).mem =
      (write_mem_bytes 8 (r (.GPR 20#5) t + 56#64)
        (reverse64 (read_mem_bytes 8 (r (.GPR 20#5) t + 104#64) t <<< (3 : Nat))) t).mem := by
  change r .PC t = _ at pc
  simp (config := {decide := true, instances := true})
    [lengthCallState, effect, lengthCallOps, p188, p192, p196, p200, p204, p208, p212,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, pc, finalizeOffset, compressOffset, BitVec.add_assoc,
     rev_vector, ← reverse64, lsl3_ubfm, Memory.write_mem_bytes_eq_mem_write_bytes]

theorem length_step (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (buf : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (owned : FinalizeOwned s base value) (aligned : CheckSPAlignment s)
    (live : Live s t) (stored : BufferAt s t buf words byteLen)
    (pc : read_pc t = base + finalizeOffset + 188#64) :
    Live s (lengthCallState t) ∧
    BufferAt s (lengthCallState t)
      (SszNative.HashStream.overwrite buf 56
        (SszNative.HashStream.finalLengthBytes byteLen) (by simp)) words byteLen ∧
    read_pc (lengthCallState t) = base + compressOffset ∧
    r (.GPR 30#5) (lengthCallState t) = base + finalizeOffset + 216#64 ∧
    r (.GPR 0#5) (lengthCallState t) = statePtr s + 64#64 ∧
    r (.GPR 1#5) (lengthCallState t) = statePtr s := by
  have g := geometry owned
  have physical := g.stateBound
  have ta := live.toActivation.aligned aligned
  obtain ⟨next, link, target, input, memory⟩ := length_observe t base ta pc
  rw [live.state, stored.length] at memory
  have at56 : (statePtr s + 56#64).toNat = (statePtr s).toNat + 56 := by bv_omega
  have storeBound : (statePtr s + 56#64).toNat + 8 ≤ 2^64 := by rw [at56]; omega
  let writes : List Span := [((statePtr s + 56#64).toNat, 8)]
  have frame : MemoryFrame writes t (lengthCallState t) := by
    intro address outside
    rw [memory]
    exact BoolCodec.write_mem_bytes_frame _ _ 8 _ _ storeBound
      (outside ((statePtr s + 56#64).toNat, 8) (by simp [writes]))
  have contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    exact g.state_subspan _ 8 (by rw [at56]; omega) (by rw [at56]; omega)
  have savedOwned : Protected writes (bodySP s).toNat 32 := by
    apply g.saved_protected
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right; left
    simp only [at56]
    constructor <;> omega
  have laterOwned : Protected writes (statePtr s + 64#64).toNat 48 := by
    right
    intro span member
    simp only [writes, List.mem_singleton] at member
    subst span
    right
    simp only [at56]
    bv_omega
  refine ⟨live.advance g (lengthCall_scalar t ta) ?_ (lengthCall_sp t ta)
    frame contained savedOwned, ⟨?_, ?_, ?_⟩, next, link, ?_, ?_⟩
  · intro reg lo hi
    simp only [List.mem_cons, List.mem_singleton]
    bv_omega
  · have bytes := length_store t (statePtr s) buf byteLen (by omega) stored.buffer
    intro i
    change (lengthCallState t).mem _ = _
    rw [memory]
    exact bytes i
  · apply stored.chaining.frame frame (by bv_omega)
    exact protected_subspan laterOwned (Nat.le_refl _) (by omega)
  · rw [read_frame _ 8 frame (by bv_omega) (protected_subspan laterOwned
      (by bv_omega) (by bv_omega))]
    exact stored.length
  · simpa only [live.state] using target
  · simpa only [live.state] using input

end SszArm.Hash.Finalize

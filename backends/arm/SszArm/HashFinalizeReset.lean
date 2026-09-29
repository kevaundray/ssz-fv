import SszArm.HashFinalizeControl

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

def resetMemory (t : ArmState) : ArmState :=
  let sp := r (.GPR 31#5) t - 16#64
  write_mem_bytes 8 (r (.GPR 20#5) t + 96#64) 0#64
    (write_mem_bytes 8 (sp + 8#64) (r (.GPR 10#5) t)
      (write_mem_bytes 8 sp (r (.GPR 9#5) t) t))

theorem reset_observe (t : ArmState) (aligned : CheckSPAlignment t) :
    (resetState t).mem = (resetMemory t).mem ∧
    r (.GPR 0#5) (resetState t) = 0#64 ∧
    read_pc (resetState t) = read_pc t + 44#64 := by
  have lower := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned t aligned)
  simp (config := {decide := true, instances := true})
    [resetState, effect, resetOps, p124, p128, p132, p136, p140, p144, p148, p152,
     p156, p160, p164, resetMemory, Op.effect, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, aligned, lower, BitVec.add_assoc,
     Memory.write_mem_bytes_eq_mem_write_bytes]

theorem reset_step (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (buf : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (owned : FinalizeOwned s base value) (aligned : CheckSPAlignment s)
    (live : Live s t) (stored : BufferAt s t buf words byteLen) :
    Live s (resetState t) ∧ BufferAt s (resetState t) buf words byteLen ∧
    r (.GPR 0#5) (resetState t) = 0#64 ∧
    read_pc (resetState t) = read_pc t + 44#64 := by
  have g := geometry owned
  have physical := g.stateBound
  have low := g.stackLow
  have spNat := g.bodySP_nat
  have apart := g.stateStack
  have ta := live.toActivation.aligned aligned
  obtain ⟨memory, zero, pc⟩ := reset_observe t ta
  let scratch := bodySP s - 16#64
  have scratchNat : scratch.toNat = (stackTop s).toNat - 48 := by
    dsimp [scratch, bodySP]; bv_omega
  have scratchNext : (scratch + 8#64).toNat = scratch.toNat + 8 := by
    have := (stackTop s).isLt; bv_omega
  have scratchBound : scratch.toNat + 16 ≤ 2^64 := by
    have := (stackTop s).isLt; rw [scratchNat]; omega
  have at96 : (statePtr s + 96#64).toNat = (statePtr s).toNat + 96 := by bv_omega
  have storeBound : (statePtr s + 96#64).toNat + 8 ≤ 2^64 := by rw [at96]; omega
  let writes : List Span := [(scratch.toNat, 16), ((statePtr s + 96#64).toNat, 8)]
  have frame : MemoryFrame writes t (resetState t) := by
    intro address outside
    have hs := outside (scratch.toNat, 16) (by simp [writes])
    have hc := outside ((statePtr s + 96#64).toNat, 8) (by simp [writes])
    rw [memory]
    unfold resetMemory
    rw [live.sp, live.state]
    change (write_mem_bytes 8 (statePtr s + 96#64) 0#64
      (write_mem_bytes 8 (scratch + 8#64) (r (.GPR 10#5) t)
        (write_mem_bytes 8 scratch (r (.GPR 9#5) t) t))).mem address = _
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ _ storeBound hc,
      BoolCodec.write_mem_bytes_frame _ _ 8 _ _ (by rw [scratchNext]; omega)
        (by rw [scratchNext]; omega),
      BoolCodec.write_mem_bytes_frame _ _ 8 _ _ (by omega) (by omega)]
  have contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact g.stack_subspan scratch 16 (by rw [scratchNat]; omega) (by rw [scratchNat]; omega)
    · exact g.state_subspan _ 8 (by rw [at96]; omega) (by rw [at96]; omega)
  have savedOwned : Protected writes (bodySP s).toNat 32 := by
    apply g.saved_protected
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · left; simp only [scratchNat]; omega
    · right; left; simp only [at96]; constructor <;> omega
  have bufferOwned : Protected writes (statePtr s).toNat 96 := by
    right
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp only [scratchNat]; omega
    · left; simp only [at96]; omega
  have lengthOwned : Protected writes (statePtr s + 104#64).toNat 8 := by
    right
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp only [scratchNat]; bv_omega
    · right; simp only [at96]; bv_omega
  refine ⟨live.advance g (reset_scalar t ta) ?_ (reset_sp t ta)
    frame contained savedOwned, ⟨?_, ?_, ?_⟩, zero, pc⟩
  · intro reg lo hi
    simp only [List.mem_cons, List.mem_singleton]
    bv_omega
  · exact bytesAt_frame frame (by simpa using (show (statePtr s).toNat + 64 ≤ 2^64 by omega))
      (by simpa using protected_subspan bufferOwned (Nat.le_refl _) (show (statePtr s).toNat + 64 ≤ (statePtr s).toNat + 96 by omega)) stored.buffer
  · apply stored.chaining.frame frame (by bv_omega)
    exact protected_subspan bufferOwned (by bv_omega) (by bv_omega)
  · rw [read_frame _ 8 frame (by bv_omega) lengthOwned]
    exact stored.length

end SszArm.Hash.Finalize

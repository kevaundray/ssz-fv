import SszArm.HashFinalizeEntry
import SszArm.HashFinalizeControl
import SszArm.HashStoreMemory

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

def delimiterMemory (s : ArmState) : ArmState :=
  write_mem_bytes 1 (r (.GPR 1#5) s + r (.GPR 8#5) s) 0x80#8
    (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 10#5) s) s)

theorem delimiter_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (delimiterState s).mem = (delimiterMemory s).mem := by
  have lower := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true})
    [delimiterState, effect, delimiterOps, p24, p28, p32, p36, p40, p44, p48, p52,
     delimiterMemory, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, lower, Memory.write_mem_bytes_eq_mem_write_bytes]

theorem delimiter_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (delimiterState s) = read_pc s + 32#64 := by
  have lower := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true})
    [delimiterState, effect, delimiterOps, p24, p28, p32, p36, p40, p44, p48, p52,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, lower, BitVec.add_assoc]

theorem delimiter_step (s t : ArmState) (base : BitVec 64) (value : StreamState)
    (owned : FinalizeOwned s base value) (aligned : CheckSPAlignment s)
    (activation : Activation s t) (stored : StateAt t (statePtr s) value)
    (pointer : r (.GPR 1#5) t = statePtr s)
    (count : r (.GPR 8#5) t = BitVec.ofNat 64 value.buffered.val) :
    Activation s (delimiterState t) ∧
    BytesAt (delimiterState t) (statePtr s)
      ⟨(SszNative.HashStream.delimiterBuffer value).toArray⟩ ∧
    ChainingAt (delimiterState t) (statePtr s + 64#64) value.chaining ∧
    read_mem_bytes 8 (statePtr s + 96#64) (delimiterState t) = BitVec.ofNat 64 value.buffered.val ∧
    read_mem_bytes 8 (statePtr s + 104#64) (delimiterState t) = value.byteLen.toBitVec := by
  have g := geometry owned
  have physical := g.stateBound
  have low := g.stackLow
  have apart := g.stateStack
  have spNat := g.bodySP_nat
  have bufferedBound := value.buffered.isLt
  have ta := activation.aligned aligned
  let scratch := bodySP s - 16#64
  let target := statePtr s + BitVec.ofNat 64 value.buffered.val
  have scratchNat : scratch.toNat = (stackTop s).toNat - 48 := by dsimp [scratch, bodySP]; bv_omega
  have targetNat : target.toNat = (statePtr s).toNat + value.buffered.val := by
    dsimp [target]; bv_omega
  have scratchBound : scratch.toNat + 8 ≤ 2^64 := by
    rw [scratchNat]; have := (stackTop s).isLt; omega
  have targetBound : target.toNat + 1 ≤ 2^64 := by rw [targetNat]; omega
  let writes : List Span := [(scratch.toNat, 8), (target.toNat, 1)]
  have memory : (delimiterState t).mem =
      (write_mem_bytes 1 target 0x80#8
        (write_mem_bytes 8 scratch (r (.GPR 10#5) t) t)).mem := by
    simpa only [delimiterMemory, pointer, count, activation.sp] using delimiter_memory t ta
  have frame : MemoryFrame writes t (delimiterState t) := by
    intro address outside
    rw [memory]
    rw [BoolCodec.write_mem_bytes_frame _ _ 1 _ _ targetBound
      (outside (target.toNat, 1) (by simp [writes]))]
    exact BoolCodec.write_mem_bytes_frame _ _ 8 _ _ scratchBound
      (outside (scratch.toNat, 8) (by simp [writes]))
  have contained : ∀ span ∈ writes, ∃ outer ∈ finalizeWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact g.stack_subspan scratch 8 (by rw [scratchNat]; omega) (by rw [scratchNat]; omega)
    · exact g.state_subspan target 1 (by rw [targetNat]; omega) (by rw [targetNat]; omega)
  have savedOwned : Protected writes (bodySP s).toNat 32 := by
    apply g.saved_protected
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · left; simp only [scratchNat]; omega
    · right; left; simp only [targetNat]; constructor <;> omega
  have chainOwned : Protected writes (statePtr s + 64#64).toNat 48 := by
    right
    intro span member
    simp only [writes, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp only [scratchNat]; bv_omega
    · simp only [targetNat]; right; bv_omega
  have stateScratch : StateAt (write_mem_bytes 8 scratch (r (.GPR 10#5) t) t)
      (statePtr s) value := by
    apply stored.frame (writes := [(scratch.toNat, 8)])
    · intro address outside
      exact BoolCodec.write_mem_bytes_frame _ _ 8 _ _ scratchBound
        (outside (scratch.toNat, 8) (by simp))
    · exact physical
    · exact g.state_stack scratch 8 (by rw [scratchNat]; omega) (by rw [scratchNat]; omega)
  refine ⟨activation.advance g (delimiter_scalar t ta) ?_ (delimiter_sp t ta)
    frame contained savedOwned, ?_, ?_, ?_, ?_⟩
  · intro reg lo hi h19 h20
    simp only [List.mem_cons, List.mem_singleton]
    bv_omega
  · have bytes := bytesAt_delimiter _ (statePtr s) value (by omega) stateScratch.buffer
    intro i
    change (delimiterState t).mem _ = _
    rw [memory]
    exact bytes i
  · apply stored.chaining.frame frame
    · bv_omega
    · apply protected_subspan chainOwned (Nat.le_refl _)
      omega
  · rw [read_frame _ 8 frame (by bv_omega) (protected_subspan chainOwned
      (by bv_omega) (by bv_omega))]
    exact stored.buffered
  · rw [read_frame _ 8 frame (by bv_omega) (protected_subspan chainOwned
      (by bv_omega) (by bv_omega))]
    exact stored.byteLen

end SszArm.Hash.Finalize

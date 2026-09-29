import SszArm.HashFinalizeScalar
import SszArm.HashFinalizeFrame

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

def entryMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 16#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
    (write_mem_bytes 8 (bodySP s) (r (.GPR 30#5) s) s)

private macro "finalize_entry_simp" : tactic => `(tactic|
  (simp (config := {decide := true, instances := true})
    (disch := first | assumption | decide)
    [entryState, effect, entryOps, p0, p4, p8, p12, Op.effect, exec_inst,
     entryMemory, bodySP, stackTop, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.add_assoc, BitVec.sub_eq_add_neg]
   all_goals arm_state_nf))

theorem entry_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (entryState s).mem = (entryMemory s).mem := by
  have lower := BoolCodec.aligned_sub32 _ (BoolCodec.stack_aligned s aligned)
  finalize_entry_simp
  all_goals simp_all only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem entry_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (entryState s) = bodySP s := by
  have lower := BoolCodec.aligned_sub32 _ (BoolCodec.stack_aligned s aligned)
  finalize_entry_simp

theorem entry_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (entryState s) = read_pc s + 16#64 := by
  have lower := BoolCodec.aligned_sub32 _ (BoolCodec.stack_aligned s aligned)
  finalize_entry_simp

theorem entry_count (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 8#5) (entryState s) = read_mem_bytes 8 (statePtr s + 96#64) (entryState s) := by
  have lower := BoolCodec.aligned_sub32 _ (BoolCodec.stack_aligned s aligned)
  unfold statePtr
  finalize_entry_simp

theorem entry_stack_frame (s : ArmState) (g : Geometry s) (aligned : CheckSPAlignment s) :
    MemoryFrame [((bodySP s).toNat, 32)] s (entryState s) := by
  intro address outside
  have apart := outside ((bodySP s).toNat, 32) (by simp)
  have low := g.stackLow
  have spNat := g.bodySP_nat
  have topBound := (stackTop s).isLt
  have at16 : (bodySP s + 16#64).toNat = (bodySP s).toNat + 16 := by bv_omega
  rw [entry_memory s aligned]
  unfold entryMemory
  rw [BoolCodec.write_mem_bytes_frame _ _ 16 _ _ (by rw [at16]; omega)
      (by rw [at16]; omega),
    BoolCodec.write_mem_bytes_frame _ _ 8 _ _ (by omega) (by omega)]

theorem entry_saved (s : ArmState) (g : Geometry s) (aligned : CheckSPAlignment s) :
    Saved s (entryState s) := by
  have low := g.stackLow
  have spNat := g.bodySP_nat
  have topBound := (stackTop s).isLt
  have at16 : (bodySP s + 16#64).toNat = (bodySP s).toNat + 16 := by bv_omega
  have memory := entry_memory s aligned
  constructor
  · have same : read_mem_bytes 8 (bodySP s) (entryState s) =
        read_mem_bytes 8 (bodySP s) (entryMemory s) := by
      apply BoolCodec.read_bytes_congr
      intro i hi
      change (entryState s).mem _ = (entryMemory s).mem _
      rw [memory]
    rw [same]
    unfold entryMemory
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 16 _ _ _
      (by omega) (by rw [at16]; omega) (by rw [at16]; omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by omega)
  · have same : read_mem_bytes 16 (bodySP s + 16#64) (entryState s) =
        read_mem_bytes 16 (bodySP s + 16#64) (entryMemory s) := by
      apply BoolCodec.read_bytes_congr
      intro i hi
      change (entryState s).mem _ = (entryMemory s).mem _
      rw [memory]
    rw [same]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 16 _ _ (by rw [at16]; omega)

theorem entry_activation (s : ArmState) (base : BitVec 64) (value : StreamState)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : FinalizeOwned s base value) : Activation s (entryState s) := by
  have g := geometry owned
  have scalar := entry_scalar s aligned
  refine ⟨scalar.error.trans error, scalar.program, entry_sp s aligned, ?_, ?_,
    entry_saved s g aligned, ?_⟩
  · intro reg lo hi h19 h20
    exact scalar.registers reg (by simp only [List.mem_cons, List.mem_singleton]; bv_omega)
  · intro reg lo hi
    rw [scalar.vectors reg]
  · apply frame_mono (entry_stack_frame s g aligned)
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    apply g.stack_subspan
    · rw [g.bodySP_nat]; omega
    · rw [g.bodySP_nat]; have := g.stackLow; omega

theorem entry_stored (s : ArmState) (base : BitVec 64) (value : StreamState)
    (aligned : CheckSPAlignment s) (owned : FinalizeOwned s base value) :
    StateAt (entryState s) (statePtr s) value := by
  have g := geometry owned
  apply owned.state.frame (entry_stack_frame s g aligned) owned.stateBound
  apply g.state_stack
  · rw [g.bodySP_nat]; omega
  · rw [g.bodySP_nat]; have := g.stackLow; omega

end SszArm.Hash.Finalize

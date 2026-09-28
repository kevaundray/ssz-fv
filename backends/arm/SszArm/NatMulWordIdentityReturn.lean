import SszArm.NatMulWordIdentityMemory

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Full original entry-through-RET proof for factor one. This borrows precisely
the normalized input prefix and neither allocates nor changes the arena cursor. -/
theorem identity_run (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s operand 1#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand 1#64 := by
  obtain ⟨fuel, u, hu, huf, ready⟩ := identity_ready s base operand hc he ha hp owned
  have currentOwned := huf.return_owned owned.return_owned
  have firstFrame := huf.values owned.return_owned.stack
  have originalAt := NatAdd.operand_at_preserved firstFrame operand owned.operandAt owned.identity_values
  have normalizedAt := SszNative.NatOperand.normalized_at (widthLoad u) operand originalAt
  have normalizedOwned : NatAdd.OperandOwned (valueWrites u) operand.normalized := by
    rw [huf.value_writes]
    exact NatAdd.normalized_owned (valueWrites s) operand owned.identity_values
  have selected : ∃ path : StatusPath,
      read_pc u = base + BitVec.ofNat 64 (valueStart path) ∧
      valuePointer path u = operand.normalized.pointer ∧
      valuePayload path u = operand.normalized.payload := by
    rcases ready with ⟨pc, zero⟩ | ⟨pc, pointer, payload⟩
    · exact ⟨.zeroBorrowed, pc, by simp [valuePointer, zero, SszNative.NatOperand.pointer],
        by simp [valuePayload, zero, SszNative.NatOperand.payload]⟩
    · exact ⟨.borrowed, pc, pointer, payload⟩
  obtain ⟨path, pc, pointer, payload⟩ := selected
  obtain ⟨hrun, returned, image, lastFrame⟩ := value_run_contract path u base
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) pc currentOwned operand.normalized
    pointer payload normalizedAt normalizedOwned
  have frame : MemoryFrame (valueWrites s) s (valueResult path base u) := by
    apply firstFrame.trans
    simpa only [huf.value_writes] using lastFrame
  refine ⟨fuel + ((valueOps path).length + 11), valueResult path base u, ?_, ?_⟩
  · rw [run_plus, hu, hrun]
  · apply identity_post_of_frame s _ operand owned (huf.returned returned) _ frame
    simpa only [huf.registers 0#5 (by decide)] using image

end SszArm.NatMulWord

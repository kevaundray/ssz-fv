import SszArm.NatMulEntryFrame
import SszArm.NatMulDispatch

namespace SszArm.NatMul

/-- The original prologue and both raw-operand scans. The resulting frame
retains the saved caller state and every byte outside the physical144-byte stack. -/
theorem entry_dispatch (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ EntryFrame s t ∧
      DispatchExit s t base left.words right.words ∧
      left.At (UintCodec.widthLoad t) ∧ right.At (UintCodec.widthLoad t) := by
  have first := entry_activation s owned.stackBound
  have operands := activated_operands owned
  have firstPC : read_pc (activated s) = base + 28#64 := by
    rw [activated_pc, pc]
    simp only [entry, BitVec.ofNat_zero, BitVec.add_zero]
  obtain ⟨fuel, t, execution, scan, exit⟩ := dispatch (activated s) base left.words right.words
    (first.code code) (first.error.trans error) (first.aligned aligned) firstPC operands.1 operands.2
  have frame := first.dispatch owned.stackBound scan
  refine ⟨7 + fuel, t, ?_, frame, ?_, ?_, ?_⟩
  · rw [run_plus, save_run s base code error aligned
      (by simpa only [entry, BitVec.ofNat_zero, BitVec.add_zero] using pc), execution]
  · simpa only [DispatchExit, RawArgs,
      activated_registers s 1#5 (by decide), activated_registers s 2#5 (by decide),
      activated_registers s 3#5 (by decide), activated_registers s 4#5 (by decide)] using exit
  · exact NatAdd.operand_at_preserved (frame.memoryFor (outcome s left right))
      left owned.leftAt owned.leftOwned
  · exact NatAdd.operand_at_preserved (frame.memoryFor (outcome s left right))
      right owned.rightAt owned.rightOwned

end SszArm.NatMul

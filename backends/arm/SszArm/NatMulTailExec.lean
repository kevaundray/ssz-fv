import SszArm.NatMulTailPost
import SszArm.NatMulWordProofs

namespace SszArm.NatMul

/-- Restores the original caller frame, executes the real B at260, and invokes
the complete word helper at its linked image offset. -/
theorem tail_checkpoint_run (s u : ArmState) (base : BitVec 64)
    (left right operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s left right) (frame : EntryFrame s u)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc u = base + 232#64)
    (pointer : r (.GPR 1#5) u = operand.pointer)
    (payload : r (.GPR 2#5) u = operand.payload)
    (factorRegister : r (.GPR 3#5) u = factor)
    (input : operand.At (UintCodec.widthLoad s))
    (inputOwned : NatAdd.OperandOwned (writesFor s (outcome s left right)) operand)
    (model : outcome s left right = SszNative.NatMul.runWord operand factor
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used) :
    ∃ fuel t, run fuel u = t ∧ Post s t left right := by
  let v := restored .tail u base
  have tailFrame : TailFrame s v := frame.tail base
  obtain ⟨vpc, _, v1, v2, v3, _, _, _⟩ := tail_restored s u base frame.saved
  have wordOwned : NatMulWord.Owned v operand factor :=
    tailFrame.word_owned owned operand factor (v1.trans pointer) (v2.trans payload)
      (v3.trans factorRegister) input inputOwned model
  have wordCode := code.transport tailFrame.program
  have wordAligned : CheckSPAlignment v :=
    block_aligned base RestorePath.tail.ops u (frame.aligned aligned)
  have wordPC : read_pc v = base + wordOffset + BitVec.ofNat 64 NatMulWord.entry := by
    simpa only [NatMulWord.entry, BitVec.add_zero] using vpc
  obtain ⟨fuel, t, execution, post⟩ := NatMulWord.program_correct v (base + wordOffset)
    operand factor wordCode.word (tailFrame.error.trans error) wordAligned wordOwned wordPC
  have restoreRun : run 8 u = v := restore_run .tail u base (frame.code code.body)
    (frame.error.trans error) (frame.aligned aligned) pc
  refine ⟨8 + fuel, t, ?_, tailFrame.post owned operand factor model post⟩
  rw [run_plus, restoreRun, execution]

end SszArm.NatMul

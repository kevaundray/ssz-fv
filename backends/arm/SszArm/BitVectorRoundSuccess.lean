import SszArm.BitVectorHelperResources
import SszArm.BitVectorRoundedOwned
import SszArm.BitVectorModel

namespace SszArm.BitVector

open UintCodec (widthLoad)

theorem round_success_expected {s c d : ArmState} {base : BitVec 64}
    {length quotient expected : SszNative.NatOperand} {data : Ssz.Bytes} {remainder : BitVec 64}
    (owned : Owned s length data) (current : Counted s d length remainder)
    (post : NatAdd.Post (roundEntry c base) d quotient (.small 1))
    (args : RoundArguments s (roundEntry c base) length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0#64) (addition : (rounding s length quotient).result = .ok expected)
    (resources : Resources s d length data)
    (before : Delimited.MemoryFrame (writesFor s (outcome s length data)) s d)
    (code : JointCodeAt d base) (aligned : CheckSPAlignment s)
    (pc : read_pc d = base + 3416#64) :
    ∃ fuel t, run fuel d = t ∧ ExpectedAt s t base length expected remainder data := by
  have stored := post.result
  rw [args.model, addition, args.output] at stored
  change SszNative.NatArithmetic.operandAt (widthLoad d)
      (r (.GPR 31#5) s + 144#64).toNat expected ∧
    widthLoad d ((r (.GPR 31#5) s + 144#64).toNat + 64) 4 = some 0 at stored
  have status : read_mem_bytes 4 (r (.GPR 31#5) s + 208#64) d = 0#32 := by
    simpa only [BitVec.add_assoc, show 144#64 + 64#64 = 208#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 64 4 0#32 stored.2
  let tested := ExpectedStage.Stage.rounding.result d base
  have testedRun : run 2 d = tested := ExpectedStage.executes .rounding d base code.body
    current.error (current.toWorking.aligned aligned) pc
  have testedCurrent := current.after_expected .rounding base
  have testedFrame := expected_frame owned current.toWorking .rounding base
  have testedCode : JointCodeAt tested base := by
    rw [← testedRun]
    exact code.run 2
  have testedPC : read_pc tested = base + 5940#64 := by
    simp (config := {decide := true}) only [tested, ExpectedStage.Stage.result, state_simp_rules,
      current.sp, status, show (0#32 : BitVec 32) = 0 by rfl, if_pos]
  have observe : widthLoad tested = widthLoad d := by
    funext address bytes
    simp only [tested, widthLoad, ExpectedStage.Stage.result, state_simp_rules]
  have testedPair : SszNative.NatArithmetic.operandAt (widthLoad tested)
      (r (.GPR 31#5) s + 144#64).toNat expected := by
    rw [observe]
    exact stored.1
  let final := ExpectedStage.Stage.rounded.result tested base
  have copiedRun : run 2 tested = final := ExpectedStage.executes .rounded tested base testedCode.body
    testedCurrent.error (testedCurrent.toWorking.aligned aligned) testedPC
  have copiedCurrent := testedCurrent.after_expected .rounded base
  have copiedFrame := expected_frame owned testedCurrent.toWorking .rounded base
  have limbs := rounded_local_owned owned division nonzero addition
  have pair := rounded_expected_pair (base := base) owned testedCurrent.toWorking testedPair limbs
  have whole : run 4 d = final := by
    change run (2 + 2) d = final
    rw [run_plus, testedRun, copiedRun]
  refine ⟨4, final, whole, copiedCurrent, ?_, ?_, pair, limbs, ?_, ?_,
    (resources.after_local owned testedFrame).after_local owned copiedFrame,
    (before.trans ((local_covered s (outcome s length data)).frame testedFrame)).trans
      ((local_covered s (outcome s length data)).frame copiedFrame)⟩
  · simp only [final, ExpectedStage.Stage.result, state_simp_rules]
  · rw [← whole]
    exact code.run 4
  · exact SszNative.BitVector.expected_of_round length quotient expected remainder
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used division nonzero addition
  · exact round_success_model s length quotient expected remainder data division nonzero addition

end SszArm.BitVector

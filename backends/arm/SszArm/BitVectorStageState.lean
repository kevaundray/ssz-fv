import SszArm.BitVectorFrame

namespace SszArm.BitVector

theorem Working.after_call {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (site : CallSite) (base : BitVec 64) :
    Working s (called site c base) length := by
  refine ⟨by simpa only [called_error] using current.error, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.sp
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.output
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.input
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.size
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.pointer
  · simpa (config := {decide := true}) [called, state_simp_rules] using current.payload
  · intro reg low high
    simpa (config := {decide := true}) [called, state_simp_rules] using current.vectors reg low high

theorem Working.after_status {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (base : BitVec 64) :
    Working s (Block.divisionStatusResult c base) length := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.error
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.sp
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.output
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.input
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.size
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.pointer
  · simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.payload
  · intro reg low high
    simpa (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules] using current.vectors reg low high

theorem Working.after_expected {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (stage : ExpectedStage.Stage) (base : BitVec 64) :
    Working s (stage.result c base) length := by
  cases stage
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.error
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.sp
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.output
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.input
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.size
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.pointer
    · simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.payload
    · intro reg low high
      simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.vectors reg low high

/-- X25 retains the actual division remainder across rounding, exact, and
narrowing. It is not replaced by a value-width or canonicality assumption. -/
structure Counted (s t : ArmState) (length : SszNative.NatOperand) (remainder : BitVec 64)
    extends Working s t length : Prop where
  remainderValue : r (.GPR 25#5) t = remainder

theorem Working.status_counted {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (base : BitVec 64) (remainder : BitVec 64)
    (loaded : read_mem_bytes 8 (r (.GPR 31#5) c + 160#64) c = remainder) :
    Counted s (Block.divisionStatusResult c base) length remainder := by
  refine ⟨current.after_status base, ?_⟩
  simp (config := {decide := true}) [Block.divisionStatusResult, state_simp_rules, loaded]

theorem Counted.after_call {s c : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (site : CallSite) (base : BitVec 64) :
    Counted s (called site c base) length remainder := by
  refine ⟨current.toWorking.after_call site base, ?_⟩
  simpa (config := {decide := true}) [called, state_simp_rules] using current.remainderValue

theorem Counted.after_return {s c t : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (returned : Delimited.Returned c t) :
    Counted s t length remainder := by
  exact ⟨current.toWorking.after_return returned,
    (returned.registers 25#5 (by decide) (by decide)).trans current.remainderValue⟩

theorem Counted.after_preparation {s c : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (phase : Stages.CallPreparation) (base : BitVec 64)
    (normal : phase = .round ∨ phase = .scope ∨ phase = .narrow) :
    Counted s (phase.result c base) length remainder := by
  refine ⟨current.toWorking.after_preparation phase base normal, ?_⟩
  rcases normal with rfl | rfl | rfl <;>
    simpa (config := {decide := true}) [Stages.CallPreparation.result, state_simp_rules] using current.remainderValue

theorem Counted.after_expected {s c : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (stage : ExpectedStage.Stage) (base : BitVec 64) :
    Counted s (stage.result c base) length remainder := by
  refine ⟨current.toWorking.after_expected stage base, ?_⟩
  cases stage <;>
    simpa (config := {decide := true}) [ExpectedStage.Stage.result, state_simp_rules] using current.remainderValue

end SszArm.BitVector

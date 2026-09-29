import SszArm.CodecDecodeBoundedErrorFields
import SszArm.CodecDecodeBoundedPreservation

namespace SszArm.Codec.Decode.Bounded

open Delimited (MemoryFrame)

@[simp] theorem error_stage_output (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    r (.GPR 19#5) (stage.result s base) = r (.GPR 19#5) s :=
  error_stage_register stage s base _ (by decide)

@[simp] theorem error_stage_actual (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    r (.GPR 20#5) (stage.result s base) = r (.GPR 20#5) s :=
  error_stage_register stage s base _ (by decide)

@[simp] theorem error_stage_writes (stage : ErrorStage) (s : ArmState) (base : BitVec 64) :
    errorWrites (stage.result s base) = errorWrites s := by
  simp only [errorWrites, error_stage_sp, error_stage_output]

theorem ErrorSpace.stage {s : ArmState} (space : ErrorSpace s)
    (stage : ErrorStage) (base : BitVec 64) : ErrorSpace (stage.result s base) := by
  obtain ⟨stack, output, apart⟩ := space
  refine ⟨?_, ?_, ?_⟩
  · simpa only [error_stage_sp] using stack
  · simpa only [error_stage_output] using output
  · simpa only [error_stage_sp, error_stage_output] using apart

/-- The failure branch's final physical state, after all stores and its real RET. -/
@[irreducible] def errorState (s : ArmState) (base : BitVec 64) : ArmState :=
  restored (ErrorStage.actual.result
    (ErrorStage.tag.result (ErrorStage.expected.result s base) base) base)

theorem error_state_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 68#64) : run 32 s = errorState s base := by
  simpa only [errorState] using error_run s base code error aligned pc

theorem error_state_frame (s : ArmState) (base : BitVec 64) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (errorState s base) := by
  let a := ErrorStage.expected.result s base
  let b := ErrorStage.tag.result a base
  let c := ErrorStage.actual.result b base
  have af := error_stage_frame .expected s base space.stack space.output
  have aSpace := space.stage .expected base
  have bf : MemoryFrame (errorWrites s) a b := by
    simpa only [a, error_stage_writes] using error_stage_frame .tag a base aSpace.stack aSpace.output
  have bSpace := aSpace.stage .tag base
  have cf : MemoryFrame (errorWrites s) b c := by
    simpa only [b, a, error_stage_writes] using error_stage_frame .actual b base bSpace.stack bSpace.output
  intro address outside
  change (restored c).mem address = s.mem address
  rw [restored_memory]
  exact ((af.trans bf).trans cf) address outside

@[simp] theorem error_state_program (s : ArmState) (base : BitVec 64) :
    (errorState s base).program = s.program := by simp [errorState]

@[simp] theorem error_state_error (s : ArmState) (base : BitVec 64) :
    read_err (errorState s base) = read_err s := by simp [errorState]

@[simp] theorem error_state_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (errorState s base) = r (.GPR 31#5) s + 48#64 := by simp [errorState]

@[simp] theorem error_state_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (errorState s base) = r (.SFP reg) s := by
  simp only [errorState, restored_vector, error_stage_vector]

end SszArm.Codec.Decode.Bounded

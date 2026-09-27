import SszArm.NatDivisionFailure
import SszArm.NatDivisionSerialize
import SszArm.NatDivisionPost

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem failure_ready (s : ArmState) (base : BitVec 64) (space : ReturnSpace s) :
    ReturnReady (failureResult base s) (.error .scratchExhausted) := by
  have owned : FailureOwned s := ⟨space.stackLow, space.outputHigh, by
    have apart := space.separate
    omega⟩
  have args := failure_arguments s base owned
  have image := failure_image s base owned
  have out := failure_registers s base 19#5 (by decide)
  refine ⟨args.2.2.1, args.1, ?_, ?_, ?_⟩
  · rw [args.2.1]
    rfl
  · rw [out]
    exact image.1
  · intro n member
    rw [out]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact image.2.1
    · exact image.2.2.1
    · exact image.2.2.2.1
    · exact image.2.2.2.2.1
    · exact image.2.2.2.2.2.1
    · exact image.2.2.2.2.2.2

/-- Once a proved reservation failure reaches pc812, every remaining native
instruction through RET is executed. No cursor or quotient memory is written. -/
theorem failure_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned original operand)
    (saved : Saved original s) (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 812#64)
    (failed : (outcome original operand).result = .error .scratchExhausted)
    (before : MemoryFrame (localWrites original) original s) :
    Post original (run 54 s) operand := by
  have space := owned.return_space saved.sp out
  have localOwned : FailureOwned s := ⟨space.stackLow, space.outputHigh, by
    have apart := space.separate
    omega⟩
  have unchanged : outcome original operand =
      SszNative.NatArithmetic.unchanged (arenaOf original).used (.error .scratchExhausted) :=
    SszNative.NatDivision.failure_unchanged operand (r (.GPR 3#5) original)
      (arenaOf original).base (arenaOf original).capacity (arenaOf original).used
      .scratchExhausted failed
  have currentSP : (r (.GPR 31#5) s).toNat + 64 = (r (.GPR 31#5) original).toNat := by
    have stack := owned.stackBound
    rw [saved.sp]
    bv_omega
  have localFrame := failure_local_frame original s base localOwned out currentSP
  have fullFrame := before.trans localFrame
  have savedAfter : Saved original (failureResult base s) := by
    apply saved.output_preserved owned.stackBound space (failure_frame s base localOwned)
    · exact failure_sp s base
    · intro reg low high
      apply failure_registers
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      bv_omega
    · intro reg low high
      simp [failureResult, failureOps, block, Op.effect, put, next, state_simp_rules]
  have outAfter : r (.GPR 19#5) (failureResult base s) = r (.GPR 0#5) original :=
    (failure_registers s base 19#5 (by decide)).trans out
  have code : CodeAt (failureResult base s) base := by
    simpa only [failureResult, CodeAt, block_program] using hc
  have error : read_err (failureResult base s) = .None := (block_error _ _ _).trans he
  have aligned : CheckSPAlignment (failureResult base s) := block_aligned _ _ _ ha
  have ready : ReturnReady (failureResult base s) (outcome original operand).result := by
    rw [failed]
    exact failure_ready s base space
  have written : WrittenAt (widthLoad (failureResult base s)) (outcome original operand) := by
    rw [unchanged]
    intro reservation impossible
    cases impossible
  have cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64)
      (failureResult base s)).toNat = (outcome original operand).used := by
    have physical := owned.arenaBound
    have address : (r (.GPR 4#5) original + 16#64).toNat =
        (r (.GPR 4#5) original).toNat + 16 := by bv_omega
    rw [fullFrame.read _ 8 (by rw [address]; omega)]
    · rw [unchanged]
      rfl
    · rw [address]
      exact owned.arenaLocal.subspan 16 8 (by decide)
  rw [show 54 = 41 + 13 by decide, run_plus, failure_run s base hc he ha hp]
  exact finish_post original _ base operand owned savedAfter outAfter code error aligned
    (failure_pc s base hp) ready written cursor (local_frame (outcome original operand) fullFrame)

end SszArm.NatDivision

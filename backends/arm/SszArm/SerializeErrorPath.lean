import SszArm.SerializeErrorPathGeometry
import SszArm.SerializePost

namespace SszArm.Serialize

open SszNative.Serialize (Desc Value Error)
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

/-- Actual PC52 staging, status dispatch, full 72-byte error copy, saved-register
reloads and RET. Every storage and payload obligation comes from original ownership. -/
theorem measurement_error_correct (s m : ArmState) (base : BitVec 64)
    (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) (reason : Error)
    (failure : (measured s (Args.ofEntry s) desc value).result = .error reason) :
    ∃ fuel t, run fuel m = t ∧ Post s t desc value := by
  have space := ErrorPath.measure_space owned measurement
  have input := ErrorPath.plan_error owned measurement reason failure
  have status := ErrorPath.error_status input
  have localWrites := ErrorPath.measure_writes owned measurement
  have covered : Covers (Finish.measureWrites m)
      (stackSpans (Args.ofEntry s) ++ externalSpans (Args.ofEntry s)) := by
    rw [localWrites]
    exact ErrorPath.writes_covered _
  have payload := owned.measured_error_owned reason failure
  have errorAt := Finish.measure_error_at base m space reason input
    (operand_owned_of_covers covered _ payload.1)
    (operand_owned_of_covers covered _ payload.2)
  have copiedFrame : MemoryFrame (ErrorPath.writes (Args.ofEntry s)) m
      (Finish.measureCopied base m) := by
    rw [← localWrites]
    exact Finish.measure_copy_frame base m space
  have saved : Finish.SavedFrom s (Finish.measureCopied base m) := by
    apply measurement.savedFrom.of_frame copiedFrame (Finish.measure_copied_sp base m)
      space.stackHigh
    · have coordinate : (Finish.sp m).toNat + 96 = (Args.ofEntry s).stack.toNat - 48 := by
        change (r (.GPR 31#5) m).toNat + 96 = _
        rw [measurement.registers.stack, bodySP_toNat _ (by have low := owned.stackLow; omega)]
        have low := owned.stackLow
        omega
      rw [coordinate]
      exact ErrorPath.saved_protected owned
    · intro reg low high outside
      apply Finish.measure_copied_register
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      repeat' constructor
      all_goals intro same; bv_omega
    · intro reg low high
      rw [Finish.measure_copied_vector]
  have returned : Emit.Returned s (Finish.measureReturned base m) :=
    Finish.returned_original s (Finish.measureCopied base m) saved
      ((Finish.measure_copied_program base m).trans measurement.program)
      ((Finish.measure_copied_error base m).trans measurement.error)
  have continuationFrame : MemoryFrame (ErrorPath.writes (Args.ofEntry s)) m
      (Finish.measureReturned base m) := by
    rw [← localWrites]
    exact Finish.measure_return_frame base m space
  have resources := Resources.of_frame owned measurement.resources continuationFrame
    (ErrorPath.writes_covered (Args.ofEntry s))
  have totalFrame : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s
      (Finish.measureReturned base m) := by
    have before : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s m :=
      measurement.frame.weaken (by
        intro span member
        rw [ErrorPath.exact_writes reason failure]
        exact List.mem_append.mpr (Or.inl member))
    have after : MemoryFrame (writesFor s (Args.ofEntry s) desc value) m
        (Finish.measureReturned base m) := continuationFrame.weaken (by
      intro span member
      rw [ErrorPath.exact_writes reason failure]
      exact List.mem_append.mpr (Or.inr member))
    exact before.trans after
  have reduced := outcome_of_measure_error s (Args.ofEntry s) desc value reason failure
  refine ⟨21, Finish.measureReturned base m,
    Finish.measure_return_run base m measurement.code measurement.error measurement.aligned
      measurement.pc status, ?_⟩
  apply post_of_return s (Finish.measureReturned base m) desc value owned returned
  · rw [reduced]
    change Measure.ErrorAt (widthLoad (Finish.measureReturned base m))
      (Args.ofEntry s).result.toNat reason
    simpa only [Finish.result, measurement.registers.result] using errorAt
  · rw [reduced]
    exact resources.cursor
  · exact resources.header
  · rw [reduced]
    exact resources.written
  · rw [reduced]
    intro index within
    simp only [Array.size_empty, Nat.not_lt_zero] at within
  · exact totalFrame

end SszArm.Serialize

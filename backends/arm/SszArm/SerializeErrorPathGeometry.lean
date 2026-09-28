import SszArm.SerializeResources
import SszArm.SerializeOwnershipResult
import SszArm.SerializeFinishMeasure
import SszArm.SerializeSaved

namespace SszArm.Serialize.ErrorPath

open SszNative.Serialize (Desc Value Error)
open Delimited (Span Protected MemoryFrame)

/-- The error continuation stages two words and copies the entire returned Plan. -/
def writes (args : Args) : List Span :=
  [(args.stack.toNat - 136, 16), (args.result.toNat, 72)]

theorem writes_covered (args : Args) :
    Covers (writes args) (stackSpans args ++ externalSpans args) := by
  intro span member
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [externalSpans], Nat.le_refl _, Nat.le_refl _⟩

theorem exact_writes {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (reason : Error) (failure : (measured s args desc value).result = .error reason) :
    writesFor s args desc value =
      (saveWrites args ++ Measure.writesFor args.measure (measured s args desc value)) ++
        writes args := by
  simp only [writesFor, afterMeasureWrites, continuationWrites, failure, List.append_nil,
    writes, List.cons_append, List.nil_append]

theorem measure_writes {s m : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) :
    Finish.measureWrites m = writes (Args.ofEntry s) := by
  have coordinate : (Args.ofEntry s).bodySP.toNat + 8 =
      (Args.ofEntry s).stack.toNat - 136 := by
    rw [bodySP_toNat _ (by have low := owned.stackLow; omega)]
    have low := owned.stackLow
    omega
  simp only [Finish.measureWrites, Finish.sp, Finish.result, measurement.registers.stack,
    measurement.registers.result, coordinate, writes]

theorem measure_space {s m : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) : Finish.MeasureSpace m := by
  have stack : Finish.sp m = (Args.ofEntry s).bodySP := measurement.registers.stack
  have target : Finish.result m = (Args.ofEntry s).result := measurement.registers.result
  have low := owned.stackLow
  have high := (Args.ofEntry s).stack.isLt
  have stackNat : (Finish.sp m).toNat = (Args.ofEntry s).stack.toNat - 144 := by
    rw [stack, bodySP_toNat _ (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [stackNat]
    omega
  · simpa only [target] using owned.resultBound
  · rw [stackNat, target]
    rcases owned.resultStack with empty | separate
    · omega
    · have staging := separate ((Args.ofEntry s).stack.toNat - 136, 16) (by simp [stackSpans])
      have plan := separate ((Args.ofEntry s).stack.toNat - 120, 72) (by simp [stackSpans])
      have saves := separate ((Args.ofEntry s).stack.toNat - 48, 48) (by simp [stackSpans])
      dsimp at staging plan saves
      omega

theorem plan_error {s m : ArmState} {base : BitVec 64} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) (reason : Error)
    (failure : (measured s (Args.ofEntry s) desc value).result = .error reason) :
    Measure.ErrorAt (UintCodec.widthLoad m) ((Finish.sp m).toNat + 24) reason := by
  have address : (Args.ofEntry s).plan.toNat = (Finish.sp m).toNat + 24 := by
    change _ = (r (.GPR 31#5) m).toNat + 24
    rw [measurement.registers.stack, plan_toNat _ (by have low := owned.stackLow; omega),
      bodySP_toNat _ (by have low := owned.stackLow; omega)]
    have low := owned.stackLow
    omega
  rw [← address]
  simpa only [failure, Measure.ResultAt] using measurement.result

theorem error_status {m : ArmState} {reason : Error}
    (input : Measure.ErrorAt (UintCodec.widthLoad m) ((Finish.sp m).toNat + 24) reason) :
    read_mem_bytes 4 (Finish.sp m + 88#64) m ≠ 0#32 := by
  have status : (read_mem_bytes 4 (Finish.sp m + 88#64) m).toNat =
      Measure.errorCode reason := by
    have address : BitVec.ofNat 64 ((Finish.sp m).toNat + 24 + 64) =
        Finish.sp m + 88#64 := by bv_omega
    have observed := Option.some.inj input.2.2.2.2.2.2
    change (read_mem_bytes 4 (BitVec.ofNat 64 ((Finish.sp m).toNat + 24 + 64)) m).toNat =
      Measure.errorCode reason at observed
    rw [address] at observed
    exact observed
  have positive : 0 < Measure.errorCode reason := by
    cases reason with
    | arithmetic cause => cases cause <;> simp [Measure.errorCode]
    | _ => simp [Measure.errorCode]
  intro zero
  have observation := congrArg BitVec.toNat zero
  rw [status] at observation
  exact (Nat.ne_of_gt positive) observation

/-- The wrapper copy cannot alias the six words reloaded by the actual epilogue. -/
theorem saved_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Protected (writes args) (args.stack.toNat - 48) 48 := by
  have low := owned.stackLow
  right
  intro span member
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · right
    dsimp
    omega
  · rcases owned.resultStack with empty | separate
    · omega
    · have apart := separate (args.stack.toNat - 48, 48) (by simp [stackSpans])
      dsimp at apart ⊢
      omega

end SszArm.Serialize.ErrorPath

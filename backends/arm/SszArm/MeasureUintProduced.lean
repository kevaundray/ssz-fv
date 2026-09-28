import SszArm.MeasureResultProduced
import SszArm.MeasureOwnership
import SszArm.MeasureUintValueFrame

namespace SszArm.Measure.Uint

open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)

theorem scan_local_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (stack : r (.GPR 31#5) s = args.bodySP)
    (frame : NatNarrow.Frame s t) :
    MemoryFrame (localWrites args (outcome s args desc value)) s t := by
  have stackNat : (r (.GPR 31#5) s).toNat = args.stack.toNat - 272 := by
    rw [stack]
    unfold Args.bodySP
    have safe := owned.stackLow
    bv_omega
  apply frame.memoryFrame
  · simp [localWrites, stackWrites, bodyStackWrites, stackNat, Nat.sub_sub]
  · rw [stackNat]
    have safe := owned.stackLow
    omega

theorem scan_body_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (stack : r (.GPR 31#5) s = args.bodySP)
    (frame : NatNarrow.Frame s t) :
    MemoryFrame (bodyWrites args (outcome s args desc value)) s t := by
  have stackNat : (r (.GPR 31#5) s).toNat = args.stack.toNat - 272 := by
    rw [stack]
    unfold Args.bodySP
    have safe := owned.stackLow
    bv_omega
  apply frame.memoryFrame
  · simp [bodyWrites, bodyStackWrites, stackNat, Nat.sub_sub]
  · rw [stackNat]
    have safe := owned.stackLow
    omega

/-- Prepending an actual scratch-only scan preserves the pinned original
semantic outcome; the writer's result is not a future-state assumption. -/
theorem produced_prepend_scan {s u t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (owned : Owned s args desc value)
    (stack : r (.GPR 31#5) s = args.bodySP) (frame : NatNarrow.Frame s u)
    (after : Produced u t args desc value base) : Produced s t args desc value base := by
  have localFrame := scan_local_frame owned stack frame
  have sameArena := arenaOf_eq_of_local_frame owned localFrame
  have sameOutcome : outcome u args desc value = outcome s args desc value :=
    outcome_eq_of_arena_eq sameArena
  have header0 := Emit.frame_read_offset localFrame args.arena 24 0 8 owned.arenaBound
    owned.headerLocal (by decide)
  have header8 := Emit.frame_read_offset localFrame args.arena 24 8 8 owned.arenaBound
    owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at header0
  refine { after with
    program := after.program.trans frame.program
    result := ?_
    cursor := ?_
    header := ⟨after.header.1.trans header0, after.header.2.trans header8⟩
    written := ?_
    frame := ?_
    registers := ?_
    vectors := ?_ }
  · simpa only [sameOutcome] using after.result
  · simpa only [sameOutcome] using after.cursor
  · simpa only [sameOutcome] using after.written
  · exact (scan_body_frame owned stack frame).trans (by simpa only [sameOutcome] using after.frame)
  · intro reg member
    have outside : reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (after.registers reg member).trans (frame.registers reg outside)
  · intro reg low high
    rw [after.vectors reg low high, frame.vectors]

end SszArm.Measure.Uint

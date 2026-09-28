import SszArm.MeasureMemory

namespace SszArm.Measure

open SszNative.Serialize (Desc Value)
open Delimited (Span Protected MemoryFrame)

theorem arenaOf_eq_of_local_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (localWrites args (outcome s args desc value)) s t) :
    arenaOf t args = arenaOf s args := by
  have r0 := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r8 := Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r16 := Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound
    owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at r0
  simp only [arenaOf, r0, r8, r16]

theorem outcome_eq_of_arena_eq {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (same : arenaOf t args = arenaOf s args) :
    outcome t args desc value = outcome s args desc value := by
  simp only [outcome, same]

/-- Transport requires original arena observations when the permitted frame also
contains the cursor. This premise is discharged from the narrower local frame
by of_local_frame, rather than asserted after an allocating body. -/
theorem Owned.of_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t)
    (sameArena : arenaOf t args = arenaOf s args) : Owned t args desc value := by
  have sameOutcome : outcome t args desc value = outcome s args desc value :=
    outcome_eq_of_arena_eq sameArena
  refine { owned with
    descriptor := descriptor_preserved owned frame
    value_at := value_preserved owned frame
    resultBound := ?_
    storageBound := ?_
    nonnull := ?_
    resultStack := ?_
    headerLocal := ?_
    freeLocal := ?_
    descriptorOwned := ?_
    valueOwned := ?_
    operandOwned := ?_
    backingOwned := ?_ }
  · simpa only [sameOutcome] using owned.resultBound
  · simpa only [sameArena] using owned.storageBound
  · simpa only [sameArena] using owned.nonnull
  · simpa only [sameOutcome] using owned.resultStack
  · simpa only [sameOutcome] using owned.headerLocal
  · simpa only [sameOutcome, sameArena] using owned.freeLocal
  · simpa only [sameOutcome] using owned.descriptorOwned
  · simpa only [sameOutcome] using owned.valueOwned
  · simpa only [sameOutcome] using owned.operandOwned
  · simpa only [sameOutcome, backing_preserved owned frame] using owned.backingOwned

theorem Owned.of_local_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (localWrites args (outcome s args desc value)) s t) :
    Owned t args desc value := by
  apply owned.of_frame
    (frame.weaken (fun span member => List.mem_append.mpr (Or.inl member)))
  exact arenaOf_eq_of_local_frame owned frame

theorem Owned.of_save_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (saveWrites args) s t) :
    Owned t args desc value := by
  apply owned.of_local_frame (frame.weaken ?_)
  intro span member
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))

theorem arenaOf_eq_of_save_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (saveWrites args) s t) :
    arenaOf t args = arenaOf s args := by
  apply arenaOf_eq_of_local_frame owned (frame.weaken ?_)
  intro span member
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))

end SszArm.Measure

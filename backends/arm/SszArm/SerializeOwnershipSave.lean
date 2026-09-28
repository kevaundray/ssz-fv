import SszArm.SerializeOwnershipMeasure
import SszArm.SerializePostObservations

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open Delimited (Span Protected MemoryFrame)

theorem save_writes_covered (s : ArmState) (args : Args) :
    Covers (saveWrites args) (writable s args) := by
  apply (save_covered args).trans
  exact Covers.of_subset (fun span member =>
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))

theorem arenaOf_eq_of_save_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (saveWrites args) s t) :
    arenaOf t args = arenaOf s args := by
  have header : Protected (saveWrites args) args.arena.toNat 24 := by
    apply protected_of_covers owned.arenaOwned
    apply (save_covered args).trans
    exact Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member))
  have r0 := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound header (by decide)
  have r8 := Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound header (by decide)
  have r16 := Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound header (by decide)
  simp only [BitVec.add_zero] at r0
  simp only [arenaOf, Measure.arenaOf, Args.measure, r0, r8, r16]

theorem Owned.of_save_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (saveWrites args) s t) :
    Owned t args desc value := by
  have sameArena := arenaOf_eq_of_save_frame owned frame
  have sameFree : freeSpan t args = freeSpan s args := by simp only [freeSpan, sameArena]
  have sameWritable : writable t args = writable s args := by simp only [writable, sameFree]
  have full := frame_of_covers frame (save_writes_covered s args)
  refine { owned with
    descriptor := descriptor_preserved owned full
    value_at := value_preserved owned full
    storageBound := ?_
    nonnull := ?_
    freeOwned := ?_
    descriptorOwned := ?_
    valueOwned := ?_
    operandOwned := ?_
    backingOwned := ?_ }
  · simpa only [sameArena] using owned.storageBound
  · simpa only [sameArena] using owned.nonnull
  · simpa only [sameFree] using owned.freeOwned
  · simpa only [sameWritable] using owned.descriptorOwned
  · simpa only [sameWritable] using owned.valueOwned
  · simpa only [sameWritable] using owned.operandOwned
  · simpa only [sameWritable, backing_preserved owned full] using owned.backingOwned

theorem Owned.measure_of_save_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (saveWrites args) s t) :
    Measure.Owned t args.measure desc value := (owned.of_save_frame frame).measure

theorem measure_local_before_save (args : Args) (first : Outcome NatOperand)
    (low : 432 ≤ args.stack.toNat) :
    ∀ span ∈ Measure.localWrites args.measure first, span.1 + span.2 ≤ args.stack.toNat - 48 := by
  have stack := bodySP_toNat args (by omega)
  intro span member
  rcases List.mem_append.mp member with stackMember | resultMember
  · simp only [Measure.stackWrites, Measure.saveWrites, Measure.bodyStackWrites,
      Args.measure, stack, List.mem_append, List.mem_singleton] at stackMember
    rcases stackMember with saved | lowering | conditional
    · subst span; dsimp; omega
    · subst span; dsimp; omega
    · split at conditional
      · simp only [List.mem_singleton] at conditional
        subst span; dsimp; omega
      · simp only [List.not_mem_nil] at conditional
  · obtain ⟨outer, outerMember, lower, upper⟩ := measure_result_covered args first low span resultMember
    simp only [List.mem_singleton] at outerMember
    subst outer
    dsimp at upper
    omega

theorem saved_protected_measure {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Protected (Measure.writesFor args.measure (measured s args desc value))
      (args.stack.toNat - 48) 48 := by
  have low := owned.stackLow
  have saveMember : (args.stack.toNat - 48, 48) ∈ stackSpans args := by simp [stackSpans]
  right
  intro span member
  rcases List.mem_append.mp member with localMember | allocation
  · exact Or.inr (measure_local_before_save args _ low span localMember)
  · simp only [Measure.allocationWrites, List.mem_flatMap] at allocation
    obtain ⟨call, callMember, spanMember⟩ := allocation
    cases allocated : call.allocation with
    | none => simp only [allocated, List.not_mem_nil] at spanMember
    | some reservation =>
      simp only [allocated, Args.measure, List.mem_cons, List.not_mem_nil, or_false] at spanMember
      rcases spanMember with rfl | rfl
      · rcases owned.arenaOwned with empty | separate
        · exact False.elim ((by decide : (24 : Nat) ≠ 0) empty)
        · have apart := separate _ (List.mem_append.mpr (Or.inl saveMember))
          dsimp at apart ⊢
          omega
      · have bounds := (Measure.resource_measure (arenaOf s args) desc value).allocations
          call callMember reservation allocated
        have count := Measure.callsTwo_measure (arenaOf s args) desc value call callMember
          reservation allocated
        rcases owned.freeOwned with empty | separate
        · dsimp [freeSpan] at empty
          omega
        · have apart := separate _
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl saveMember))))
          dsimp [freeSpan] at apart ⊢
          omega

end SszArm.Serialize

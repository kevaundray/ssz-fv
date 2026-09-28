import SszArm.SerializeGeometry

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open Delimited (Span Protected MemoryFrame)

theorem Covers.of_subset {small large : List Span}
    (included : ∀ span ∈ small, span ∈ large) : Covers small large := by
  intro span member
  exact ⟨span, included span member, Nat.le_refl _, Nat.le_refl _⟩

theorem protected_subspan_of_bounds {writes : List Span} {address bytes start count : Nat}
    (owned : Protected writes address bytes) (lower : address ≤ start)
    (upper : start + count ≤ address + bytes) : Protected writes start count := by
  have smaller := owned.subspan (start - address) count (by omega)
  have same : address + (start - address) = start := by omega
  simpa only [same] using smaller

theorem measure_stack_covered (args : Args) (first : Outcome NatOperand)
    (low : 432 ≤ args.stack.toNat) :
    Covers (Measure.stackWrites args.measure first) (stackSpans args) := by
  have stack := bodySP_toNat args (by omega)
  intro span member
  simp only [Measure.stackWrites, Measure.saveWrites, Measure.bodyStackWrites,
    Args.measure, stack, List.mem_append, List.mem_singleton] at member
  rcases member with saved | lower | conditional
  · subst span
    refine ⟨(args.stack.toNat - 224, 80), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega
  · subst span
    refine ⟨(args.stack.toNat - 432, 16), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega
  · split at conditional
    · simp only [List.mem_singleton] at conditional
      subst span
      refine ⟨(args.stack.toNat - 296, 68), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega
    · simp only [List.not_mem_nil] at conditional

theorem measure_result_covered (args : Args) (first : Outcome NatOperand)
    (low : 432 ≤ args.stack.toNat) :
    Covers (Measure.resultWrites args.measure first) [(args.stack.toNat - 120, 72)] := by
  have position := plan_toNat args (by omega)
  have extent := resultExtent_le first
  intro span member
  cases result : first.result with
  | ok operand =>
    simp only [Measure.resultWrites, result, Args.measure, position,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      refine ⟨(args.stack.toNat - 120, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega
  | error reason =>
    simp only [Measure.resultWrites, result, Args.measure, position,
      List.mem_singleton] at member
    subst span
    refine ⟨(args.stack.toNat - 120, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega

theorem measure_local_covered (args : Args) (first : Outcome NatOperand)
    (low : 432 ≤ args.stack.toNat) :
    Covers (Measure.localWrites args.measure first) (stackSpans args) := by
  intro span member
  rcases List.mem_append.mp member with stack | result
  · exact measure_stack_covered args first low span stack
  · obtain ⟨outer, outerMember, lower, upper⟩ := measure_result_covered args first low span result
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact ⟨_, by simp [stackSpans], lower, upper⟩

theorem measure_allocation_covered (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    Covers (Measure.allocationWrites args.measure (measured s args desc value))
      [(args.arena.toNat + 16, 8), freeSpan s args] := by
  intro span member
  simp only [Measure.allocationWrites, List.mem_flatMap] at member
  obtain ⟨call, callMember, spanMember⟩ := member
  cases allocated : call.allocation with
  | none => simp only [allocated, List.not_mem_nil] at spanMember
  | some reservation =>
    simp only [allocated, List.mem_cons, List.not_mem_nil, or_false, Args.measure] at spanMember
    rcases spanMember with rfl | rfl
    · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · have bounds := (Measure.resource_measure (arenaOf s args) desc value).allocations
        call callMember reservation allocated
      refine ⟨freeSpan s args, by simp, bounds.1, ?_⟩
      dsimp [freeSpan]
      omega

theorem measure_writes_covered_narrow {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Covers (Measure.writesFor args.measure (measured s args desc value))
      (stackSpans args ++ [(args.arena.toNat + 16, 8), freeSpan s args]) := by
  intro span member
  rcases List.mem_append.mp member with localMember | allocation
  · obtain ⟨outer, outerMember, lower, upper⟩ :=
      measure_local_covered args _ owned.stackLow span localMember
    exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩
  · obtain ⟨outer, outerMember, lower, upper⟩ :=
      measure_allocation_covered s args desc value span allocation
    exact ⟨outer, List.mem_append.mpr (Or.inr outerMember), lower, upper⟩

theorem measure_writes_covered {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Covers (Measure.writesFor args.measure (measured s args desc value)) (writable s args) := by
  apply (measure_writes_covered_narrow owned).trans
  apply Covers.of_subset
  intro span member
  rcases List.mem_append.mp member with stack | arena
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl stack)))
  · exact List.mem_append.mpr (Or.inr arena)

theorem measure_result_stack (args : Args) (first : Outcome NatOperand)
    (low : 432 ≤ args.stack.toNat) :
    ∀ span ∈ Measure.resultWrites args.measure first,
      Protected (Measure.stackWrites args.measure first) span.1 span.2 := by
  have stack := bodySP_toNat args (by omega)
  intro span member
  obtain ⟨outer, outerMember, lower, upper⟩ := measure_result_covered args first low span member
  simp only [List.mem_singleton] at outerMember
  subst outer
  right
  intro store storeMember
  simp only [Measure.stackWrites, Measure.saveWrites, Measure.bodyStackWrites,
    Args.measure, stack, List.mem_append, List.mem_singleton] at storeMember
  rcases storeMember with saved | lowering | conditional
  · subst store; right; dsimp at lower ⊢; omega
  · subst store; right; dsimp at lower ⊢; omega
  · split at conditional
    · simp only [List.mem_singleton] at conditional
      subst store; right; dsimp at lower ⊢; omega
    · simp only [List.not_mem_nil] at conditional

theorem measure_descriptor_covered (args : Args) (desc : Desc) :
    Covers (Measure.descriptorSpans args.measure desc)
      [(args.descriptor.toNat, Emit.descriptorBytes desc)] := by
  intro span member
  refine ⟨(args.descriptor.toNat, SszArm.Emit.descriptorBytes desc), by simp, ?_⟩
  cases desc with
  | progressiveBitList cap =>
    cases cap <;> simp only [Measure.descriptorSpans, Args.measure, List.mem_singleton] at member <;>
      subst span <;> simp [SszArm.Emit.descriptorBytes]
  | _ =>
    simp only [Measure.descriptorSpans, Args.measure, List.mem_singleton] at member
    subst span
    simp [SszArm.Emit.descriptorBytes]

theorem measure_value_covered (args : Args) (value : Value) :
    Covers (Measure.valueSpans args.measure value) [(args.value.toNat, Emit.valueBytes value)] := by
  intro span member
  refine ⟨(args.value.toNat, SszArm.Emit.valueBytes value), by simp, ?_⟩
  cases value <;>
    simp only [Measure.valueSpans, Args.measure, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals first
    | (subst span; simp [SszArm.Emit.valueBytes])
    | (rcases member with rfl | rfl <;>
        simp [SszArm.Emit.valueBytes] <;> omega)

theorem Owned.measure {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) : Measure.Owned s args.measure desc value := by
  have low := owned.stackLow
  have stack := bodySP_toNat args (by omega)
  have position := plan_toNat args (by omega)
  have descriptorCover := measure_descriptor_covered args desc
  have valueCover := measure_value_covered args value
  have covered := measure_writes_covered owned
  have localCover : Covers (Measure.localWrites args.measure (measured s args desc value))
      (stackSpans args ++ externalSpans args) := by
    apply (measure_local_covered args _ low).trans
    exact Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member))
  refine {
    retain := Or.inr rfl
    physical := owned.physical
    descriptor := owned.descriptor
    value_at := owned.value_at
    descriptorBound := ?_
    valueBound := ?_
    resultBound := ?_
    arenaBound := owned.arenaBound
    storageBound := owned.storageBound
    nonnull := owned.nonnull
    stackLow := ?_
    resultStack := measure_result_stack args _ low
    headerLocal := protected_of_covers owned.arenaOwned localCover
    freeLocal := ?_
    descriptorOwned := ?_
    valueOwned := ?_
    operandOwned := fun operand member => operand_owned_of_covers covered operand (owned.operandOwned operand member)
    backingOwned := fun span member => protected_of_covers (owned.backingOwned span member) covered }
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := descriptorCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact Nat.le_trans upper owned.descriptorBound
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := valueCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact Nat.le_trans upper owned.valueBound
  · change args.plan.toNat + Measure.resultExtent (measured s args desc value) ≤ 2^64
    rw [position]
    have extent := resultExtent_le (measured s args desc value)
    have bound := args.stack.isLt
    omega
  · change 288 ≤ args.bodySP.toNat
    rw [stack]
    omega
  · apply protected_of_covers owned.freeOwned
    intro span member
    rcases List.mem_append.mp member with localMember | header
    · obtain ⟨outer, outerMember, lower, upper⟩ := localCover span localMember
      exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩
    · exact ⟨span, List.mem_append.mpr (Or.inr header), Nat.le_refl _, Nat.le_refl _⟩
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := descriptorCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact protected_subspan_of_bounds (protected_of_covers owned.descriptorOwned covered) lower upper
  · intro span member
    obtain ⟨outer, outerMember, lower, upper⟩ := valueCover span member
    simp only [List.mem_singleton] at outerMember
    subst outer
    exact protected_subspan_of_bounds (protected_of_covers owned.valueOwned covered) lower upper

end SszArm.Serialize

import SszArm.SerializeOwnershipMeasure

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open Delimited (Span Protected MemoryFrame)

theorem emit_stack_covered (args : Args) (count : Nat) (low : 432 ≤ args.stack.toNat) :
    Covers (Emit.stackWrites (args.emit count)) (stackSpans args) := by
  have stack := bodySP_toNat args (by omega)
  intro span member
  simp only [Emit.stackWrites, Args.emit, stack, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨(args.stack.toNat - 320, 16), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega
  · refine ⟨(args.stack.toNat - 224, 80), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega

theorem emit_writes_covered_output (args : Args) (count : Nat) (low : 432 ≤ args.stack.toNat) :
    Covers (Emit.writesFor (args.emit count) count)
      (stackSpans args ++ [(args.result.toNat, 72), (args.output.toNat, count)]) := by
  intro span member
  simp only [Emit.writesFor, List.mem_append] at member
  rcases member with (stack | result) | output
  · obtain ⟨outer, outerMember, lower, upper⟩ := emit_stack_covered args count low span stack
    exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩
  · simp only [Args.emit, List.mem_cons, List.not_mem_nil, or_false] at result
    rcases result with rfl | rfl <;>
      refine ⟨(args.result.toNat, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega
  · split at output
    · simp only [List.not_mem_nil] at output
    · simp only [Args.emit, List.mem_singleton] at output
      subst span
      exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem emit_writes_covered_external (args : Args) (count : Nat)
    (low : 432 ≤ args.stack.toNat) (fitting : count ≤ args.capacity.toNat) :
    Covers (Emit.writesFor (args.emit count) count) (stackSpans args ++ externalSpans args) := by
  apply (emit_writes_covered_output args count low).trans
  intro span member
  rcases List.mem_append.mp member with stack | external
  · exact ⟨span, List.mem_append.mpr (Or.inl stack), Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at external
    rcases external with rfl | rfl
    · exact ⟨_, by simp [externalSpans], Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(args.output.toNat, args.capacity.toNat), by simp [externalSpans], Nat.le_refl _, ?_⟩
      dsimp
      omega

theorem emit_writes_covered {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Covers (Emit.writesFor (args.emit count) count) (writable s args) := by
  apply (emit_writes_covered_external args count owned.stackLow fitting).trans
  exact Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member))

theorem emit_backing_eq (s : ArmState) (args : Args) (count : Nat) (value : Value) :
    Emit.backingSpan s (args.emit count) value = Measure.backingSpans s args.measure value := by
  cases value <;> rfl

theorem Owned.emit_of_observations {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat)
    (expected : SszNative.Serialize.expectedSize desc value = .ok count)
    (representable : count < 2^64) (fitting : count ≤ args.capacity.toNat)
    (descriptor : Emit.DescriptorAt t args.descriptor desc)
    (value_at : Emit.ValueAt t args.value value)
    (backing : Measure.backingSpans t args.measure value = Measure.backingSpans s args.measure value) :
    Emit.Owned t (args.emit count) desc value count := by
  have low := owned.stackLow
  have stack := bodySP_toNat args (by omega)
  have capacity : (args.emit count).capacity.toNat = count := by
    simp only [Args.emit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt representable]
  have stackCover := emit_stack_covered args count low
  have covered := emit_writes_covered owned count fitting
  refine {
    expected := expected
    representable := representable
    fitting := by simpa only [capacity] using Nat.le_refl count
    physical := owned.physical
    descriptorBound := owned.descriptorBound
    descriptor := descriptor
    valueBound := owned.valueBound
    value_at := value_at
    resultBound := ?_
    outputBound := ?_
    stackLow := ?_
    resultStack := ?_
    outputStack := ?_
    outputResult := ?_
    descriptorOwned := protected_of_covers owned.descriptorOwned covered
    valueOwned := protected_of_covers owned.valueOwned covered
    operandOwned := fun operand member => operand_owned_of_covers covered operand (owned.operandOwned operand member)
    backingOwned := ?_ }
  · change args.result.toNat + 68 ≤ 2^64
    have bound := owned.resultBound
    omega
  · rw [capacity]
    change args.output.toNat + count ≤ 2^64
    have bound := owned.outputBound
    omega
  · change 176 ≤ args.bodySP.toNat
    rw [stack]
    omega
  · change Protected (Emit.stackWrites (args.emit count)) args.result.toNat 68
    exact protected_subspan_of_bounds (protected_of_covers owned.resultStack stackCover)
      (Nat.le_refl _) (by omega)
  · rw [capacity]
    change Protected (Emit.stackWrites (args.emit count)) args.output.toNat count
    exact protected_subspan_of_bounds (protected_of_covers owned.outputStack stackCover)
      (Nat.le_refl _) (by omega)
  · rw [capacity]
    apply protected_subspan_of_bounds (protected_of_covers owned.outputResult ?_)
      (Nat.le_refl _) (by omega)
    intro span member
    simp only [Args.emit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      refine ⟨(args.result.toNat, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega
  · intro span member
    rw [emit_backing_eq, backing] at member
    exact protected_of_covers (owned.backingOwned span member) covered

theorem emit_header_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.writesFor (args.emit count) count) args.arena.toNat 24 :=
  protected_of_covers owned.arenaOwned (emit_writes_covered_external args count owned.stackLow fitting)

theorem emit_free_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.writesFor (args.emit count) count) (freeSpan s args).1 (freeSpan s args).2 := by
  apply protected_of_covers owned.freeOwned
  apply (emit_writes_covered_external args count owned.stackLow fitting).trans
  exact Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member))

theorem emit_header_preserved {s t u : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat)
    (frame : MemoryFrame (Emit.writesFor (args.emit count) count) t u) :
    read_mem_bytes 8 args.arena u = read_mem_bytes 8 args.arena t ∧
    read_mem_bytes 8 (args.arena + 8#64) u = read_mem_bytes 8 (args.arena + 8#64) t ∧
    read_mem_bytes 8 (args.arena + 16#64) u = read_mem_bytes 8 (args.arena + 16#64) t := by
  have header := emit_header_protected owned count fitting
  have first := Emit.frame_read_offset frame args.arena 24 0 8 owned.arenaBound header (by decide)
  exact ⟨by simpa only [BitVec.add_zero] using first,
    Emit.frame_read_offset frame args.arena 24 8 8 owned.arenaBound header (by decide),
    Emit.frame_read_offset frame args.arena 24 16 8 owned.arenaBound header (by decide)⟩

end SszArm.Serialize

import SszArm.SerializeOwnershipEmit
import SszArm.SerializePostLogic

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open Delimited (Span Protected MemoryFrame)

/-- Used only to transport observations: the exported final frame still retains
writesFor's exact success stores and error-copy extent, including Result padding. -/
def postEnvelope (s : ArmState) (args : Args) (count : Nat) : List Span :=
  stackSpans args ++ [(args.result.toNat, 72), (args.output.toNat, count),
    (args.arena.toNat + 16, 8), freeSpan s args]

theorem size_writes_covered (args : Args) (operand : NatOperand) :
    Covers (sizeWrites args operand) (stackSpans args) := by
  intro span member
  cases operand with
  | small scalar => simp only [sizeWrites, List.not_mem_nil] at member
  | large pointer limbs =>
    by_cases empty : limbs = []
    · simp only [sizeWrites, empty, ↓reduceIte, List.not_mem_nil] at member
    · simp only [sizeWrites, empty, ↓reduceIte, List.mem_singleton] at member
      subst span
      exact ⟨(args.stack.toNat - 160, 16), by simp [stackSpans], Nat.le_refl _, by omega⟩

theorem after_measure_writes_covered (args : Args) (first : Outcome NatOperand) :
    Covers (afterMeasureWrites args first) (stackSpans args ++ [(args.result.toNat, 72)]) := by
  intro span member
  simp only [afterMeasureWrites, List.mem_append, List.mem_singleton] at member
  rcases member with staging | result
  · subst span
    exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩
  · cases measuredResult : first.result with
    | error reason =>
      simp only [measuredResult, List.mem_singleton] at result
      subst span
      exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    | ok operand =>
      simp only [measuredResult, List.mem_singleton] at result
      subst span
      exact ⟨(args.stack.toNat - 120, 72), by simp [stackSpans], Nat.le_refl _, by omega⟩

theorem writesFor_covered_output {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Covers (writesFor s args desc value)
      (postEnvelope s args (outcome s args desc value).writes.size) := by
  have stackCover : Covers (stackSpans args)
      (postEnvelope s args (outcome s args desc value).writes.size) :=
    Covers.of_subset (fun span member => List.mem_append.mpr (Or.inl member))
  have measureCover : Covers (Measure.writesFor args.measure (measured s args desc value))
      (postEnvelope s args (outcome s args desc value).writes.size) :=
    (measure_writes_covered_narrow owned).trans
    (Covers.of_subset (by
      intro span member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [postEnvelope, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rcases member with stack | header | storage
      · exact Or.inl stack
      · exact Or.inr (Or.inr (Or.inr (Or.inl header)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr storage)))))
  have afterCover : Covers (afterMeasureWrites args (measured s args desc value))
      (postEnvelope s args (outcome s args desc value).writes.size) :=
    (after_measure_writes_covered args (measured s args desc value)).trans
    (Covers.of_subset (by
      intro span member
      rcases List.mem_append.mp member with stack | result
      · exact List.mem_append.mpr (Or.inl stack)
      · simp only [List.mem_singleton] at result
        subst span
        simp [postEnvelope]))
  intro span member
  simp only [writesFor, List.mem_append] at member
  rcases member with ((saved | measureMember) | afterMember) | continuation
  · exact ((save_covered args).trans stackCover) span saved
  · exact measureCover span measureMember
  · exact afterCover span afterMember
  · cases success : (measured s args desc value).result with
    | error reason =>
      simp only [continuationWrites, success, List.not_mem_nil] at continuation
    | ok operand =>
      by_cases passes : operand.value < 2^64 ∧ operand.value ≤ args.capacity.toNat
      · simp only [continuationWrites, success, passes, List.mem_append] at continuation
        rcases continuation with scan | emitted
        · exact ((size_writes_covered args operand).trans stackCover) span scan
        · have count := outcome_writes_size_of_success s args desc value owned.physical operand
            success passes.1 passes.2
          apply ((emit_writes_covered_output args operand.value owned.stackLow).trans ?_) span emitted
          apply Covers.of_subset
          intro store storeMember
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at storeMember
          rcases storeMember with stack | result | output
          · exact List.mem_append.mpr (Or.inl stack)
          · subst store
            simp [postEnvelope]
          · subst store
            simp [postEnvelope, count]
      · simp only [continuationWrites, success, passes, ↓reduceIte, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at continuation
        rcases continuation with scan | spill | result
        · exact ((size_writes_covered args operand).trans stackCover) span scan
        · subst span
          exact ⟨_, by simp [postEnvelope, stackSpans], Nat.le_refl _, Nat.le_refl _⟩
        · subst span
          exact ⟨(args.result.toNat, 72), by simp [postEnvelope], Nat.le_refl _, by omega⟩

theorem writesFor_covered {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) : Covers (writesFor s args desc value) (writable s args) := by
  apply (writesFor_covered_output owned).trans
  intro span member
  simp only [postEnvelope, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with stack | result | output | header | storage
  · exact ⟨span, by simp [writable, stack], Nat.le_refl _, Nat.le_refl _⟩
  · subst span
    exact ⟨_, by simp [writable, externalSpans], Nat.le_refl _, Nat.le_refl _⟩
  · subst span
    refine ⟨(args.output.toNat, args.capacity.toNat), by simp [writable, externalSpans],
      Nat.le_refl _, ?_⟩
    have count := outcome_writes_size_le s args desc value owned.physical
    dsimp
    omega
  · subst span
    exact ⟨_, by simp [writable], Nat.le_refl _, Nat.le_refl _⟩
  · subst span
    exact ⟨_, by simp [writable], Nat.le_refl _, Nat.le_refl _⟩

theorem output_tail {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (writesFor s args desc value) s t)
    (index : Nat) (low : (outcome s args desc value).writes.size ≤ index)
    (high : index < args.capacity.toNat) :
    t.mem (args.output + BitVec.ofNat 64 index) = s.mem (args.output + BitVec.ofNat 64 index) := by
  have position : (args.output + BitVec.ofNat 64 index).toNat = args.output.toNat + index := by
    have bound := owned.outputBound
    bv_omega
  apply frame_of_covers frame (writesFor_covered_output owned)
  intro span member
  simp only [postEnvelope, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [position]
  rcases member with stack | result | output | header | storage
  · rcases owned.outputStack with empty | separate
    · omega
    · have apart := separate span stack
      omega
  · subst span
    rcases owned.outputResult with empty | separate
    · omega
    · have apart := separate (args.result.toNat, 72) (by simp)
      dsimp at apart ⊢
      omega
  · subst span
    right
    dsimp
    omega
  · subst span
    rcases owned.arenaOwned with empty | separate
    · omega
    · have apart := separate (args.output.toNat, args.capacity.toNat) (by simp [externalSpans])
      dsimp at apart ⊢
      omega
  · subst span
    rcases owned.freeOwned with empty | separate
    · omega
    · have apart := separate (args.output.toNat, args.capacity.toNat) (by simp [externalSpans])
      dsimp at apart ⊢
      omega

end SszArm.Serialize

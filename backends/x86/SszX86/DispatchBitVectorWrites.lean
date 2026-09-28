import SszX86.DispatchBitVectorOwned
import SszX86.BitVectorProofs

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

private theorem division_writes (length : NatOperand) (base capacity used : Nat)
    (span : Nat × Nat)
    (member : span ∈ SszNative.BitVector.allocationWrites
      (SszNative.NatDivision.run length 8 base capacity used)) :
    base + used ≤ span.1 ∧ span.1 + span.2 ≤ base + capacity := by
  cases allocated : (SszNative.NatDivision.run length 8 base capacity used).allocation with
  | none => simp only [SszNative.BitVector.allocationWrites, allocated, List.not_mem_nil] at member
  | some r =>
    simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton] at member
    subst span
    obtain ⟨cursor, count, checks, pointer, finish, success⟩ :=
      SszNative.NatDivision.allocation_resources length 8 base capacity used r allocated
    rw [← count] at checks finish
    have fits := checks.2.2.2.2.2
    have start := SszNative.Arena.used_le_start base used
    unfold SszNative.Arena.finish at fits finish
    constructor <;> omega

private theorem division_progress (length : NatOperand) (base capacity used : Nat) :
    used ≤ (SszNative.NatDivision.run length 8 base capacity used).used := by
  cases allocated : (SszNative.NatDivision.run length 8 base capacity used).allocation with
  | none =>
    rw [(SszNative.NatDivision.no_allocation_resources length 8 base capacity used allocated).1]
    exact Nat.le_refl _
  | some r =>
    obtain ⟨cursor, count, checks, pointer, finish, success⟩ :=
      SszNative.NatDivision.allocation_resources length 8 base capacity used r allocated
    have start := SszNative.Arena.used_le_start base used
    unfold SszNative.Arena.finish at finish
    omega

private theorem addition_writes (left right : NatOperand) (base capacity used : Nat)
    (span : Nat × Nat)
    (member : span ∈ SszNative.BitVector.allocationWrites
      (SszNative.NatAdd.run left right base capacity used)) :
    base + used ≤ span.1 ∧ span.1 + span.2 ≤ base + capacity := by
  cases allocated : (SszNative.NatAdd.run left right base capacity used).allocation with
  | none => simp only [SszNative.BitVector.allocationWrites, allocated, List.not_mem_nil] at member
  | some r =>
    simp only [SszNative.BitVector.allocationWrites, allocated, List.mem_singleton] at member
    subst span
    obtain ⟨checks, pointer, cursor, count⟩ :=
      SszNative.NatAdd.allocation_geometry left right base capacity used r allocated
    have fits := checks.2.2.2.2.2
    have start := SszNative.Arena.used_le_start base used
    unfold SszNative.Arena.finish at fits
    constructor <;> omega

/-- Both reservations, including all trimmed high zero words, are within the
original free suffix; the later reservation starts after the committed cursor. -/
theorem bitVector_writes (length : NatOperand) (data : Ssz.Bytes)
    (base capacity used : Nat) (span : Nat × Nat)
    (member : span ∈ (SszNative.BitVector.run length data ⟨base, capacity, used⟩).writes) :
    base + used ≤ span.1 ∧ span.1 + span.2 ≤ base + capacity := by
  have division := division_writes length base capacity used
  have progress := division_progress length base capacity used
  cases hd : (SszNative.NatDivision.run length 8 base capacity used).result with
  | error reason =>
    simp only [SszNative.BitVector.run, hd, SszNative.BitVector.Outcome.writes,
      List.append_nil] at member
    exact division span member
  | ok pair =>
    obtain ⟨quotient, remainder⟩ := pair
    by_cases zero : remainder = 0
    · simp only [SszNative.BitVector.run, hd, zero, ↓reduceIte,
        SszNative.BitVector.Outcome.writes, List.append_nil] at member
      exact division span member
    · have addition := addition_writes quotient (.small 1) base capacity
        (SszNative.NatDivision.run length 8 base capacity used).used
      cases ha : (SszNative.NatAdd.run quotient (.small 1) base capacity
        (SszNative.NatDivision.run length 8 base capacity used).used).result <;>
        simp only [SszNative.BitVector.run, hd, zero, ↓reduceIte, ha,
          SszNative.BitVector.Outcome.writes] at member
      all_goals
        rcases List.mem_append.mp member with before | after
        · exact division span before
        · have bounds := addition span after
          exact ⟨by omega, bounds.2⟩

end SszX86.Dispatch

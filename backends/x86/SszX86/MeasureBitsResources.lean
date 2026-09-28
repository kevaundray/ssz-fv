import SszX86.MeasureOwned
import SszX86.MeasureFrame

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- Cursor monotonicity is unconditional, including invalid used>capacity input. -/
theorem wide_used_mono (base capacity used : Nat) (wide : BitVec 128) :
    used ≤ (NatArithmetic.fromWide base capacity used wide).used := by
  by_cases small : wide.toNat < 2^64
  · simp only [NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged, Nat.le_refl]
  cases reserved : Arena.reserve base capacity used 2 with
  | none =>
    simp only [NatArithmetic.fromWide, small, ↓reduceIte, reserved,
      NatArithmetic.unchanged, Nat.le_refl]
  | some r =>
    obtain ⟨checks, rfl⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
    simp only [NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.committed,
      Arena.finish, Arena.start]
    omega

/-- Every positive count allocation is precisely two written words, with all
alignment bytes consumed but unwritten. No initial used≤capacity is required. -/
theorem wide_allocation_geometry (base capacity used : Nat) (wide : BitVec 128)
    (r : Arena.Reservation)
    (allocated : (NatArithmetic.fromWide base capacity used wide).allocation = some r) :
    Arena.reserve base capacity used 2 = some r ∧
    (NatArithmetic.fromWide base capacity used wide).written =
      [wide.setWidth 64, (wide >>> 64).setWidth 64] ∧
    base + used ≤ r.pointer ∧ r.pointer + 16 ≤ base + capacity ∧
    used ≤ r.used ∧ r.used ≤ capacity := by
  by_cases small : wide.toNat < 2^64
  · simp only [NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged] at allocated
    cases allocated
  cases reserved : Arena.reserve base capacity used 2 with
  | none =>
    simp only [NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.unchanged] at allocated
    cases allocated
  | some reservation =>
    simp only [NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.committed,
      Option.some.injEq] at allocated
    subst reservation
    obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [NatArithmetic.fromWide, small, ↓reduceIte, reserved, NatArithmetic.committed]
    all_goals rw [shape]
    all_goals have fits := checks.2.2.2.2.2
    all_goals simp only [Arena.finish, Arena.start, Nat.reduceMul] at *
    all_goals omega

/-- Membership keeps the two distinct call sites and the first committed cursor.
A missing optional bound does not remove the first constructor from the trace. -/
theorem list_call_cases (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) (call : NatArithmetic.Outcome NatOperand)
    (member : call ∈ (measureList limit bits arena).calls) :
    call = NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count ∨
    call = NatArithmetic.fromWide arena.base arena.capacity
      (fromWide arena bits.count).used (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) := by
  cases first : (fromWide arena bits.count).result with
  | error reason =>
    simp only [measureList, Serialize.bind, first] at member
    change call ∈ [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] at member
    exact Or.inl (List.mem_singleton.mp member)
  | ok actual =>
    simp only [measureList, Serialize.bind, first] at member
    have empty := (bounded_resources limit actual (fromWide arena bits.count).used).2
    have cursor := (bounded_resources limit actual (fromWide arena bits.count).used).1
    cases checked : (bounded limit actual (fromWide arena bits.count).used).result with
    | error reason =>
      simp only [checked, empty, List.append_nil] at member
      change call ∈ [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] at member
      exact Or.inl (List.mem_singleton.mp member)
    | ok resultUnit =>
      simp only [checked, empty, cursor, List.nil_append] at member
      change call ∈ [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] ++
        [NatArithmetic.fromWide arena.base arena.capacity (fromWide arena bits.count).used
          (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))] at member
      simpa only [List.mem_append, List.mem_singleton] using member

/-- A later successful reservation remains inside the original free suffix,
not a newly assumed arena, even after a previous successful reservation. -/
theorem list_allocation_geometry (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) (call : NatArithmetic.Outcome NatOperand)
    (member : call ∈ (measureList limit bits arena).calls) (r : Arena.Reservation)
    (allocated : call.allocation = some r) :
    arena.base + arena.used ≤ r.pointer ∧
    r.pointer + 8 * call.written.length ≤ arena.base + arena.capacity := by
  rcases list_call_cases limit bits arena call member with rfl | rfl
  · have geometry := wide_allocation_geometry _ _ _ _ r allocated
    rw [geometry.2.1]
    exact ⟨geometry.2.2.1, by simpa using geometry.2.2.2.1⟩
  · have geometry := wide_allocation_geometry _ _ _ _ r allocated
    have cursor := wide_used_mono arena.base arena.capacity arena.used bits.count
    change arena.used ≤ (fromWide arena bits.count).used at cursor
    rw [geometry.2.1]
    exact ⟨by omega, by simpa using geometry.2.2.2.1⟩

end SszX86.Measure.Bits

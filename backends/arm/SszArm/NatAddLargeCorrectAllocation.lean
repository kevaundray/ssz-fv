import SszArm.NatAddLargeCorrectMemory

namespace SszArm.NatAdd.LargeCorrect

open SszNative
open UintCodec (widthLoad)
open Delimited (Span Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem large_outcome (s : ArmState) (left right : NatOperand)
    (owned : Owned s left right) (leftNonzero : left.wordCount ≠ 0)
    (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)) :
    outcome s left right =
      match Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
          (SszNative.NatAdd.count left right + 1) with
      | none => NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)
      | some reservation => NatArithmetic.committed reservation (SszNative.NatAdd.writtenWords left right) := by
  have hl := count_bound s left owned.leftAt
  have hr := count_bound s right owned.rightAt
  have bound : SszNative.NatAdd.count left right + 1 < 2^64 := by
    simp only [SszNative.NatAdd.count]
    omega
  rw [outcome, SszNative.NatAdd.run_large left right _ _ _ leftNonzero rightNonzero large]
  simp only [bound, ↓reduceIte]

structure Allocation (s : ArmState) (left right : NatOperand)
    (reservation : Arena.Reservation) : Prop where
  outcomeEq : outcome s left right =
    NatArithmetic.committed reservation (SszNative.NatAdd.writtenWords left right)
  positive : 0 < reservation.pointer
  aligned : reservation.pointer % 8 = 0
  physical : reservation.pointer + 8 * (SszNative.NatAdd.count left right + 1) ≤ 2^64
  usedBound : reservation.used < 2^64
  fresh : Protected (localWrites s ++ [((r (.GPR 5#5) s).toNat, 24)])
    reservation.pointer (8 * (SszNative.NatAdd.count left right + 1))

theorem allocation (s : ArmState) (left right : NatOperand)
    (owned : Owned s left right) (leftNonzero : left.wordCount ≠ 0)
    (rightNonzero : right.wordCount ≠ 0)
    (large : ¬ (left.wordCount ≤ 1 ∧ right.wordCount ≤ 1))
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
      (SszNative.NatAdd.count left right + 1) = some reservation) :
    Allocation s left right reservation := by
  have result : outcome s left right =
      NatArithmetic.committed reservation (SszNative.NatAdd.writtenWords left right) := by
    rw [large_outcome s left right owned leftNonzero rightNonzero large, reserved]
  obtain ⟨checks, exactReservation⟩ :=
    (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) reservation).mp reserved
  have cursorBound := checks.2.2.2.2.1
  have capacity := checks.2.2.2.2.2
  have startBound := Arena.used_le_start (arenaOf s).base (arenaOf s).used
  have storage := owned.arenaStorage
  have capPositive : 0 < (arenaOf s).capacity := by
    unfold Arena.finish at capacity
    omega
  have basePositive := owned.arenaNonnull capPositive
  refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exactReservation]
    simp only [Arena.Reservation.pointer]
    omega
  · rw [exactReservation]
    simp only [Arena.Reservation.pointer, Arena.start_pointer]
    exact Arena.aligned_mod _
  · rw [exactReservation]
    simp only [Arena.Reservation.pointer]
    unfold Arena.finish at capacity
    omega
  · simpa only [exactReservation] using cursorBound
  · have allocated : (outcome s left right).allocation = some reservation := by
      simp only [result, NatArithmetic.committed]
    simpa only [result, NatArithmetic.committed, SszNative.NatAdd.writtenWords_length] using
      owned.fresh reservation allocated

theorem Allocation.pointer_bound {s : ArmState} {left right : NatOperand}
    {reservation : Arena.Reservation} (allocated : Allocation s left right reservation) :
    reservation.pointer < 2^64 := by have := allocated.physical; omega

theorem Allocation.writes {s : ArmState} {left right : NatOperand}
    {reservation : Arena.Reservation} (allocated : Allocation s left right reservation) :
    writesFor s (outcome s left right) = localWrites s ++
      [((r (.GPR 5#5) s).toNat + 16, 8),
       (reservation.pointer, 8 * (SszNative.NatAdd.count left right + 1))] := by
  simp only [allocated.outcomeEq, NatArithmetic.committed, writesFor,
    SszNative.NatAdd.writtenWords_length]

theorem Allocation.suffix_contained {s : ArmState} {left right : NatOperand}
    {reservation : Arena.Reservation} (allocated : Allocation s left right reservation)
    (index remaining : Nat) (within : index + remaining ≤ SszNative.NatAdd.count left right + 1) :
    ∀ inner ∈ LargeLoop.suffixWrites (r (.GPR 31#5) s)
      (BitVec.ofNat 64 reservation.pointer) index remaining,
      ∃ outer ∈ writesFor s (outcome s left right),
        outer.1 ≤ inner.1 ∧ inner.1 + inner.2 ≤ outer.1 + outer.2 := by
  intro inner member
  have pointer : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
    BitVec.toNat_ofNat_of_lt allocated.pointer_bound
  simp only [LargeLoop.suffixWrites, List.mem_cons, List.mem_singleton, pointer] at member
  rcases member with rfl | rfl
  · refine ⟨((r (.GPR 31#5) s).toNat - 16, 16), ?_, by omega, by omega⟩
    rw [allocated.writes]
    simp [localWrites]
  · refine ⟨(reservation.pointer, 8 * (SszNative.NatAdd.count left right + 1)), ?_, ?_, ?_⟩
    · rw [allocated.writes]; simp
    · simp only [Prod.fst]; omega
    · simp only [Prod.fst, Prod.snd]; omega

theorem Allocation.output_stack {s : ArmState} {left right : NatOperand}
    {reservation : Arena.Reservation} (allocated : Allocation s left right reservation) :
    Protected [((r (.GPR 31#5) s).toNat - 16, 16)] reservation.pointer
      (8 * (SszNative.NatAdd.count left right + 1)) := by
  apply protected_of_contained allocated.fresh
  intro inner member
  refine ⟨inner, ?_, Nat.le_refl _, Nat.le_refl _⟩
  simp only [List.mem_singleton] at member
  subst inner
  simp [localWrites]

theorem Allocation.output_local {s : ArmState} {left right : NatOperand}
    {reservation : Arena.Reservation} (allocated : Allocation s left right reservation) :
    Protected (localWrites s) reservation.pointer
      (8 * (SszNative.NatAdd.count left right + 1)) := by
  apply protected_of_contained allocated.fresh
  intro inner member
  exact ⟨inner, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩

end SszArm.NatAdd.LargeCorrect

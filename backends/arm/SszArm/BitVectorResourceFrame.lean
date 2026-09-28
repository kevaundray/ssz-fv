import SszArm.BitVectorArena
import SszArm.BitVectorRoundOwned

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame)

private theorem rounded_origin (s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (rounded : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (present : (outcome s length data).rounded = some rounded) :
    ∃ quotient remainder,
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).result =
        .ok (quotient, remainder) ∧ remainder ≠ 0 ∧ rounded = rounding s length quotient := by
  cases divided : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result with
  | error reason =>
    simp only [outcome, SszNative.BitVector.run, divided] at present
    cases present
  | ok value =>
    obtain ⟨quotient, remainder⟩ := value
    by_cases zero : remainder = 0
    · simp only [outcome, SszNative.BitVector.run, divided, zero, ↓reduceIte] at present
      cases present
    · rw [rounded_eq s length quotient remainder data divided zero] at present
      exact ⟨quotient, remainder, rfl, zero, (Option.some.inj present).symm⟩

theorem division_buffer_physical {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome s length data).divided.allocation = some reservation) :
    reservation.pointer + 8 * (outcome s length data).divided.written.length ≤ 2^64 := by
  have extent := division_allocation_end length (arenaOf s) reservation
    (by simpa only [outcome, divided_eq] using allocated)
  have cursor := (division_cursor_bounds s length data owned).2
  have storage := owned.arenaStorage
  simp only [outcome, divided_eq] at cursor ⊢
  omega

theorem rounded_buffer_physical {s : ArmState} {length quotient : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (reservation : SszNative.Arena.Reservation)
    (allocated : (rounding s length quotient).allocation = some reservation) :
    reservation.pointer + 8 * (rounding s length quotient).written.length ≤ 2^64 := by
  have geometry := SszNative.NatAdd.allocation_geometry quotient (.small 1) (arenaOf s).base
    (arenaOf s).capacity
    (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used
    reservation allocated
  have cursor := (rounded_cursor_bounds s length quotient data owned).2
  have storage := owned.arenaStorage
  dsimp only [rounding] at cursor ⊢
  rw [geometry.2.1]
  rw [geometry.2.2.1] at cursor
  simp only [SszNative.Arena.finish] at cursor
  omega

theorem allocated_local_owned {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (span : Delimited.Span)
    (member : span ∈ (outcome s length data).writes) : Protected (localWrites s) span.1 span.2 := by
  have cover : Covers (localWrites s ++
      [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)]) (localWrites s) :=
    fun part within => ⟨part, List.mem_append_left _ within, Nat.le_refl _, Nat.le_refl _⟩
  exact cover.protected (owned.fresh span member)

theorem divided_after_local {s a b : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (frame : MemoryFrame (localWrites s) a b)
    (stored : SszNative.BitVector.allocationAt (widthLoad a) (outcome s length data).divided) :
    SszNative.BitVector.allocationAt (widthLoad b) (outcome s length data).divided := by
  intro reservation allocated
  have physical := division_buffer_physical owned reservation allocated
  have member := divided_write s length data reservation
    (by simpa only [outcome, divided_eq] using allocated)
  apply written_preserved reservation.pointer (outcome s length data).divided.written physical
    (by simpa only [outcome, divided_eq] using allocated_local_owned owned _ member) frame
  exact stored reservation allocated

theorem written_after_local {s a b : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (frame : MemoryFrame (localWrites s) a b)
    (stored : (outcome s length data).writtenAt (widthLoad a)) :
    (outcome s length data).writtenAt (widthLoad b) := by
  refine ⟨divided_after_local owned frame stored.1, ?_⟩
  intro rounded present reservation allocated
  obtain ⟨quotient, remainder, divided, nonzero, rfl⟩ := rounded_origin s length data rounded present
  have physical := rounded_buffer_physical owned reservation allocated
  have member := rounded_write s length quotient remainder data divided nonzero reservation allocated
  exact written_preserved reservation.pointer (rounding s length quotient).written physical
    (allocated_local_owned owned _ member) frame (stored.2 _ present reservation allocated)

/-- The second helper preserves the complete first allocation, not merely the
normalized quotient prefix. Its extra high zero word remains observable. -/
theorem division_buffer_owned_round {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (args : RoundArguments s c length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome s length data).divided.allocation = some reservation) :
    Protected (NatAdd.writesFor c (NatAdd.outcome c quotient (.small 1))) reservation.pointer
      (8 * (outcome s length data).divided.written.length) := by
  have first : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).allocation = some reservation := by
    simpa only [outcome, divided_eq] using allocated
  have common : Protected (NatAdd.localWrites c ++ [((r (.GPR 5#5) c).toNat, 24)])
      reservation.pointer (8 * (outcome s length data).divided.written.length) := by
    simpa only [outcome, divided_eq] using (round_envelope owned args).protected
      (owned.fresh _ (divided_write s length data reservation first))
  cases second : (NatAdd.outcome c quotient (.small 1)).allocation with
  | none =>
    simp only [NatAdd.writesFor, second]
    exact (show Covers (NatAdd.localWrites c ++ [((r (.GPR 5#5) c).toNat, 24)])
      (NatAdd.localWrites c) from fun span member =>
        ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩).protected common
  | some next =>
    have ordered := allocations_ordered length quotient (arenaOf s) reservation next first
      (by simpa only [args.model, rounding] using second)
    simp only [NatAdd.writesFor, second]
    rcases common with empty | separate
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with inLocals | rfl | rfl
      · exact separate span (List.mem_append_left _ inLocals)
      · have header := separate ((r (.GPR 5#5) c).toNat, 24) (by simp)
        omega
      · left
        simpa only [outcome, divided_eq] using ordered

end SszArm.BitVector

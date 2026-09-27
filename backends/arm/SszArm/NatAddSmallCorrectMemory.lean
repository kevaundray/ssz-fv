import SszArm.NatAddSmallCorrectModel

namespace SszArm.NatAdd.SmallCorrect

open UintCodec SszNative
open Delimited (Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem reservation_geometry {s : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (reservation : Arena.Reservation)
    (reserved : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used 2 = some reservation) :
    0 < reservation.pointer ∧ reservation.pointer % 8 = 0 ∧
      reservation.pointer + 16 ≤ 2^64 ∧ reservation.used < 2^64 := by
  obtain ⟨checks, exactReservation⟩ :=
    (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) reservation).mp reserved
  have capacity := checks.2.2.2.2.2
  have finish := checks.2.2.2.2.1
  have basePositive := owned.arenaNonnull (by unfold Arena.finish at capacity; omega)
  have physical := owned.arenaStorage
  subst reservation
  simp only [Arena.Reservation.mk.injEq, Arena.finish] at *
  refine ⟨by omega, ?_, by omega, finish⟩
  rw [Arena.start_pointer]
  exact Arena.aligned_mod _

theorem reservation_fresh {s : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used 2 = some reservation) :
    Protected (localWrites s ++ [((r (.GPR 5#5) s).toNat, 24)]) reservation.pointer 16 := by
  have model := model_overflow s left right hl hr overflow
  rw [reserved] at model
  have allocated : (outcome s left right).allocation = some reservation := by
    simp only [model, NatArithmetic.committed]
  simpa only [model, NatArithmetic.committed, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul] using owned.fresh reservation allocated

theorem reservation_owned {s u : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat)
    (h5 : r (.GPR 5#5) u = r (.GPR 5#5) s)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used 2 = some reservation) :
    ArenaSmallReservationOwned u reservation := by
  have geometry := reservation_geometry owned reservation reserved
  have fresh := reservation_fresh owned hl hr overflow reservation reserved
  have bound := owned.arenaBound
  have cursor : (r (.GPR 5#5) u + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by
    rw [h5]
    bv_omega
  refine ⟨by rw [cursor]; omega, geometry.1, geometry.2.2.1, ?_⟩
  rw [cursor]
  rcases fresh with empty | separate
  · omega
  · have apart := separate ((r (.GPR 5#5) s).toNat, 24) (by simp)
    omega

theorem fresh_local {s : ArmState} {pointer : Nat}
    (fresh : Protected (localWrites s ++ [((r (.GPR 5#5) s).toNat, 24)]) pointer 16) :
    Protected (localWrites s) pointer 16 := by
  rcases fresh with empty | apart
  · exact Or.inl empty
  · right
    intro span member
    exact apart span (List.mem_append_left _ member)

/-- Read back the exact two words from the actual paired allocation store. -/
theorem allocated_words (u v : ArmState) (base : BitVec 64) (reservation : Arena.Reservation)
    (success : ArenaSmallSuccess u v base reservation)
    (physical : reservation.pointer + 16 ≤ 2^64) :
    NatMemory.wordsAt (widthLoad v) reservation.pointer [r (.GPR 9#5) u, 1#64] := by
  have pointerBound : reservation.pointer < 2^64 := by omega
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer := by
    exact Nat.mod_eq_of_lt pointerBound
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp success.memory
  have paired := UintCodec.Tail.write_pair_words (arenaCursorMemory u reservation)
    (BitVec.ofNat 64 reservation.pointer) (r (.GPR 9#5) u) 1#64
    (by rw [pointerNat]; exact physical)
  intro i
  have hi : i.val < 2 := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with zero | one
  · simp only [widthLoad, zero, Nat.mul_zero, Nat.add_zero]
    rw [reads]
    simp only [arenaSmallReservedMemory, paired]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (BitVec.ofNat 64 reservation.pointer) (BitVec.ofNat 64 reservation.pointer + 8#64) 1#64
      (by rw [pointerNat]; omega) (by bv_omega) (by left; bv_omega),
      BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by rw [pointerNat]; omega)]
    simp [zero]
  · have address : BitVec.ofNat 64 (reservation.pointer + 8 * i.val) =
        BitVec.ofNat 64 reservation.pointer + 8#64 := by rw [one]; bv_omega
    simp only [widthLoad, address]
    rw [reads]
    simp only [arenaSmallReservedMemory, paired]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)]
    simp [one]

theorem allocated_at (u v : ArmState) (base : BitVec 64) (reservation : Arena.Reservation)
    (success : ArenaSmallSuccess u v base reservation)
    (positive : 0 < reservation.pointer) (aligned : reservation.pointer % 8 = 0)
    (physical : reservation.pointer + 16 ≤ 2^64) :
    (NatOperand.large (BitVec.ofNat 64 reservation.pointer)
      [r (.GPR 9#5) u, 1#64]).At (widthLoad v) := by
  have pointerBound : reservation.pointer < 2^64 := by omega
  have pointerNat : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
    Nat.mod_eq_of_lt pointerBound
  refine ⟨by simpa only [pointerNat] using positive,
    by simpa only [pointerNat] using aligned, ?_, ?_⟩
  · simpa only [pointerNat, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using physical
  · simpa only [pointerNat] using allocated_words u v base reservation success physical

end SszArm.NatAdd.SmallCorrect

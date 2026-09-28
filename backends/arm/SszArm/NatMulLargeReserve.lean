import SszArm.NatMulLargeGeometry

namespace SszArm.NatMul

open Delimited (Span Protected MemoryFrame)
open SszNative (NatOperand NatArithmetic)

/-- The body region is below, and disjoint from, the saved 96-byte image. -/
def largeWorkWrites (s : ArmState) (reservation : SszNative.Arena.Reservation) (count : Nat) : List Span :=
  [((r (.GPR 31#5) s).toNat - 144, 48),
   ((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * count)]

structure LargeReservation (s : ArmState) (left right : NatOperand)
    (reservation : SszNative.Arena.Reservation) : Prop where
  model : outcome s left right = NatArithmetic.committed reservation (SszNative.NatMul.writtenWords left right)
  positive : 0 < left.wordCount + right.wordCount
  physical : reservation.pointer + 8 * (left.wordCount + right.wordCount) ≤ 2^64
  nonnull : 0 < reservation.pointer
  aligned : reservation.pointer % 8 = 0
  addressBound : reservation.pointer < 2^64
  usedBound : reservation.used < 2^64
  fresh : Protected (localWrites s (outcome s left right) ++ [((r (.GPR 5#5) s).toNat, 24)])
    reservation.pointer (8 * (left.wordCount + right.wordCount))

theorem large_reservation {s : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (largeLeft : 1 < left.wordCount) (largeRight : 1 < right.wordCount)
    (reservation : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
      (left.wordCount + right.wordCount) = some reservation) : LargeReservation s left right reservation := by
  have model := reserve_model_success left right (arenaOf s).base (arenaOf s).capacity
    (arenaOf s).used largeLeft largeRight reservation reserved
  change outcome s left right = _ at model
  obtain ⟨checks, value⟩ := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _
    (by omega) reservation).1 reserved
  have positiveCapacity : 0 < (arenaOf s).capacity := by
    have finish := checks.2.2.2.2.2
    simp only [SszNative.Arena.finish] at finish
    omega
  have positiveBase := owned.arenaNonnull positiveCapacity
  have storage := owned.arenaStorage
  have fresh := owned.fresh reservation (by rw [model]; rfl)
  refine ⟨model, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value]
    have finish := checks.2.2.2.2.2
    simp only [SszNative.Arena.finish] at finish
    dsimp only
    omega
  · rw [value]
    dsimp only
    omega
  · rw [value]
    exact (congrArg (fun n => n % 8) (SszNative.Arena.start_pointer _ _)).trans
      (SszNative.Arena.aligned_mod _)
  · rw [value]
    have finish := checks.2.2.2.2.2
    simp only [SszNative.Arena.finish] at finish
    dsimp only
    omega
  · rw [value]
    exact checks.2.2.2.2.1
  · simpa only [model, NatArithmetic.committed, SszNative.NatMul.writtenWords_length] using fresh

theorem LargeReservation.work_cover {s : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation) :
    BitVector.Covers (writesFor s (outcome s left right))
      (largeWorkWrites s reservation (left.wordCount + right.wordCount)) := by
  intro span member
  simp only [largeWorkWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  have writes : writesFor s (outcome s left right) =
      localWrites s (outcome s left right) ++
        [((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * (left.wordCount + right.wordCount))] := by
    simp only [writesFor, allocated.model, NatArithmetic.committed, SszNative.NatMul.writtenWords_length]
  rw [writes]
  rcases member with rfl | rfl | rfl
  · refine ⟨((r (.GPR 31#5) s).toNat - 144, 144), ?_, le_rfl, by omega⟩
    exact List.mem_append_left _ (large_stack_local _ _)
  · exact ⟨_, by simp, le_rfl, le_rfl⟩
  · exact ⟨_, by simp, le_rfl, le_rfl⟩

theorem LargeReservation.reserve_cover {s u : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) (entry : EntryFrame s u) :
    BitVector.Covers (largeWorkWrites s reservation (left.wordCount + right.wordCount))
      [((r (.GPR 31#5) u).toNat - 16, 16),
       ((r (.GPR 5#5) u + 16#64).toNat, 8), (reservation.pointer, 8 * (left.wordCount + right.wordCount))] := by
  have sp := large_sp_nat owned entry.sp
  have stack := owned.stackBound
  have arena := owned.arenaBound
  have cursor : (r (.GPR 5#5) u + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by
    rw [entry.arena]; bv_omega
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨((r (.GPR 31#5) s).toNat - 144, 48), by simp [largeWorkWrites], by omega, by omega⟩
  · exact ⟨((r (.GPR 5#5) s).toNat + 16, 8), by simp [largeWorkWrites], by rw [cursor], by rw [cursor]⟩
  · exact ⟨_, by simp [largeWorkWrites], le_rfl, le_rfl⟩

theorem LargeReservation.work_saved {s u : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64) :
    Protected (largeWorkWrites s reservation (left.wordCount + right.wordCount))
      (r (.GPR 31#5) u).toNat 96 := by
  have current := large_sp_nat owned sp
  have stack := owned.stackBound
  have positive := allocated.positive
  have arenaApart : (r (.GPR 5#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat - 144 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 5#5) s).toNat := by
    rcases owned.arenaLocal with empty | separate
    · omega
    · have apart := separate _ (large_stack_local _ _)
      simp only [Prod.fst, Prod.snd] at apart
      omega
  have payloadApart : reservation.pointer + 8 * (left.wordCount + right.wordCount) ≤
      (r (.GPR 31#5) s).toNat - 144 ∨ (r (.GPR 31#5) s).toNat ≤ reservation.pointer := by
    rcases allocated.fresh with empty | separate
    · omega
    · have apart := separate _ (List.mem_append_left _ (large_stack_local _ _))
      simp only [Prod.fst, Prod.snd] at apart
      omega
  right
  intro span member
  simp only [largeWorkWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem LargeReservation.loop_cover {s u : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    (pointer : (r (.GPR 20#5) u).toNat = reservation.pointer) :
    BitVector.Covers (largeWorkWrites s reservation (left.wordCount + right.wordCount))
      (loopWrites (r (.GPR 31#5) u) (r (.GPR 20#5) u) (left.wordCount + right.wordCount)) := by
  have current := large_sp_nat owned sp
  have stack := owned.stackBound
  intro span member
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨((r (.GPR 31#5) s).toNat - 144, 48), by simp [largeWorkWrites], by omega, by omega⟩
  · exact ⟨(reservation.pointer, 8 * (left.wordCount + right.wordCount)),
      by simp [largeWorkWrites], by rw [pointer], by rw [pointer]⟩

theorem LargeReservation.loop_space {s u : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    (pointer : (r (.GPR 20#5) u).toNat = reservation.pointer) :
    LoopSpace (r (.GPR 31#5) u) (r (.GPR 20#5) u) (left.wordCount + right.wordCount) := by
  have current := large_sp_nat owned sp
  have stack := owned.stackBound
  have positive := allocated.positive
  refine ⟨by omega, by rw [pointer]; exact allocated.physical, ?_⟩
  rw [pointer]
  rcases allocated.fresh with empty | separate
  · omega
  · have apart := separate _ (List.mem_append_left _ (large_stack_local _ _))
    simp only [Prod.fst, Prod.snd] at apart
    omega

theorem LargeReservation.loop_arena {s u : ArmState} {left right : NatOperand}
    {reservation : SszNative.Arena.Reservation} (allocated : LargeReservation s left right reservation)
    (owned : Owned s left right) (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    (pointer : (r (.GPR 20#5) u).toNat = reservation.pointer) :
    Protected (loopWrites (r (.GPR 31#5) u) (r (.GPR 20#5) u) (left.wordCount + right.wordCount))
      (r (.GPR 5#5) s).toNat 24 := by
  have slot := (large_slot_cover owned sp 48 (by decide)).protected owned.arenaLocal
  have positive := allocated.positive
  right
  intro span member
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rcases slot with empty | separate
    · omega
    · exact separate _ (by simp)
  · rw [pointer]
    rcases allocated.fresh with empty | separate
    · simp only [Prod.fst, Prod.snd]; omega
    · have apart := separate ((r (.GPR 5#5) s).toNat, 24) (by simp)
      simp only [Prod.fst, Prod.snd] at apart ⊢
      omega

end SszArm.NatMul

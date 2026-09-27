import SszArm.NatDivisionArena
import SszArm.NatDivisionMemory

namespace SszArm.NatDivision

open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The checked large path has exactly one possible write: the cursor word,
and that write exists if and only if the shared reservation succeeds. -/
theorem arena_big_reservation_memory {s t : ArmState}
    (base address capacity used : BitVec 64) (words : Nat)
    (post : ArenaReservationPost false s t base address capacity used words)
    (physical : (r (.GPR 21#5) s + 16#64).toNat + 8 ≤ 2^64) :
    match SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words with
    | none => t.mem = s.mem
    | some reservation =>
        MemoryFrame [((r (.GPR 21#5) s + 16#64).toNat, 8)] s t ∧
        (read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) t).toNat = reservation.used := by
  rcases post with ⟨failed, hp, reached⟩ | ⟨allocated, u, reached, hp, pointer, start, finish, result, exit⟩
  · rw [failed]
    exact reached.memory
  · rw [allocated]
    simp only [Bool.false_eq_true, ↓reduceIte] at hp pointer start finish result
    subst t
    have header := reached.frame.registers 21#5 (by decide)
    have committed := arena_big_store_memory u base (by simpa only [header] using physical)
    constructor
    · intro a outside
      rw [committed.1 a (by simpa only [header] using outside), reached.memory]
    · rw [← header, committed.2]
      exact finish

/-- The width-two path commits precisely the two quotient words, not merely its
normalized descriptor. All premises here are physical allocation geometry. -/
theorem arena_small_reservation_memory {s t : ArmState}
    (base address capacity used : BitVec 64)
    (post : ArenaReservationPost true s t base address capacity used 2)
    (physical : (r (.GPR 21#5) s + 16#64).toNat + 8 ≤ 2^64)
    (fresh : ∀ reservation,
      SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some reservation →
      0 < reservation.pointer ∧ reservation.pointer % 8 = 0 ∧
      reservation.pointer + 16 ≤ 2^64 ∧
      ((r (.GPR 21#5) s + 16#64).toNat + 8 ≤ reservation.pointer ∨
        reservation.pointer + 16 ≤ (r (.GPR 21#5) s + 16#64).toNat)) :
    match SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
    | none => t.mem = s.mem
    | some reservation =>
        MemoryFrame [((r (.GPR 21#5) s + 16#64).toNat, 8), (reservation.pointer, 16)] s t ∧
        (read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) t).toNat = reservation.used ∧
        SszNative.NatMemory.Pair (UintCodec.widthLoad t) (BitVec.ofNat 64 reservation.pointer) 2#64
          ((r (.GPR 0#5) s).toNat + 2^64 * (r (.GPR 1#5) s).toNat) := by
  rcases post with ⟨failed, hp, reached⟩ | ⟨allocated, u, reached, hp, pointer, start, finish, result, exit⟩
  · rw [failed]
    exact reached.memory
  · have geometry := fresh _ allocated
    rw [allocated]
    simp only [↓reduceIte] at hp result
    change r (.GPR 8#5) u = address at pointer
    change (r (.GPR 9#5) u).toNat = SszNative.Arena.start address.toNat used.toNat at start
    change (r (.GPR 10#5) u).toNat = SszNative.Arena.finish address.toNat used.toNat 2 at finish
    subst t
    have header := reached.frame.registers 21#5 (by decide)
    have pointerNat : (arenaSmallPointer u).toNat =
        address.toNat + SszNative.Arena.start address.toNat used.toNat := by
      simp only [arenaSmallPointer, BitVec.toNat_add, pointer, start]
      exact Nat.mod_eq_of_lt (by have h := geometry.2.2.1; dsimp only at h; omega)
    have owned : ArenaSmallOwned u := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [header] using physical
      · simpa only [pointerNat] using geometry.1
      · simpa only [pointerNat] using geometry.2.1
      · simpa only [pointerNat] using geometry.2.2.1
      · simpa only [pointerNat, header] using geometry.2.2.2
    have committed := arena_small_store_memory u base owned hp
    refine ⟨?_, ?_, ?_⟩
    · intro a outside
      rw [committed.1 a (by simpa only [header, pointerNat] using outside), reached.memory]
    · rw [← header, committed.2.1]
      exact finish
    · have ptr : arenaSmallPointer u =
          BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [pointerNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        have h := geometry.2.2.1
        dsimp only at h
        omega
      simpa only [ptr, reached.frame.registers 0#5 (by decide),
        reached.frame.registers 1#5 (by decide)] using committed.2.2

theorem arena_small_reservation_frame {s t : ArmState}
    (base address capacity used : BitVec 64)
    (post : ArenaReservationPost true s t base address capacity used 2) :
    ArenaFrame s t := by
  rcases post with ⟨failed, hp, reached⟩ |
    ⟨allocated, u, reached, hp, pointer, start, finish, result, exit, count⟩
  · exact reached.frame
  · subst t
    exact reached.frame.trans (arena_small_store_frame u base)

/-- Opaque terminal register facts for starting the large copy loop at452. -/
theorem arena_big_reservation_success_registers {s t : ArmState}
    (base address capacity used : BitVec 64) (words : Nat)
    (post : ArenaReservationPost false s t base address capacity used words)
    (reservation : SszNative.Arena.Reservation)
    (success : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat words =
      some reservation) :
    read_pc t = base + 452#64 ∧
    r (.GPR 8#5) t = r (.GPR 8#5) s ∧
    r (.GPR 9#5) t = 0#64 ∧
    r (.GPR 24#5) t = BitVec.ofNat 64 reservation.pointer ∧
    t.program = s.program ∧ read_err t = read_err s ∧
    (∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s) ∧
    (∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 24#5] →
      r (.GPR reg) t = r (.GPR reg) s) := by
  rcases post with ⟨failed, hp, reached⟩ |
    ⟨allocated, u, reached, hp, pointer, start, finish, result, exit, count⟩
  · rw [failed] at success
    contradiction
  · have same := Option.some.inj (allocated.symm.trans success)
    subst reservation
    simp only [Bool.false_eq_true, ↓reduceIte] at hp result exit
    change r (.GPR 10#5) u = address at pointer
    change (r (.GPR 11#5) u).toNat = SszNative.Arena.start address.toNat used.toNat at start
    change (r (.GPR 12#5) u).toNat = SszNative.Arena.finish address.toNat used.toNat words at finish
    subst t
    have effect := arena_big_store_effect u base
    refine ⟨exit, count rfl, effect.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [effect.2.2.1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, pointer, start, BitVec.toNat_ofNat]
    · exact (block_program _ _ _).trans reached.frame.program
    · exact (block_error _ _ _).trans reached.frame.error
    · intro reg
      have unchanged : r (.SFP reg) (block base arenaBigStoreOps u) = r (.SFP reg) u := by
        simp [arenaBigStoreOps, block, Op.effect, put, next, state_simp_rules]
      exact unchanged.trans (reached.frame.vectors reg)
    · intro reg hr
      have hstore : reg ∉ [9#5, 24#5] := by simp_all
      have hguards : reg ∉ [8#5, 9#5, 10#5, 11#5, 12#5, 13#5] := by simp_all
      exact (arena_big_store_registers u base reg hstore).trans (reached.frame.registers reg hguards)

end SszArm.NatDivision

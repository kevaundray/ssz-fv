import SszArm.NatDivisionEntry
import SszArm.NatDivisionLoopMemory

namespace SszArm.NatDivision

open Delimited (Protected)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Allocation geometry follows from the real checks and physical storage
ownership. Neither a valid old cursor nor a signed capacity bound is assumed. -/
theorem Owned.allocation_geometry {s : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned s operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome s operand).allocation = some reservation) :
    0 < reservation.pointer ∧ reservation.pointer < 2^64 ∧
      reservation.pointer % 8 = 0 ∧
      reservation.pointer + 8 * (outcome s operand).written.length ≤ 2^64 := by
  have resources := SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) s)
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used reservation allocated
  have length : (outcome s operand).written.length =
      (if operand.wordCount ≤ 2 then 2 else operand.wordCount) := resources.2.1
  have positive : 0 < (outcome s operand).written.length := by
    rw [length]
    split <;> omega
  have checks := resources.2.2.1
  have pointer := resources.2.2.2.1
  have capacity := checks.2.2.2.2.2
  have capacityPositive : 0 < (arenaOf s).capacity := by
    unfold SszNative.Arena.finish at capacity
    omega
  have basePositive := owned.arenaNonnull capacityPositive
  have endBound : reservation.pointer + 8 * (outcome s operand).written.length ≤ 2^64 := by
    have storage := owned.arenaStorage
    rw [pointer, length]
    unfold SszNative.Arena.finish at capacity
    omega
  refine ⟨by rw [pointer]; omega, by omega, ?_, endBound⟩
  rw [pointer, SszNative.Arena.start_pointer]
  exact SszNative.Arena.aligned_mod _

theorem loopWords_of_words (s : ArmState) (pointer : BitVec 64)
    (words : List (BitVec 64)) (stored : NatCompare.Words s pointer words) :
    LoopWords s pointer words := by
  intro i hi
  exact stored ⟨i, hi⟩

theorem words_of_loopWords (s : ArmState) (pointer : BitVec 64)
    (words : List (BitVec 64)) (stored : LoopWords s pointer words) :
    NatCompare.Words s pointer words := by
  intro i
  exact stored i.val i.isLt

/-- Every final quotient word can be transferred into the shared observation
model before separately normalizing the returned Nat representation. -/
theorem loopWords_at (s : ArmState) (pointer : BitVec 64)
    (words : List (BitVec 64)) (stored : LoopWords s pointer words) :
    SszNative.NatMemory.wordsAt (widthLoad s) pointer.toNat words := by
  intro i
  have h := congrArg BitVec.toNat (stored i.val i.isLt)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using congrArg some h

theorem Owned.loop_space {original current : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (sp : r (.GPR 31#5) current = r (.GPR 31#5) original - 64#64) :
    LoopSpace (r (.GPR 31#5) current) (BitVec.ofNat 64 reservation.pointer)
      (outcome original operand).written.length := by
  have geometry := owned.allocation_geometry reservation allocated
  have positive := geometry.1
  have bounded := geometry.2.1
  have extent := geometry.2.2.2
  have lower := owned.stackBound
  have fresh := owned.fresh reservation allocated
  have apart : reservation.pointer + 8 * (outcome original operand).written.length ≤
      (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ reservation.pointer := by
    rcases fresh with empty | separate
    · have resources := SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) original)
        (arenaOf original).base (arenaOf original).capacity (arenaOf original).used reservation allocated
      have length := resources.2.1
      change (outcome original operand).written.length = _ at length
      split at length <;> omega
    · have h := separate ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega
  rw [sp]
  refine ⟨by bv_omega, ?_, ?_⟩
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using extent
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    bv_omega

end SszArm.NatDivision

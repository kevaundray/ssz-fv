import SszArm.BitVectorMemory

namespace SszArm.BitVector

open SszNative
open Delimited (Protected MemoryFrame)
open UintCodec (widthLoad)

/-- The first helper's cursor remains within the unsigned caller arena. This
uses exact checked reservations, not the older signed-capacity Arena.Valid. -/
theorem division_cursor_bounds (s : ArmState) (length : NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) :
    (arenaOf s).used ≤ (outcome s length data).divided.used ∧
      (outcome s length data).divided.used ≤ (arenaOf s).capacity := by
  rw [outcome, divided_eq]
  cases allocated : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).allocation with
  | none =>
    have resources := SszNative.NatDivision.no_allocation_resources length 8
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used allocated
    rw [resources.1]
    exact ⟨Nat.le_refl _, owned.arenaUsed⟩
  | some reservation =>
    have resources := SszNative.NatDivision.allocation_resources length 8
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used reservation allocated
    rw [resources.1, resources.2.2.2.2.1]
    have start := Arena.used_le_start (arenaOf s).base (arenaOf s).used
    have checks := resources.2.2.1
    exact ⟨by unfold Arena.finish; omega, checks.2.2.2.2.2⟩

/-- The complete first buffer, not merely the normalized quotient's limbs, ends
at its committed cursor. This is what preserves a redundant zero high limb. -/
theorem division_allocation_end (length : NatOperand) (arena : SszNative.Delimited.ArenaState)
    (reservation : Arena.Reservation)
    (allocated : (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).allocation =
      some reservation) :
    reservation.pointer + 8 *
      (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).written.length =
      arena.base + (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).used := by
  obtain ⟨used, size, checks, pointer, finish, success⟩ :=
    SszNative.NatDivision.allocation_resources length 8 arena.base arena.capacity arena.used
      reservation allocated
  rw [size, pointer, used, finish]
  simp only [Arena.finish, Nat.add_assoc]

/-- Rounding starts at or above the committed division end. Padding between
these extents is charged but remains outside both write footprints. -/
theorem allocations_ordered (length quotient : NatOperand)
    (arena : SszNative.Delimited.ArenaState) (first second : Arena.Reservation)
    (divided : (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).allocation =
      some first)
    (rounded : (SszNative.NatAdd.run quotient (.small 1) arena.base arena.capacity
      (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).used).allocation =
      some second) :
    first.pointer + 8 *
      (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).written.length ≤
      second.pointer := by
  have endAddress := division_allocation_end length arena first divided
  have geometry := SszNative.NatAdd.allocation_geometry quotient (.small 1)
    arena.base arena.capacity
    (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).used second rounded
  have start := Arena.used_le_start arena.base
    (SszNative.NatDivision.run length 8 arena.base arena.capacity arena.used).used
  rw [endAddress, geometry.2.1]
  omega

/-- Word observations transport through a later disjoint stage without exposing
any implementation detail of the earlier allocation loop. -/
theorem written_preserved {s t : ArmState} {writes : List (Nat × Nat)}
    (pointer : Nat) (words : List (BitVec 64))
    (physical : pointer + 8 * words.length ≤ 2^64)
    (owned : Protected writes pointer (8 * words.length))
    (frame : MemoryFrame writes s t)
    (stored : NatMemory.wordsAt (widthLoad s) pointer words) :
    NatMemory.wordsAt (widthLoad t) pointer words := by
  intro index
  have within := index.isLt
  rw [frame.load _ 8 (by omega) (owned.subspan (8 * index.val) 8 (by omega))]
  exact stored index

/-- The public postcondition exposes all first-helper writes even if optional
rounding failed and the returned outer result is ScratchExhausted. -/
theorem Post.divided_written {s t : ArmState} {length : NatOperand} {data : Ssz.Bytes}
    (post : Post s t length data) :
    SszNative.BitVector.allocationAt (widthLoad t)
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used) := by
  simpa only [outcome, divided_eq] using post.written.1

end SszArm.BitVector

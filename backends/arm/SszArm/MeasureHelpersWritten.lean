import SszArm.MeasureHelpersAllocation

namespace SszArm.Measure.Helpers

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

theorem fromWide_written_preserved {writes : List Span} {s t : ArmState}
    (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (frame : MemoryFrame writes s t)
    (input : NatDivision.WrittenAt (widthLoad s)
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide)) :
    NatDivision.WrittenAt (widthLoad t)
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide) := by
  intro reservation allocated index
  have bounds := (resource_fromWide arena wide).allocations _
    (by simp [SszNative.Serialize.fromWide]) reservation allocated
  have count := fromWide_written_length arena wide reservation allocated
  have pointerBound : reservation.pointer < 2^64 := by omega
  have buffer := fromWide_buffer_owned writes arena wide storage free reservation allocated
  change Protected writes (BitVec.ofNat 64 reservation.pointer).toNat _ at buffer
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] at buffer
  have physical : reservation.pointer + 8 *
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).written.length ≤ 2^64 := by
    omega
  have within := index.isLt
  have wordOwned := buffer.subspan (8 * index.val) 8 (by omega)
  rw [frame.load (reservation.pointer + 8 * index.val) 8 (by omega) wordOwned]
  exact input reservation allocated index

end SszArm.Measure.Helpers

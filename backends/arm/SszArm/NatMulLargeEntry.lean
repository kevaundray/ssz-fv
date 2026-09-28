import SszArm.NatMulLargeReserve

namespace SszArm.NatMul

open SszNative (NatOperand)
open Delimited (Protected)

structure LargeStart (s u : ArmState) (base : BitVec 64) (left right : NatOperand) : Prop where
  frame : EntryFrame s u
  pc : read_pc u = base + 412#64
  raw : RawArgs s u
  leftCount : r (.GPR 21#5) u = BitVec.ofNat 64 left.wordCount
  rightCount : r (.GPR 22#5) u = BitVec.ofNat 64 right.wordCount
  payload : r (.GPR 8#5) u = r (.GPR 2#5) s
  previous : r (.GPR 9#5) u = BitVec.ofNat 64 (right.wordCount - 1)

theorem large_start {s u : ArmState} {base : BitVec 64} {left right : NatOperand}
    (frame : EntryFrame s u) (exit : DispatchExit s u base left.words right.words)
    (largeLeft : 1 < left.wordCount) (largeRight : 1 < right.wordCount) :
    LargeStart s u base left right := by
  change 1 < SszNative.Limbs.sigWords left.words at largeLeft
  change 1 < SszNative.Limbs.sigWords right.words at largeRight
  have zero : ¬(SszNative.Limbs.sigWords left.words = 0 ∨ SszNative.Limbs.sigWords right.words = 0) := by omega
  have rightOne : SszNative.Limbs.sigWords right.words ≠ 1 := by omega
  have leftOne : SszNative.Limbs.sigWords left.words ≠ 1 := by omega
  simp only [DispatchExit, if_neg zero, if_neg rightOne, if_neg leftOne] at exit
  rcases exit with ⟨pc, raw, leftCount, rightCount, payload, previous⟩
  exact ⟨frame, pc, raw, leftCount, rightCount, payload, previous⟩

theorem LargeStart.count {s u : ArmState} {base : BitVec 64} {left right : NatOperand}
    (start : LargeStart s u base left right) (owned : Owned s left right) :
    reserveCount u = left.wordCount + right.wordCount := by
  have leftBound := large_count_bound s left owned.leftAt
  have rightBound := large_count_bound s right owned.rightAt
  simp only [reserveCount, start.leftCount, start.rightCount, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]

theorem LargeStart.header {s u : ArmState} {base : BitVec 64} {left right : NatOperand}
    (start : LargeStart s u base left right) (owned : Owned s left right)
    (offset : Nat) (bound : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 5#5) u + BitVec.ofNat 64 offset) u =
      read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) s := by
  rw [start.frame.arena]
  exact large_header_read owned start.frame.memory
    ((entry_local_covered s (outcome s left right)).protected owned.arenaLocal) offset bound

theorem LargeStart.header_stack {s u : ArmState} {base : BitVec 64} {left right : NatOperand}
    (start : LargeStart s u base left right) (owned : Owned s left right) :
    (r (.GPR 5#5) u).toNat + 24 ≤ (r (.GPR 31#5) u).toNat - 16 ∨
      (r (.GPR 31#5) u).toNat ≤ (r (.GPR 5#5) u).toNat := by
  have slot := (large_slot_cover owned start.frame.sp 16 (by decide)).protected owned.arenaLocal
  have physical := (ReturnSpace.of_owned owned start.frame.saved).stack
  rw [start.frame.arena]
  rcases slot with empty | separate
  · omega
  · have apart := separate _ (by simp)
    simp only [Prod.fst, Prod.snd] at apart
    omega

theorem LargeStart.cursor_separate {s u : ArmState} {base : BitVec 64} {left right : NatOperand}
    (start : LargeStart s u base left right) (owned : Owned s left right)
    (largeLeft : 1 < left.wordCount) (largeRight : 1 < right.wordCount)
    (checks : SszNative.Arena.Checks (arenaOf s).base (arenaOf s).capacity (arenaOf s).used (reserveCount u)) :
    (r (.GPR 5#5) u + 16#64).toNat + 8 ≤
        (arenaOf s).base + SszNative.Arena.start (arenaOf s).base (arenaOf s).used ∨
      (arenaOf s).base + SszNative.Arena.finish (arenaOf s).base (arenaOf s).used (reserveCount u) ≤
        (r (.GPR 5#5) u + 16#64).toNat := by
  rw [start.count owned] at checks ⊢
  let reservation : SszNative.Arena.Reservation :=
    ⟨(arenaOf s).base + SszNative.Arena.start (arenaOf s).base (arenaOf s).used,
     SszNative.Arena.finish (arenaOf s).base (arenaOf s).used (left.wordCount + right.wordCount)⟩
  have reserved := (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ _
    (by omega) reservation).2 ⟨checks, rfl⟩
  have allocated := large_reservation owned largeLeft largeRight reservation reserved
  have physical := owned.arenaBound
  have cursor : (r (.GPR 5#5) u + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by
    rw [start.frame.arena]; bv_omega
  rw [cursor]
  rcases allocated.fresh with empty | separate
  · omega
  · have apart := separate ((r (.GPR 5#5) s).toNat, 24) (by simp)
    simp only [Prod.fst, Prod.snd, reservation, SszNative.Arena.finish] at apart ⊢
    omega

end SszArm.NatMul

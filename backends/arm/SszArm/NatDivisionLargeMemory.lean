import SszArm.NatDivisionCopy
import SszArm.NatDivisionLoop
import SszArm.NatDivisionBodyMemory
import SszArm.NatDivisionAllocated

namespace SszArm.NatDivision

open Delimited (MemoryFrame Protected)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem CopyFrame.tight_memory {s t : ArmState} {destination : BitVec 64} {count : Nat}
    (frame : CopyFrame destination count s t) :
    MemoryFrame (loopWrites (r (.GPR 31#5) s) destination count) s t := by
  intro a outside
  apply frame.memory a
  · have h := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [loopWrites])
    simp only [Prod.fst, Prod.snd] at h
    omega
  · exact outside (destination.toNat, 8 * count) (by simp [loopWrites])

/-- The complete copied/divided payload is the shared model's written extent,
so a tight in-place-loop frame embeds in the exact allocation-dependent frame. -/
theorem payload_body_frame {original s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (frame : MemoryFrame (loopWrites (r (.GPR 31#5) s) (BitVec.ofNat 64 reservation.pointer)
      (outcome original operand).written.length) s t) :
    MemoryFrame (bodyWrites original operand) s t := by
  have bounded := (owned.allocation_geometry reservation allocated).2.1
  have lower := owned.stackBound
  have slot : (r (.GPR 31#5) s).toNat - 16 = (r (.GPR 31#5) original).toNat - 80 := by
    rw [sp]
    bv_omega
  apply frame.weaken
  intro span member
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [bodyWrites, allocated, slot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]

theorem Owned.input_allocation_separate {original : ArmState} (pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned original (.large pointer words))
    (nonempty : 0 < words.length) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original (.large pointer words)).allocation = some reservation) :
    pointer.toNat + 8 * words.length ≤ reservation.pointer ∨
      reservation.pointer + 8 * (outcome original (.large pointer words)).written.length ≤ pointer.toNat := by
  have inputOwned := owned.operandOwned
  change Protected (writesFor original (outcome original (.large pointer words)))
    pointer.toNat (8 * words.length) at inputOwned
  rcases inputOwned with empty | separate
  · omega
  · exact separate (reservation.pointer, 8 * (outcome original (.large pointer words)).written.length)
      (by simp [writesFor, allocated])

/-- Neither copying nor reverse division can rewrite the already-committed
cursor: the payload and lowering-slot ownership both exclude the descriptor. -/
theorem Owned.payload_cursor {original current : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (reservation : SszNative.Arena.Reservation)
    (allocated : (outcome original operand).allocation = some reservation)
    (sp : r (.GPR 31#5) current = r (.GPR 31#5) original - 64#64) :
    Protected (loopWrites (r (.GPR 31#5) current) (BitVec.ofNat 64 reservation.pointer)
      (outcome original operand).written.length)
      ((r (.GPR 4#5) original).toNat + 16) 8 := by
  have bounded := (owned.allocation_geometry reservation allocated).2.1
  have stack := owned.stackBound
  have arenaApart : (r (.GPR 4#5) original).toNat + 24 ≤ (r (.GPR 31#5) original).toNat - 80 ∨
      (r (.GPR 31#5) original).toNat ≤ (r (.GPR 4#5) original).toNat := by
    rcases owned.arenaLocal with empty | separate
    · omega
    · have h := separate ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
      simp only [Prod.fst, Prod.snd] at h
      omega
  have payloadApart : reservation.pointer + 8 * (outcome original operand).written.length ≤
      (r (.GPR 4#5) original).toNat ∨
      (r (.GPR 4#5) original).toNat + 24 ≤ reservation.pointer := by
    rcases owned.fresh reservation allocated with empty | separate
    · have resources := SszNative.NatDivision.allocation_resources operand (r (.GPR 3#5) original)
        (arenaOf original).base (arenaOf original).capacity (arenaOf original).used reservation allocated
      have length := resources.2.1
      change (outcome original operand).written.length = _ at length
      split at length <;> omega
    · exact separate ((r (.GPR 4#5) original).toNat, 24) (by simp)
  right
  intro span member
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp only [Prod.fst, Prod.snd]
    rw [sp]
    bv_omega
  · simp only [Prod.fst, Prod.snd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
    omega

theorem LoopSpace.source {s : ArmState} {pointer : BitVec 64} {words : List (BitVec 64)}
    (space : LoopSpace (r (.GPR 31#5) s) pointer words.length) :
    NatCompare.Source s pointer words := ⟨space.stack, space.physical, Or.inr space.apart⟩

end SszArm.NatDivision

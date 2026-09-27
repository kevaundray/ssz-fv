import SszX86.NatDivisionCopy
import SszX86.NatDivisionFrame

namespace SszX86.NatDivision.Copy
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every byte of a disjoint physical region survives the complete copy. -/
theorem Ready.bytes_apart {s t : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat} (ready : Ready s t destination words count)
    (p : BitVec 64) (n : Nat) (apart : Large.Disjoint p destination n (8*count)) :
    ∀ i < n, t.dmem.get? (p + BitVec.ofNat 64 i) = s.dmem.get? (p + BitVec.ofNat 64 i) := by
  intro i hi
  exact ready.frame _ (apart i hi)

/-- A copy frame transports concrete loads, including the output spill and CALL slot. -/
theorem Ready.load_apart {s t : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat} (ready : Ready s t destination words count)
    (p : BitVec 64) (n : Nat) (apart : Large.Disjoint p destination n (8*count)) :
    Mem.loadInt t.dmem p n = Mem.loadInt s.dmem p n := by
  apply memmove_loadInt_congr
  exact ready.bytes_apart p n apart

/-- The copy only adds mappings; this does not require destination separation. -/
theorem Ready.mapped {s t : MachineData} {destination p : BitVec 64}
    {words : List (BitVec 64)} {count n : Nat} (ready : Ready s t destination words count)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped t.dmem p n := by
  rw [ready.copied]
  exact memory_mapped s.dmem destination p words count n hm

/-- The copied prefix occupies exactly the already-authorized allocation. -/
theorem Ready.outcome_frame {before after : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat}
    (ready : Ready before after destination words count)
    (original : MachineData) (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
    (reservation : Arena.Reservation) (allocated : outcome.allocation = some reservation)
    (pointer : destination.toNat = reservation.pointer)
    (length : outcome.written.length = count)
    (bound : destination.toNat + 8*count ≤ 2^64)
    (frame : NatDivision.Frame original before.dmem outcome) :
    NatDivision.Frame original after.dmem outcome := by
  intro a output activation allocation
  have outside := (allocation reservation allocated).2
  rw [length, ← pointer] at outside
  rw [ready.frame a (fun i hi => Body.outside_byte destination a (8*count) i bound outside hi)]
  exact frame a output activation allocation

/-- Saved registers are read at offsets8..55 from the copy's fixed stack pointer. -/
theorem Ready.saved {before after : MachineData} {destination : BitVec 64}
    {words : List (BitVec 64)} {count : Nat}
    (ready : Ready before after destination words count)
    (original : MachineData) (sp : BitVec 64)
    (apart : Large.Disjoint sp destination 56 (8*count))
    (saved : SavedAt before.dmem sp original) : SavedAt after.dmem sp original := by
  apply savedAt_congr before.dmem after.dmem sp original _ saved
  intro i hi
  apply ready.frame
  intro j hj
  have separation := apart (8+i) (by omega) j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using separation

end SszX86.NatDivision.Copy

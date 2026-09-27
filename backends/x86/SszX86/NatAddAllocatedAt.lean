import SszX86.NatAddProtected

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The complete allocated buffer is physically a Large before from_words
normalizes its borrowed prefix; the redundant carry slot remains observable. -/
theorem allocated_at (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written) :
    (NatOperand.large (BitVec.ofNat 64 r.pointer)
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written).At (widthLoad m) := by
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have positive : 0 < (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length := by
    rw [geometry.2.2.2]
    split <;> omega
  have pointerBound : r.pointer < 2^64 := by omega
  simp only [NatOperand.At, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.2.2.2, written⟩

end SszX86.NatAdd

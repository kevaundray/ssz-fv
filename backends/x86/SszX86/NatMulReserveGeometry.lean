import SszX86.NatMulReservePost

namespace SszX86.NatMul.Reservation
open SszNative

/-- The helper destination is the checked reservation's exact pointer. -/
theorem initialized_pointer (s : MachineData) (address capacity used : BitVec 64)
    (positive : 0 < total s) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (total s) = some r)
    (guardFlags fillFlags : StatusFlags) :
    (initializedState s address used guardFlags fillFlags).regs.rdi.toBitVec =
      BitVec.ofNat 64 r.pointer := by
  have geometry := ((Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).mp reserved).2
  rw [geometry]
  simp [initializedState, preparedState, allocatedState, reservedState,
    BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The store's end cursor consumes the full zero-filled product, including
high words that normalization will later omit from the returned representation. -/
theorem initialized_end (s : MachineData) (address capacity used : BitVec 64)
    (positive : 0 < total s) (bound : total s < 2^64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (total s) = some r)
    (guardFlags : StatusFlags) :
    (allocatedState s address used guardFlags).regs.r11.toBitVec = BitVec.ofNat 64 r.used := by
  have geometry := ((Arena.reserve_eq_some_iff_checks _ _ _ _ positive r).mp reserved).2
  rw [geometry]
  simp only [allocatedState, reservedState, counted_nat s s.status bound,
    UInt64.toBitVec_ofNat', Arena.Reservation.used]

/-- The right scan leaves one minus its significant count in R10; the actual
SUB at 452 therefore caches total minus one, not total. -/
theorem initialized_last_index (s : MachineData) (address used : BitVec 64)
    (right : s.regs.r10.toBitVec = 1#64 - s.regs.r13.toBitVec)
    (positive : 0 < total s) (bound : total s < 2^64)
    (guardFlags fillFlags : StatusFlags) :
    (initializedState s address used guardFlags fillFlags).regs.rbp.toBitVec =
      BitVec.ofNat 64 (total s - 1) := by
  simp only [initializedState, preparedState, allocatedState, reservedState, countState,
    UInt64.toBitVec_ofBitVec, right]
  unfold total at *
  bv_omega

end SszX86.NatMul.Reservation

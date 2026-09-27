import SszX86.NatDivisionReserveSmall
import SszX86.NatDivisionReserveLarge
import SszX86.DelimitedWorkMemory

namespace SszX86.NatDivision.Reservation.Small
open SszX86.NatDivision
open SszX86.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- No padding, source, output, or stack byte outside the three written words is
modified by a successful two-word quotient reservation. -/
theorem reserved_frame (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags) (p : BitVec 64)
    (header : ∀ j < 8, p ≠ s.regs.r12.toBitVec + 16#64 + BitVec.ofNat 64 j)
    (payload : ∀ j < 16, p ≠
      BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) +
        BitVec.ofNat 64 j) :
    (reservedState s address used flags).dmem.get? p = s.dmem.get? p := by
  dsimp only [reservedState]
  refine Eq.trans (b := (Mem.storeInt (Mem.storeInt s.dmem (s.regs.r12.toBitVec + 16#64) 8
    (BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat + 16)).toInt)
    (BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat)) 8
    s.regs.rax.toBitVec.toInt).get? p) ?_ ?_
  · apply memmove_store_lookup_outside
    intro j hj
    simpa only [memmove_addr_add] using payload (8+j)
      (by simp only [Int.toBytes_length] at hj; omega)
  refine Eq.trans (b := (Mem.storeInt s.dmem (s.regs.r12.toBitVec + 16#64) 8
    (BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat + 16)).toInt).get? p) ?_ ?_
  · apply memmove_store_lookup_outside
    intro j hj
    exact payload j (by simp only [Int.toBytes_length] at hj; omega)
  · apply memmove_store_lookup_outside
    intro j hj
    exact header j (by simpa only [Int.toBytes_length] using hj)

/-- Payload/header disjointness is physical, not a reserve-success premise.
Under it the cursor commit survives both quotient stores exactly. -/
theorem reserved_cursor (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags)
    (bound : SszNative.Arena.start address.toNat used.toNat + 16 < 2^64)
    (apart : ∀ i < 8, ∀ j < 16,
      s.regs.r12.toBitVec + 16#64 + BitVec.ofNat 64 i ≠
        BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat) +
          BitVec.ofNat 64 j) :
    BoolCodec.observe (reservedState s address used flags).dmem s.regs.r12.toBitVec 16 8 =
      some (SszNative.Arena.start address.toNat used.toNat + 16) := by
  let pointer := BitVec.ofNat 64 (address.toNat + SszNative.Arena.start address.toNat used.toNat)
  have low (m : DataMem) (v : Int) :
      Mem.loadInt (Mem.storeInt m pointer 8 v) (s.regs.r12.toBitVec + 16#64) 8 =
        Mem.loadInt m (s.regs.r12.toBitVec + 16#64) 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    exact apart i hi j (by omega)
  have high (m : DataMem) (v : Int) :
      Mem.loadInt (Mem.storeInt m (pointer + 8#64) 8 v) (s.regs.r12.toBitVec + 16#64) 8 =
        Mem.loadInt m (s.regs.r12.toBitVec + 16#64) 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    simpa only [memmove_addr_add] using apart i hi (8+j) (by omega)
  simp only [reservedState, BoolCodec.observe]
  rw [high, low]
  have exactCursor := BoolCodec.observe_store64 s.dmem s.regs.r12.toBitVec 16
    (BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat + 16))
  simpa only [BoolCodec.observe, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using exactCursor

/-- Both quotient limbs are observable exactly, including a zero low limb.
The high limb is written even when normalization could later shorten a result. -/
theorem reserved_payload (s : MachineData) (address used : BitVec 64)
    (flags : StatusFlags)
    (room : address.toNat + SszNative.Arena.start address.toNat used.toNat + 16 ≤ 2^64) :
    let pointer := BitVec.ofNat 64
      (address.toNat + SszNative.Arena.start address.toNat used.toNat)
    BoolCodec.observe (reservedState s address used flags).dmem pointer 0 8 =
      some s.regs.rax.toNat ∧
    BoolCodec.observe (reservedState s address used flags).dmem pointer 8 8 =
      some s.regs.rdx.toNat := by
  let pointer := BitVec.ofNat 64
    (address.toNat + SszNative.Arena.start address.toNat used.toNat)
  have bound : pointer.toNat + 16 ≤ 2^64 := by
    dsimp only [pointer]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact room
  have disjoint (m : DataMem) (v : Int) :
      Mem.loadInt (Mem.storeInt m (pointer + 8#64) 8 v) pointer 8 =
        Mem.loadInt m pointer 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj equal
    have equal' : pointer + BitVec.ofNat 64 i =
        pointer + BitVec.ofNat 64 (8+j) := by
      simpa only [memmove_addr_add] using equal
    have positions := memmove_addr_injective pointer 16 i (8+j) bound
      (by omega) (by omega) equal'
    omega
  simp only [reservedState, BoolCodec.observe, BitVec.add_zero]
  rw [disjoint]
  simp only [pointer, stored_word_load, Option.map_some, Int.toNat_natCast,
    UInt64.toNat_toBitVec]
  exact ⟨True.intro, True.intro⟩

/-- Reservation never unmaps source/input memory, including on payload aliasing. -/
theorem reserved_mapped (s : MachineData) (address used base : BitVec 64)
    (flags : StatusFlags) (count : Nat) (hm : UintCodec.Large.Mapped s.dmem base count) :
    UintCodec.Large.Mapped (reservedState s address used flags).dmem base count := by
  dsimp only [reservedState]
  repeat' first | exact hm | apply UintCodec.Large.mapped_store

end SszX86.NatDivision.Reservation.Small

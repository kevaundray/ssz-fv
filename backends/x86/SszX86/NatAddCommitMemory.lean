import SszX86.NatAddWorkMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The single cursor store used before any successfully reserved limb writes. -/
def cursorMem (s : MachineData) (m : DataMem) (used : Nat) : DataMem :=
  Mem.storeInt m (s.regs.r9.toBitVec + 16#64) 8 (BitVec.ofNat 64 used).toInt

theorem allocated_pointer_nat (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    (BitVec.ofNat 64 r.pointer).toNat = r.pointer := by
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have positive : 0 < (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length := by
    rw [geometry.2.2.2]
    split <;> omega
  have bound : r.pointer < 2^64 := by omega
  exact Nat.mod_eq_of_lt bound

theorem WorkFrame.cursor_store {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (work : WorkFrame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    WorkFrame s (cursorMem s m (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) := by
  intro a output scratch
  apply Eq.trans (memmove_store_lookup_outside m _ a _ ?_) (work a output scratch)
  intro i hi
  have inside : i < 8 := by simpa only [Int.toBytes_length] using hi
  have outside := (scratch r allocated).1
  have bound := owned.header_bound
  change Body.Outside a.toNat (s.regs.r9.toBitVec.toNat+16) 8 at outside
  change s.regs.r9.toBitVec.toNat + 24 ≤ 2^64 at bound
  unfold Body.Outside at outside
  bv_omega

theorem cursor_store_value (s : MachineData) (m : DataMem) (value : Nat) (bound : value < 2^64) :
    widthLoad (cursorMem s m value) (s.regs.r9.toNat+16) 8 = some value := by
  change widthLoad (cursorMem s m value) (s.regs.r9.toBitVec.toNat+16) 8 = some value
  simpa only [cursorMem, widthLoad, width_address, BoolCodec.observe,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using
    BoolCodec.observe_store64 m s.regs.r9.toBitVec 16 (BitVec.ofNat 64 value)

/-- Any exact full-buffer write frame composes with the cursor-only frame. -/
theorem WorkFrame.buffer {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (r : Arena.Reservation) (allocated : outcome.allocation = some r)
    (buffer : ∀ a : BitVec 64, Body.Outside a.toNat r.pointer (8*outcome.written.length) →
      after.get? a = before.get? a) : WorkFrame s after outcome := by
  intro a output scratch
  exact (buffer a (scratch r allocated).2).trans (work a output scratch)

theorem WorkFrame.fill {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    {m : DataMem} (work : WorkFrame s m
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    WorkFrame s (Large.fillMem m (BitVec.ofNat 64 r.pointer) 0
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written)
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat) := by
  apply work.buffer r allocated
  intro a outside
  apply Large.fill_frame
  intro i low high
  apply Body.outside_byte (BitVec.ofNat 64 r.pointer) a _ i
  · rw [allocated_pointer_nat s left right address capacity used ra owned r allocated]
    exact (allocation_bounds s left right address capacity used ra owned r allocated).2.2.2.2.2
  · simpa only [allocated_pointer_nat s left right address capacity used ra owned r allocated] using outside
  · simpa only [Nat.zero_add] using high

/-- The allocator header is disjoint from every newly written limb, even when
read-only inputs alias the arena's already-used prefix. -/
theorem cursor_after_buffer (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (before after : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (buffer : ∀ a : BitVec 64,
      Body.Outside a.toNat r.pointer
        (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) →
      after.get? a = before.get? a) :
    widthLoad after (s.regs.r9.toNat+16) 8 = widthLoad before (s.regs.r9.toNat+16) 8 := by
  unfold widthLoad
  congr 1
  apply memmove_loadInt_congr
  intro i hi
  apply buffer
  have bound := owned.header_bound
  have natural : (BitVec.ofNat 64 (s.regs.r9.toNat+16) + BitVec.ofNat 64 i).toNat =
      s.regs.r9.toNat+16+i := by bv_omega
  rw [natural]
  have bounds := allocation_bounds s left right address capacity used ra owned r allocated
  have apart := owned.arena_header
  have usedBound := owned.used_bound
  unfold Body.Outside Body.Apart at *
  omega

end SszX86.NatAdd

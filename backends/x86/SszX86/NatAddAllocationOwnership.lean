import SszX86.NatAddReserveMemory
import SszX86.NatAddCarryMath

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem allocated_operand_apart (s : MachineData) (left right operand : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (stored : operand.At (widthLoad s.dmem)) (protection : OperandProtected s address capacity used operand)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    Carry.Apart operand (BitVec.ofNat 64 r.pointer)
      (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have pointerNat := allocated_pointer_nat s left right address capacity used ra owned r allocated
    apply Body.apart_bytes
    · exact stored.2.2.1
    · rw [pointerNat]
      exact bounds.2.2.2.2.2
    · rw [pointerNat]
      have apart := protection.arena
      have usedBound := owned.used_bound
      unfold Body.Apart at *
      omega

theorem allocated_mapped (left right : NatOperand) (address capacity used : BitVec 64)
    (m : DataMem) (hm : Large.Mapped m address capacity.toNat) (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r) :
    Large.Mapped m (BitVec.ofNat 64 r.pointer)
      (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) := by
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have bounded := Reservation.Small.mapped_subrange m address capacity.toNat
    (Arena.start address.toNat used.toNat)
    (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length)
    hm geometry.1.2.2.2.2.2
  have pointer : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) =
      BitVec.ofNat 64 r.pointer := by
    simp only [geometry.2.1, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [pointer] at bounded
  exact bounded

/-- A carry loop's exact buffer frame preserves the preexisting mapped output
region; no disjointness between the immutable operands is imposed. -/
theorem output_mapped_after_buffer (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (before after : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (hm : Large.Mapped before s.regs.rdi.toBitVec 68)
    (buffer : ∀ a : BitVec 64, Body.Outside a.toNat r.pointer
      (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) →
      after.get? a = before.get? a) : Large.Mapped after s.regs.rdi.toBitVec 68 := by
  intro i hi
  obtain ⟨byte, old⟩ := hm i hi
  refine ⟨byte, ?_⟩
  rw [buffer]
  · exact old
  · have outBound := owned.output_bound
    have natural : (s.regs.rdi.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rdi.toNat+i := by
      change s.regs.rdi.toBitVec.toNat + 68 ≤ 2^64 at outBound
      change (s.regs.rdi.toBitVec + BitVec.ofNat 64 i).toNat = s.regs.rdi.toBitVec.toNat+i
      bv_omega
    rw [natural]
    have bounds := allocation_bounds s left right address capacity used ra owned r allocated
    have apart := owned.arena_output
    have usedBound := owned.used_bound
    unfold Body.Outside Body.Apart at *
    omega

end SszX86.NatAdd

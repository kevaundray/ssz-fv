import SszX86.NatDivisionLargeProofMemory
import SszX86.NatDivisionReserveWideResources

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem large_operand_shape (operand : NatOperand) (count : 2 < operand.wordCount) :
    ∃ pointer limbs, operand = .large pointer limbs := by
  cases operand with
  | small limb =>
    have bound := Limbs.sigWords_le_length [limb]
    change 2 < Limbs.sigWords [limb] at count
    simp only [List.length_singleton] at bound
    omega
  | large pointer limbs => exact ⟨pointer, limbs, rfl⟩

theorem large_operand_length {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) (count : 2 < operand.wordCount) :
    operand.words.length + 1 < 2^64 ∧ operand.wordCount + 1 < 2^64 ∧
      s.regs.rdx.toBitVec = BitVec.ofNat 64 operand.words.length := by
  obtain ⟨pointer, limbs, rfl⟩ := large_operand_shape operand count
  have bound := owned.operand_at.2.2.1
  have significant := Limbs.sigWords_le_length limbs
  exact ⟨by change limbs.length + 1 < 2^64; omega,
    by change Limbs.sigWords limbs + 1 < 2^64; omega, owned.operand_payload⟩

theorem large_reserved_destination_mapped {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r)
    (before after : StatusFlags) :
    Large.Mapped (largeReservedState s operand address used before after).dmem
      (BitVec.ofNat 64 r.pointer) (8*operand.wordCount) := by
  obtain ⟨checks, canonical⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).1 reserved
  have fits := checks.2.2.2.2.2
  have hm := Reservation.Small.mapped_subrange s.dmem address capacity.toNat
    (Arena.start address.toNat used.toNat) (8*operand.wordCount) owned.arena_mapped
    (by simpa only [Arena.finish] using fits)
  have pointer : BitVec.ofNat 64 r.pointer =
      address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) := by
    rw [canonical]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [pointer]
  exact large_reserved_mapped s operand address used _ before after _ hm

theorem large_reserved_call_slot {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64}
    (owned : Owned s operand divisor address capacity used ra) (before after : StatusFlags) :
    ∃ old, Mem.loadInt (largeReservedState s operand address used before after).dmem
      (s.regs.rsp.toBitVec - 64) 8 = some old := by
  have hm := large_reserved_mapped s operand address used _ before after 64 owned.stack_mapped
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    Large.mapped_load _ _ 64 0 8 hm (by decide)

end SszX86.NatDivision

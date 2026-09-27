import SszX86.NatDivisionLargeProofResources
import SszX86.NatDivisionCopyFinish
import SszX86.NatDivisionReserveFailureFinish

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every copy-entry resource is obtained from the original ownership and the
actual cursor commit, not postulated as a successful-execution premise. -/
theorem large_reserved_ready (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = some r)
    (before after : StatusFlags) :
    Copy.CopyReady s operand divisor address capacity used ra r
      (largeReservedState s operand address used before after) := by
  have lengths := large_operand_length owned count
  obtain ⟨checks, canonical⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).1 reserved
  have pointer : r.pointer = address.toNat + Arena.start address.toNat used.toNat := by
    rw [canonical]
  have phase := SszNative.NatDivision.phase_reserved operand divisor address.toNat
    capacity.toNat used.toNat owned.divisor_nonzero owned.divisor_ne_one count r reserved
  constructor
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, largeCountedState]
  · exact lengths.2.2
  · exact owned.operand_pointer
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, largeCountedState]
  · rfl
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, pointer]
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, pointer,
      BitVec.ofNat_add, BitVec.ofNat_toNat]
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, largeCountedState]
  · exact owned.divisor_register
  · simp [Copy.get, largeReservedState, Reservation.Large.reservedState, largeCountedState]
  · rfl
  · rfl
  · exact large_reserved_destination_mapped owned count r reserved before after
  · exact large_reserved_mapped s operand address used _ before after 68 owned.output_mapped
  · exact large_reserved_frame owned count r reserved before after
  · exact large_reserved_saved owned before after
  · exact large_reserved_spill owned before after
  · exact large_reserved_call_slot owned before after
  · simpa only [phase] using large_reserved_cursor owned count r reserved before after

/-- Full allocated/large arithmetic path, including checked reservation failure,
all physical copying, every linked runtime division call, normalization, and RET.
The original borrowed representation and complete written quotient are retained. -/
theorem large_phase (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount) (flags : StatusFlags) :
    Eventually (step e) (Post s operand divisor address capacity used ra)
      (scanState (prologueState s) (BitVec.ofNat 64 operand.wordCount)
        (BitVec.ofNat 64 operand.wordCount) flags, base + 83) := by
  apply large_counted_cps e base hc s operand divisor address capacity used ra owned count flags
  intro countedFlags
  have lengths := large_operand_length owned count
  have countReg : (largeCountedState s operand countedFlags).regs.rax.toNat = operand.wordCount := by
    simp [largeCountedState, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (by omega : operand.wordCount < 2^64)]
  apply Reservation.Large.reservation_cps e base hc
    (largeCountedState s operand countedFlags) address capacity used
    (large_counted_header owned countedFlags) (by rw [countReg]; omega)
  intro t ready
  change Eventually (step e) (Post s operand divisor address capacity used ra) (t.1, t.2)
  obtain ⟨frame, failure | success⟩ := ready
  · obtain ⟨failed, pc, memory⟩ := failure
    rw [countReg] at failed
    rw [pc]
    apply large_reserve_failure_finish e base hc s t.1 operand divisor address capacity used ra
      owned count failed
    · exact memory
    · have stack := frame.2 .rsp (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
      exact stack
    · exact frame.1
  · obtain ⟨reservation, reserved, pc, after, state⟩ := success
    rw [countReg] at reserved
    rw [pc, state]
    exact Copy.copy_finish e base hc hdiv s
      (largeReservedState s operand address used countedFlags after)
      operand divisor address capacity used ra owned count reservation reserved
      (large_reserved_ready s operand divisor address capacity used ra owned count reservation
        reserved countedFlags after)

end SszX86.NatDivision

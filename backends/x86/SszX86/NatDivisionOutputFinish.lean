import SszX86.NatDivisionOutputPreserve
import SszX86.NatDivisionFrame

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Exact byte footprint used by either private result publication path. -/
abbrev ResultOnly (before after : DataMem) (out : BitVec 64) : Prop :=
  ∀ address, (∀ i < 68, address ≠ out + BitVec.ofNat 64 i) →
    after.get? address = before.get? address

theorem result_only_saved (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem) (sp : BitVec 64)
    (stack : sp = s.regs.rsp.toBitVec - 56)
    (frame : ResultOnly before after s.regs.rdi.toBitVec)
    (saved : SavedAt before sp s) : SavedAt after sp s := by
  apply savedAt_congr before after sp s _ saved
  intro i hi
  apply frame
  intro j hj same
  have low := owned.stack_low
  have bound := owned.output_bound
  have apart := owned.output_stack
  simp only [Body.Apart, ← UInt64.toNat_toBitVec] at apart low bound
  rw [stack] at same
  bv_omega

theorem result_only_cursor (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (before after : DataMem)
    (frame : ResultOnly before after s.regs.rdi.toBitVec) :
    widthLoad after (s.regs.r8.toNat+16) 8 = widthLoad before (s.regs.r8.toNat+16) 8 := by
  exact result_frame_load before after s.regs.rdi.toBitVec frame owned.output_bound
    s.regs.r8.toNat 24 16 8 owned.header_bound owned.header_output (by decide)

end SszX86.NatDivision

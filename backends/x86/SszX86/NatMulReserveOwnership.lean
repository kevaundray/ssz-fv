import SszX86.NatMulReserveSpills
import SszX86.NatMulMemoryActivation

namespace SszX86.NatMul.Reservation
open SszNative
open UintCodec

/-- The exact scan/activation state supplies the complete reservation's storage
contract from initial physical ownership, including aliased immutable inputs. -/
theorem storage_of_active (s current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (memory : current.dmem = pushedMem s)
    (stack : current.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 88#64) :
    Storage current address capacity used := by
  refine ⟨owned.used_bound, ?_, ?_, ?_⟩
  · rw [memory]
    exact pushed_mapped s _ _ owned.free_mapped
  · rw [memory, stack]
    exact owned.local_mapped
  · rw [stack]
    exact owned.free_stack_disjoint

/-- Scanning and activation preserve all three original arena-header loads. -/
theorem header_of_active (s current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (memory : current.dmem = pushedMem s) (arena : current.regs.r9 = s.regs.r9) :
    Header current address capacity used := by
  obtain ⟨addressLoad, capacityLoad, usedLoad⟩ := pushed_header s left right address capacity used ra owned
  refine ⟨?_, ?_, ?_⟩
  · simpa only [memory, arena] using addressLoad
  · simpa only [memory, arena] using capacityLoad
  · simpa only [memory, arena] using usedLoad

/-- Header and stack separation is inherited rather than postulated for the
committed spill values. -/
theorem cursor_stack_of_active (s current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned s left right address capacity used ra)
    (stack : current.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 88#64)
    (arena : current.regs.r9 = s.regs.r9) :
    Large.Disjoint current.regs.rsp.toBitVec (current.regs.r9.toBitVec + 16#64) 40 8 := by
  intro i hi j hj equal
  rw [stack, arena] at equal
  have apart := owned.header_stack
  have low := owned.stack_low
  have bound := owned.header_bound
  change 96 ≤ s.regs.rsp.toBitVec.toNat at low
  change s.regs.r9.toBitVec.toNat + 24 ≤ 2^64 at bound
  change Body.Apart s.regs.r9.toBitVec.toNat 24 (s.regs.rsp.toBitVec.toNat - 96) 96 at apart
  unfold Body.Apart at apart
  bv_omega

end SszX86.NatMul.Reservation

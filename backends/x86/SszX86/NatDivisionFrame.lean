import SszX86.NatDivisionProtected
import SszX86.NatDivisionStack
import SszX86.NatDivisionOutputMemory

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Append an actual store wholly inside the original 64-byte activation.
Both scratch stores at entry RSP-56 and CALL's slot at entry RSP-64 fit this
rule; no arena or output footprint is enlarged. -/
theorem Frame.store_stack {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)}
    (frame : Frame s m outcome) (low : 64 ≤ s.regs.rsp.toNat)
    (distance count : Nat) (value : Int)
    (start : distance ≤ 64) (within : count ≤ distance) :
    Frame s (Mem.storeInt m (s.regs.rsp.toBitVec - BitVec.ofNat 64 distance) count value) outcome := by
  intro a output activation allocation
  have same := stack_store_frame m s.regs.rsp.toBitVec a 64 distance count value start within
    (by
      intro i hi
      simp only [Body.Outside, ← UInt64.toNat_toBitVec] at activation low
      bv_omega)
  exact same.trans (frame a output activation allocation)

/-- The actual successful-result stores append only the designated output68
writes, while preserving the run's exact conditional arena/cursor footprint. -/
theorem Frame.result_success {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)}
    (frame : Frame s m outcome) (bound : s.regs.rdi.toNat + 68 ≤ 2^64)
    (pointer payload remainder : BitVec 64) :
    Frame s (resultSuccessMem m s.regs.rdi.toBitVec pointer payload remainder) outcome := by
  intro a output activation allocation
  have same := result_success_mem_frame m s.regs.rdi.toBitVec pointer payload remainder a
    (by
      intro i hi
      simp only [Body.Outside, ← UInt64.toNat_toBitVec] at output bound
      bv_omega)
  exact same.trans (frame a output activation allocation)

/-- Error publication has the same physical output68 bound and cannot authorize
cursor or arena writes on a failed reservation. -/
theorem Frame.result_error {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)}
    (frame : Frame s m outcome) (bound : s.regs.rdi.toNat + 68 ≤ 2^64) :
    Frame s (resultErrorMem m s.regs.rdi.toBitVec) outcome := by
  intro a output activation allocation
  have same := result_error_mem_frame m s.regs.rdi.toBitVec a
    (by
      intro i hi
      simp only [Body.Outside, ← UInt64.toNat_toBitVec] at output bound
      bv_omega)
  exact same.trans (frame a output activation allocation)

/-- Before a final no-allocation return, the frame already preserves the
original physical arena cursor; no final-result observation is needed. -/
theorem Frame.cursor_unallocated {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64} {m : DataMem}
    (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (owned : Owned s operand divisor address capacity used ra)
    (unallocated : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation =
      none) :
    Mem.loadInt m (s.regs.r8.toBitVec + 16) 8 = some (used.toNat : Int) := by
  have bound := owned.header_bound
  have output := owned.header_output
  have activation := owned.header_stack
  have same : Mem.loadInt m (s.regs.r8.toBitVec + 16) 8 =
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply frame.no_allocation unallocated
    · simp only [Body.Outside, Body.Apart, ← UInt64.toNat_toBitVec] at output bound ⊢
      bv_omega
    · simp only [Body.Outside, Body.Apart, ← UInt64.toNat_toBitVec] at activation bound ⊢
      bv_omega
  exact same.trans owned.used_load

/-- Reconstruct the original physical return-slot load from the final frame.
This is independent of which quotient, allocation, or error branch executed. -/
theorem Frame.return_slot {s : MachineData} {operand : NatOperand}
    {divisor address capacity used ra : BitVec 64} {m : DataMem}
    (frame : Frame s m
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat))
    (owned : Owned s operand divisor address capacity used ra) :
    Mem.loadInt m s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
  have same : Mem.loadInt m s.regs.rsp.toBitVec 8 = Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
    apply memmove_loadInt_congr
    intro i hi
    have preserved := preserves_region s operand divisor address capacity used ra owned m frame
      s.regs.rsp.toNat 8 owned.return_protected i hi
    simpa only [← UInt64.toNat_toBitVec, width_address] using preserved
  exact same.trans owned.return_load

end SszX86.NatDivision

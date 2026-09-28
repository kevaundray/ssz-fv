import SszX86.NatMulWordWorkMemory
import SszX86.NatMulMemoryOutput
import SszX86.NatMulMemoryBuffer

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem WorkFrame.publish {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (publish : NatMul.PublishFrame s before after outcome.result) : WorkFrame s after outcome := by
  intro a output activation scratch
  exact (publish a output).trans (work a output activation scratch)

theorem WorkFrame.buffer {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (r : Arena.Reservation) (allocated : outcome.allocation = some r)
    (buffer : NatMul.BufferFrame before after r.pointer (8*outcome.written.length)) :
    WorkFrame s after outcome := by
  intro a output activation scratch
  exact (buffer a (scratch r allocated).2).trans (work a output activation scratch)

/-- The two real local slots are below, not inside, the six saved words. -/
theorem WorkFrame.store_local {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s m outcome)
    (low : 64 ≤ s.regs.rsp.toNat) (off count : Nat) (inside : off+count ≤ 16) (value : Int) :
    WorkFrame s (Mem.storeInt m ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off) count value) outcome := by
  intro a output activation scratch
  have unchanged :
      (Mem.storeInt m ((s.regs.rsp.toBitVec-64)+BitVec.ofNat 64 off) count value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi equal
    have byte : i < count := by simpa only [Int.toBytes_length] using hi
    change 64 ≤ s.regs.rsp.toBitVec.toNat at low
    change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat-64) 16 at activation
    unfold Body.Outside at activation
    bv_omega
  exact unchanged.trans (work a output activation scratch)

theorem WorkFrame.store_cursor {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s m outcome)
    (r : Arena.Reservation) (allocated : outcome.allocation = some r)
    (headerBound : s.regs.r8.toNat+24 ≤ 2^64) (value : Int) :
    WorkFrame s (Mem.storeInt m (s.regs.r8.toBitVec+16#64) 8 value) outcome := by
  intro a output activation scratch
  have cursor := (scratch r allocated).1
  have unchanged : (Mem.storeInt m (s.regs.r8.toBitVec+16#64) 8 value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi equal
    have byte : i < 8 := by simpa only [Int.toBytes_length] using hi
    change s.regs.r8.toBitVec.toNat+24 ≤ 2^64 at headerBound
    change Body.Outside a.toNat (s.regs.r8.toBitVec.toNat+16) 8 at cursor
    unfold Body.Outside at cursor
    bv_omega
  exact unchanged.trans (work a output activation scratch)

end SszX86.NatMulWord

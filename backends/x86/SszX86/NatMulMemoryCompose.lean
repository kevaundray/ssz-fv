import SszX86.NatMulMemoryStack
import SszX86.NatMulMemoryOutput
import SszX86.NatMulMemoryBuffer

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem WorkFrame.initial (s : MachineData) (outcome : NatArithmetic.Outcome NatOperand) :
    WorkFrame s (pushedMem s) outcome := by
  intro a _ _ _
  rfl

theorem WorkFrame.publish {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (publish : PublishFrame s before after outcome.result) : WorkFrame s after outcome := by
  intro a output activation scratch
  exact (publish a output).trans (work a output activation scratch)

theorem WorkFrame.buffer {s : MachineData} {before after : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s before outcome)
    (r : Arena.Reservation) (allocated : outcome.allocation = some r)
    (buffer : BufferFrame before after r.pointer (8*outcome.written.length)) :
    WorkFrame s after outcome := by
  intro a output activation scratch
  exact (buffer a (scratch r allocated).2).trans (work a output activation scratch)

/-- Local spills and the nested call's return-address store cannot damage the
saved registers; all are inside the lower 48 bytes of the 96-byte activation. -/
theorem WorkFrame.store_local {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s m outcome)
    (low : 96 ≤ s.regs.rsp.toNat) (off count : Nat) (inside : off+count ≤ 48) (value : Int) :
    WorkFrame s (Mem.storeInt m ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off) count value)
      outcome := by
  intro a output activation scratch
  have unchanged :
      (Mem.storeInt m ((s.regs.rsp.toBitVec-96) + BitVec.ofNat 64 off) count value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi equal
    have byte : i < count := by simpa only [Int.toBytes_length] using hi
    change 96 ≤ s.regs.rsp.toBitVec.toNat at low
    change Body.Outside a.toNat (s.regs.rsp.toBitVec.toNat-96) 48 at activation
    unfold Body.Outside at activation
    bv_omega
  exact unchanged.trans (work a output activation scratch)

/-- The model's successful allocation authorizes the sole arena-header write. -/
theorem WorkFrame.store_cursor {s : MachineData} {m : DataMem}
    {outcome : NatArithmetic.Outcome NatOperand} (work : WorkFrame s m outcome)
    (r : Arena.Reservation) (allocated : outcome.allocation = some r)
    (headerBound : s.regs.r9.toNat+24 ≤ 2^64) (value : Int) :
    WorkFrame s (Mem.storeInt m (s.regs.r9.toBitVec+16) 8 value) outcome := by
  intro a output activation scratch
  have cursor := (scratch r allocated).1
  have unchanged : (Mem.storeInt m (s.regs.r9.toBitVec+16) 8 value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro i hi equal
    have byte : i < 8 := by simpa only [Int.toBytes_length] using hi
    change s.regs.r9.toBitVec.toNat+24 ≤ 2^64 at headerBound
    change Body.Outside a.toNat (s.regs.r9.toBitVec.toNat+16) 8 at cursor
    unfold Body.Outside at cursor
    bv_omega
  exact unchanged.trans (work a output activation scratch)

end SszX86.NatMul

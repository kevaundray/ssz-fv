import SszX86.DispatchTransport
import SszX86.BitListFrame

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

/-- The actual caller's continuation and callee-saved registers, measured from
the original entry SP, not a post-dispatch activation. -/
structure Returned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx.toBitVec = s.regs.rbx.toBitVec
  r12 : t.1.regs.r12.toBitVec = s.regs.r12.toBitVec
  r13 : t.1.regs.r13.toBitVec = s.regs.r13.toBitVec
  r14 : t.1.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.1.regs.r15.toBitVec = s.regs.r15.toBitVec
  rbp : t.1.regs.rbp.toBitVec = s.regs.rbp.toBitVec
  return_word : Mem.loadInt t.1.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))

def Preserved (s : MachineData) (address capacity used : BitVec 64) (t : MachineState) : Prop :=
  ∀ p n, ReadOnly s address capacity used p n → ∀ i < n,
    t.1.dmem.get? (BitVec.ofNat 64 (p + i)) = s.dmem.get? (BitVec.ofNat 64 (p + i))

structure CommonPost (s : MachineData) (base : Int64) (ra address capacity used : BitVec 64)
    (t : MachineState) : Prop where
  returned : Returned s ra t
  readonly : Preserved s address capacity used t
  table : TableAt t.1.dmem base

theorem returned_body {s : MachineData} {base : Int64} {kind : Kind} {ra : BitVec 64}
    {t : MachineState} (post : Body.Returned (bodyState s base kind) (saved s ra) t) :
    Returned s ra t := by
  refine ⟨post.pc, ?_, post.rbx, post.r12, post.r13, post.r14, post.r15, post.rbp, ?_⟩
  · have sp := post.sp
    rw [body_sp] at sp
    have eq : s.regs.rsp.toBitVec - 360 + 368 = s.regs.rsp.toBitVec + 8 := by bv_omega
    exact sp.trans eq
  · have ret := post.activation.2.2.2.2.2.2
    rw [body_sp] at ret
    simpa only [show (360 : BitVec 64) = 360#64 by decide, BitVec.sub_add_cancel, saved] using ret

theorem returned_list {s : MachineData} {base : Int64} {kind : Kind} {ra : BitVec 64}
    {t : MachineState} (post : SszX86.BitList.Returned (bodyState s base kind) (saved s ra) t) :
    Returned s ra t := by
  refine ⟨post.pc, ?_, post.rbx, post.r12, post.r13, post.r14, post.r15, post.rbp, ?_⟩
  · have sp := post.sp
    rw [body_sp] at sp
    have eq : s.regs.rsp.toBitVec - 360 + 368 = s.regs.rsp.toBitVec + 8 := by bv_omega
    exact sp.trans eq
  · have ret := post.returnSlot
    rw [body_sp] at ret
    simpa only [BitVec.sub_add_cancel, saved] using ret

theorem ReadOnly.byte {s : MachineData} {address capacity used : BitVec 64}
    {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) (i : Nat) (hi : i < n) :
    (savedMem s).get? (BitVec.ofNat 64 (p + i)) = s.dmem.get? (BitVec.ofNat 64 (p + i)) := by
  rw [BitVec.ofNat_add]
  exact saved_lookup s _ (h.pushes low i hi)

theorem preserved_table {s : MachineData} {base : Int64} {kind : Kind} {ra : BitVec 64}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (h : Owned s base kind ra data address capacity used)
    (preserved : Preserved s address capacity used t) : TableAt t.1.dmem base := by
  intro i hi
  have same := preserved _ _ h.table_owned i hi
  rw [width_address] at same
  exact same.trans (h.table i hi)

end SszX86.Dispatch

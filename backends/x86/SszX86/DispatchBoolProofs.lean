import SszX86.DispatchPost
import SszX86.BoolProofs

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

theorem bool_separated (s : MachineData) (base : Int64) (ra : BitVec 64)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .bool ra data address capacity used) :
    StackSeparated (bodyState s base .bool).regs.rdi.toBitVec
      (bodyState s base .bool).regs.rsp.toBitVec := by
  intro j hj i hi
  rw [body_sp, body_output]
  have apart := h.output_stack
  have low := h.stack_low
  have out := h.output_bound
  have high := h.stack_bound
  clear h
  change Body.Apart s.regs.rdi.toBitVec.toNat 80 (s.regs.rsp.toBitVec.toNat - 472) 480 at apart
  change 472 ≤ s.regs.rsp.toBitVec.toNat at low
  change s.regs.rdi.toBitVec.toNat + 80 ≤ 2^64 at out
  change s.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 at high
  unfold Body.Apart at apart
  bv_omega

theorem bool_refines (e : Executable) (base : Int64)
    (code : CodeAt e base) (bodyCode : BoolCodec.CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : Owned s base .bool ra data address capacity used) :
    Eventually (step e) (fun t =>
      SszNative.BoolCodec.ResultAt (BoolCodec.observe t.1.dmem s.regs.rdi.toBitVec)
        (Ssz.deserialize .bool data) ∧
      t.1 = BoolCodec.decoded (bodyState s base .bool) (saved s ra) data[0]!.toBitVec ∧
      CommonPost s base ra address capacity used t) (s, base) := by
  have sep := bool_separated s base ra data address capacity used h
  apply entry_runs e base code s .bool ra data address capacity used h
  apply eventually_weaken _ _ _ _ _
    (BoolCodec.body_refines e base bodyCode (bodyState s base .bool) (saved s ra) data
      h.tail.output h.output_bound h.saved_at sep h.length.symm (by
        intro one
        have loaded := h.source_bytes 0 (by omega)
        simpa only [body_memory, body_source, BitVec.add_zero,
          Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          show (default : UInt8) = 0 by decide] using loaded))
  intro t post
  rcases post with ⟨pc, observed, state⟩
  have restored := BoolCodec.decoded_saved (bodyState s base .bool).dmem
    (bodyState s base .bool).regs.rdi.toBitVec (bodyState s base .bool).regs.r14.toBitVec
    (bodyState s base .bool).regs.rsp.toBitVec data[0]!.toBitVec (saved s ra) sep h.saved_at
  have returned : Returned s ra t := by
    refine ⟨pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [state]
      change (bodyState s base .bool).regs.rsp.toBitVec + 368 = s.regs.rsp.toBitVec + 8
      rw [body_sp]
      bv_omega
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · simp only [state, BoolCodec.decoded, BoolCodec.returned, saved, UInt64.toBitVec_ofBitVec]
    · have ret := restored.2.2.2.2.2.2
      rw [body_sp] at ret
      simpa only [state, BoolCodec.decoded, BoolCodec.returned,
        show (360 : BitVec 64) = 360#64 by decide, BitVec.sub_add_cancel, saved] using ret
  have kept : Preserved s address capacity used t := by
    intro p n region i hi
    have frame := BoolCodec.decoded_frame (savedMem s) s.regs.rdi.toBitVec s.regs.rcx.toBitVec
      (BitVec.ofNat 64 (p + i)) data[0]!.toBitVec (by
        intro j hj
        have bound := region.bound
        have apart := region.output
        have out := h.output_bound
        change Body.Apart p n s.regs.rdi.toBitVec.toNat 80 at apart
        change s.regs.rdi.toBitVec.toNat + 80 ≤ 2^64 at out
        unfold Body.Apart at apart
        bv_omega)
    change t.1.dmem.get? _ = _
    rw [state]
    exact frame.trans (region.byte h.stack_low i hi)
  exact ⟨observed, state, returned, kept, preserved_table h kept⟩

end SszX86.Dispatch

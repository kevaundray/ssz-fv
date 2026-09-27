import SszX86.UintTailExec

namespace SszX86.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- ABI return from the original activation. The PC is loaded from original
SP+360; all six callee-saved registers and SP are restored, and only the result
and the six explicitly initialized scratch words can differ in memory. -/
structure Returned (s : MachineData) (t : MachineState) (saved : Saved) : Prop where
  pc : t.2 = Int64.ofBitVec saved.rip
  returnSlot : (Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 360#64) 8).map
    (fun value => Int64.ofBitVec (BitVec.ofInt 64 value)) = some t.2
  sp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 368#64
  rbx : t.1.regs.rbx.toBitVec = saved.rbx
  r12 : t.1.regs.r12.toBitVec = saved.r12
  r13 : t.1.regs.r13.toBitVec = saved.r13
  r14 : t.1.regs.r14.toBitVec = saved.r14
  r15 : t.1.regs.r15.toBitVec = saved.r15
  rbp : t.1.regs.rbp.toBitVec = saved.rbp
  activation : SavedAt t.1.dmem s.regs.rsp.toBitVec saved
  frame : Frame s t.1

/-- A Large pair's entire borrowed byte slice is unchanged, not merely its
mathematical value. Empty and redundant Large slices satisfy the same contract. -/
theorem borrowed_bytes_preserved (s t : MachineData) (pointer payload : BitVec 64)
    (value : Nat) (hf : Frame s t) (hn : NatPair s pointer payload value)
    (hp : pointer ≠ 0#64) :
    ∀ i < 8 * payload.toNat,
      t.dmem.get? (pointer + BitVec.ofNat 64 i) =
        s.dmem.get? (pointer + BitVec.ofNat 64 i) := by
  intro i hi
  rcases hn with ⟨hz, _⟩ | ⟨words, _, _, hspace, hcount, _, _, hsep⟩
  · exact (hp hz).elim
  · rcases hsep with rfl | ⟨hout, hstack⟩
    · have hc : payload.toNat = 0 := hcount
      omega
    · apply hf <;> bv_omega

theorem returned_contract (s t : MachineData) (saved : Saved) (hs : Separated s)
    (hm : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (hsp : t.regs.rsp = s.regs.rsp) (hf : Frame s t) :
    Returned s (returned t saved, Int64.ofBitVec saved.rip) saved := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rcases hm with ⟨_, _, _, _, _, _, hrip⟩
    simp only [hrip, Option.map_some, SszX86.ofBytes_wordBytes]
  · simp only [returned, UInt64.toBitVec_ofBitVec, hsp]
  · exact frame_saved s t saved hs hf hm
  · exact hf

/-- Native success tail through RET, with an arbitrary continuation and exact
final machine state. Neither Small nor Large is privileged by this execution lemma. -/
theorem success_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s)
    (P : MachineState → Prop)
    (hp : P (returned (successReady s) saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 5502) := by
  apply success_stores e base hc s hm P
  apply BoolCodec.epilogue e base (bool_codeAt e base hc) (successReady s) saved
  · exact frame_saved s (successReady s) saved hs (success_frame s hs) ha
  · exact hp

/-- Native scope-error tail, including the shared reason/tag stores and RET. -/
theorem scope_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s)
    (P : MachineState → Prop)
    (hp : P (returned (scopeReady s) saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 2851) := by
  apply scope_stores e base hc s hm P
  apply BoolCodec.epilogue e base (bool_codeAt e base hc) (scopeReady s) saved
  · exact frame_saved s (scopeReady s) saved hs (scope_frame s hs) ha
  · exact hp

/-- Native scratch-error tail. Mapping does not constrain old local values:
2918--2975 initialize every copied word before the actual loads and RET. -/
theorem scratch_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (hwork : ActivationMapped s.dmem s.regs.rsp.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s)
    (P : MachineState → Prop)
    (hp : P (returned (scratchReady s) saved, Int64.ofBitVec saved.rip)) :
    Eventually (step e) P (s, base + 2918) := by
  apply scratch_stores e base hc s hm hwork hs P
  apply BoolCodec.epilogue e base (bool_codeAt e base hc) (scratchReady s) saved
  · exact frame_saved s (scratchReady s) saved hs (scratch_frame s hs) ha
  · exact hp

/-- Success publishes the unrestricted native Nat and returns with the full ABI
and byte-frame contract. `frame_words` preserves any borrowed Large limb slice. -/
theorem success_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (value : Nat)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s)
    (hn : NatPair s s.regs.r9.toBitVec s.regs.r8.toBitVec value) :
    Eventually (step e) (fun t =>
      SszNative.UintCodec.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toBitVec.toNat
        (.ok (.uint value)) ∧
      Returned s t saved ∧ t.1 = returned (successReady s) saved) (s, base + 5502) := by
  apply success_runs e base hc s saved hm ha hs
  exact ⟨success_result s value hs hn,
    returned_contract s (successReady s) saved hs ha rfl (success_frame s hs), rfl⟩

/-- Scope errors retain the exact descriptor Nat (including empty/redundant
Large representations), record the original R14 input length, and return. -/
theorem scope_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (expected : Nat)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s)
    (hn : NatPair s s.regs.rax.toBitVec s.regs.rcx.toBitVec expected) :
    Eventually (step e) (fun t =>
      SszNative.UintCodec.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toBitVec.toNat
        (.error (.scope expected s.regs.r14.toBitVec.toNat)) ∧
      Returned s t saved ∧ t.1 = returned (scopeReady s) saved) (s, base + 2851) := by
  apply scope_runs e base hc s saved hm ha hs
  exact ⟨scope_result s expected hs hn,
    returned_contract s (scopeReady s) saved hs ha rfl (scope_frame s hs), rfl⟩

/-- Resource failure is exactly reason 32768 with all three argument Nats Small
zero; this is not identified with an upstream SSZ semantic error. -/
theorem scratch_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved)
    (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (hwork : ActivationMapped s.dmem s.regs.rsp.toBitVec)
    (ha : SavedAt s.dmem s.regs.rsp.toBitVec saved) (hs : Separated s) :
    Eventually (step e) (fun t =>
      SszNative.UintCodec.scratchExhaustedAt (widthLoad t.1.dmem) s.regs.rdi.toBitVec.toNat ∧
      Returned s t saved ∧ t.1 = returned (scratchReady s) saved) (s, base + 2918) := by
  apply scratch_runs e base hc s saved hm hwork ha hs
  exact ⟨scratch_result s hs,
    returned_contract s (scratchReady s) saved hs ha rfl (scratch_frame s hs), rfl⟩

end SszX86.UintCodec.Tail

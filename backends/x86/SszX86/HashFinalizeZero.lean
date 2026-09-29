import SszX86.HashFinalizePrefix

namespace SszX86.Hash.Finalize
open SszNative.HashStream

structure BufferPost (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (s : MachineData) : Prop where
  memory : MemoryLive root entry state ra s.dmem
  regs : RegsLive entry s
  buffer : BytesAt s.dmem entry.regs.rsi.toBitVec buf.toList
  chaining : ChainingAt s.dmem (entry.regs.rsi.toBitVec + 64) chain

theorem memset_regs (entry s : MachineData) (live : RegsLive entry s)
    (ra : BitVec 64) (t : MachineState) (h : MemsetReturned (callState s ra) ra t) :
    RegsLive entry t.1 := by
  have keep := h.2.2.2.2
  have eqreg (r : Reg64) (ha : r ≠ .rax) (hb : r ≠ .rsp) (hc : r ≠ .rdi)
      (hd : r ≠ .rdx) (he : r ≠ .r8) (hf : r ≠ .r9) :
      t.1.regs.get64 r = s.regs.get64 r := by
    simpa only [callState, Emit.callState, Reg64s.get64] using keep r ha hb hc hd he hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (UInt64.toBitVec_inj.mp (eqreg .rbx (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.output
  · exact (UInt64.toBitVec_inj.mp (eqreg .r14 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.state
  · simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec,
      BitVec.sub_add_cancel, live.stack] using h.2.2.1
  · exact (UInt64.toBitVec_inj.mp (eqreg .rbp (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.rbp
  · exact (UInt64.toBitVec_inj.mp (eqreg .r12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.r12
  · exact (UInt64.toBitVec_inj.mp (eqreg .r13 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.r13
  · exact (UInt64.toBitVec_inj.mp (eqreg .r15 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans live.r15

theorem zero_call_slot (entry s : MachineData) (regs : RegsLive entry s)
    (memory : StackAt s.dmem entry.regs.rsp.toBitVec 192) :
    Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8 := by
  have hm := mapped_subrange s.dmem (entry.regs.rsp.toBitVec - 192) 192 160 8
    memory.2 (by decide)
  have addr : s.regs.rsp.toBitVec - 8 =
      entry.regs.rsp.toBitVec - 192 + BitVec.ofNat 64 160 := by rw [regs.stack]; bv_omega
  simpa only [addr] using hm

/-- Either real memset call executes to its own original return PC, including n=0. -/
theorem zero_buffer_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra) (overflow : Bool)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s)
    (start count : Nat) (bound : start + count ≤ 64)
    (dest : s.regs.rdi.toBitVec = entry.regs.rsi.toBitVec + BitVec.ofNat 64 start)
    (length : s.regs.rdx.toBitVec = BitVec.ofNat 64 count) (zero : s.regs.rsi = 0)
    (P : MachineState → Prop)
    (next : ∀ t, BufferPost root entry state ra
      (overwrite buf start (List.replicate count 0) (by simpa using bound)) chain t →
      Eventually (step e) P (t, root - 256 + if overflow then 75 else 116)) :
    Eventually (step e) P (s, root - 256 + if overflow then 69 else 110) := by
  let ret := (root - 256 + if overflow then 75 else 116).toBitVec
  have slot := zero_call_slot entry s live.regs live.memory.stack
  have apart : Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) count 8 := by
    intro i hi j hj equal
    rw [dest, live.regs.stack] at equal
    have a : entry.regs.rsp.toBitVec - 24 - 8 + BitVec.ofNat 64 j =
        entry.regs.rsp.toBitVec - 192 + BitVec.ofNat 64 (160 + j) := by bv_omega
    have b : entry.regs.rsi.toBitVec + BitVec.ofNat 64 start + BitVec.ofNat 64 i =
        entry.regs.rsi.toBitVec + BitVec.ofNat 64 (start + i) := by bv_omega
    exact pre.stackState (160 + j) (by omega) (start + i) (by omega)
      (a.symm.trans (equal.symm.trans b))
  have mapping : Mapped s.dmem s.regs.rdi.toBitVec count := by
    rw [dest]
    exact mapped_subrange _ _ 112 start count live.memory.stateMapped (by omega)
  have run := zero_helper_runs e (root + 127936) hc.memset s ret count length zero
    (by omega) mapping apart
  have resumed : Eventually (step e) P (callState s ret, root + 127936) := by
    apply eventually_trans (step e) _ P _ run
    intro t post
    have frame : MemoryFrame s.dmem t.1.dmem (WorkWritable entry) := by
      apply frame_mono _ _ _ _ post.frame
      intro a inside
      rcases inside with inside | ⟨i, hi, equal⟩
      · apply state_store_work entry start count (by omega) a
        simpa only [dest] using inside
      · refine Or.inr (Or.inr ⟨160 + i, by omega, ?_⟩)
        rw [equal, live.regs.stack]
        bv_omega
    have memory := memory_update root entry state ra pre s.dmem t.1.dmem live.memory frame post.mapped
    have regs := memset_regs entry s live.regs ret t post.returned
    have before : BytesAt (callState s ret).dmem entry.regs.rsi.toBitVec buf.toList := by
      apply bytesAt_frame s.dmem (callState s ret).dmem _ _ _ live.buffer (storeInt_frame _ _ _ _)
      intro i hi inside
      obtain ⟨j, hj, equal⟩ := inside
      have hi' : i < 64 := by simpa using hi
      apply pre.stackState (160 + j) (by omega) i (by omega)
      rw [equal, live.regs.stack]
      bv_omega
    have buffer : BytesAt t.1.dmem entry.regs.rsi.toBitVec
        (overwrite buf start (List.replicate count 0) (by simpa using bound)).toList := by
      apply bytesAt_overwrite _ _ _ buf start (List.replicate count 0) (by simpa using bound)
      · have h := pre.statePhysical
        unfold Physical at h ⊢
        omega
      · exact before
      · simpa only [dest] using post.output
      · simpa only [dest, List.length_replicate] using post.callFrame
    have chaining : ChainingAt t.1.dmem (entry.regs.rsi.toBitVec + 64) chain := by
      apply bytesAt_frame s.dmem t.1.dmem _ _ _ live.chaining post.frame
      intro i hi inside
      have hi' : i < 32 := by simpa using hi
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · have physical := pre.statePhysical
        unfold Physical at physical
        rw [dest] at equal
        bv_omega
      · apply pre.stackState (160 + j) (by omega) (64 + i) (by omega)
        rw [equal, live.regs.stack]
        bv_omega
    have finish := next t.1 ⟨memory, regs, buffer, chaining⟩
    have pc := post.returned.1
    simpa only [pc, ret, Int64.ofBitVec_toBitVec] using finish
  have target : root - 256 + Int64.ofInt 128192 = root + 127936 := by
    apply Int64.toBitVec_inj.mp
    change root.toBitVec - 256 + 128192 = root.toBitVec + 127936
    bv_omega
  cases overflow
  · apply finalize_call110_cps e (root - 256) hc.finalize s P slot
    simpa only [ret, Bool.false_eq_true, ↓reduceIte, target] using resumed
  · apply finalize_call69_cps e (root - 256) hc.finalize s P slot
    simpa only [ret, ↓reduceIte, target] using resumed

end SszX86.Hash.Finalize

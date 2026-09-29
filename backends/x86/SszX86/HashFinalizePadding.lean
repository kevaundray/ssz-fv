import SszX86.HashFinalizeDigest

namespace SszX86.Hash.Finalize
open SszNative.HashStream

/-- The overflow branch resets only the buffered count, after first compression. -/
theorem reset_buffer_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s) (P : MachineState → Prop)
    (next : ∀ t, BufferPost root entry state ra buf chain t → get t .rdi = 0 →
      Eventually (step e) P (t, root - 256 + 97)) :
    Eventually (step e) P (s, root - 256 + 87) := by
  apply reset_runs e (root - 256) hc.finalize s P
  · change ∃ old, Mem.loadInt s.dmem (s.regs.r14.toBitVec + 96) 8 = some old
    rw [live.regs.state]
    exact UintCodec.Large.mapped_load _ _ 112 96 8 live.memory.stateMapped (by decide)
  intro flags
  let t := resetState s flags
  have mem : t.dmem = Mem.storeInt s.dmem (entry.regs.rsi.toBitVec + 96) 8 0 := by
    change Mem.storeInt s.dmem (s.regs.r14.toBitVec + 96) 8 0 = _
    rw [live.regs.state]
  have memory : MemoryLive root entry state ra t.dmem := by
    rw [mem]
    exact state_store_live root entry state ra pre _ live.memory 96 8 (by decide) 0
  have buffer : BytesAt t.dmem entry.regs.rsi.toBitVec buf.toList := by
    rw [mem]
    simpa only [BitVec.add_zero] using state_store_preserve _ _ pre.statePhysical 96 8 0 buf.toList
      (by decide) (by simp) (Or.inr (by simp)) 0 (by simpa only [BitVec.add_zero] using live.buffer)
  have chaining : ChainingAt t.dmem (entry.regs.rsi.toBitVec + 64) chain := by
    rw [mem]
    exact state_store_preserve _ _ pre.statePhysical 96 8 64 (chainingBytes chain)
      (by decide) (by simp) (Or.inr (by simp)) 0 live.chaining
  exact next t ⟨memory, live.regs, buffer, chaining⟩ rfl

/-- Shared final-block suffix: zero through byte55, wrapped BE length, compression,
BE digest stores, and the real return. -/
theorem final_padding_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s)
    (pos : Nat) (bound : pos ≤ 56) (position : get s .rdi = BitVec.ofNat 64 pos)
    (digest : Ssz.Sha256.digest (compressBuffer chain (finishBuffer buf pos bound state.byteLen)) =
      finalize state) :
    Eventually (step e) (FinalizePost entry state ra) (s, root - 256 + 97) := by
  apply final_zero_setup_runs e (root - 256) hc.finalize s
  intro flags
  let t := zeroSetup s (56 - get s .rdi) flags
  have count : t.regs.rdx.toBitVec = BitVec.ofNat 64 (56 - pos) := by
    change 56 - get s .rdi = _
    rw [position]
    bv_omega
  have dest : t.regs.rdi.toBitVec = entry.regs.rsi.toBitVec + BitVec.ofNat 64 pos := by
    change get s .rdi + get s .r14 = _
    rw [position]
    change BitVec.ofNat 64 pos + s.regs.r14.toBitVec = _
    rw [live.regs.state, BitVec.add_comm]
  have liveT : BufferPost root entry state ra buf chain t :=
    ⟨live.memory, live.regs, live.buffer, live.chaining⟩
  apply zero_buffer_runs e root hc entry state ra pre false t buf chain liveT pos (56 - pos)
    (by omega) dest count rfl
  intro cleared clearPost
  apply length_buffer_runs e root hc entry state ra pre cleared _ chain clearPost
  intro finished finishPost
  apply compress_buffer_runs e root hc compress entry state ra pre false finished _ chain finishPost
  intro compressed compressPost
  exact digest_return_runs e root hc entry state ra pre compressed _ _ compressPost digest

/-- All counts 0..63 reach one or two real compression calls; neither panic PC is reached. -/
theorem padding_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra)
    (s : MachineData) (entered : PrefixPost root entry state ra s) :
    Eventually (step e) (FinalizePost entry state ra) (s, root - 256 + 40) := by
  have countBound := state.buffered.isLt
  have countNat : (get s .rdi).toNat = state.buffered.val + 1 := by
    rw [entered.newCount]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : state.buffered.val + 1 < 2^64)]
  apply padding_branch_runs e (root - 256) hc.finalize s
  by_cases spill : 56 < state.buffered.val + 1
  · have branch : ¬ (get s .rdi).toNat ≤ 56 := by rw [countNat]; omega
    simp only [branch, ↓reduceIte]
    let compared := compare s (get s .rdi) 56
    apply check_overflow_runs e (root - 256) hc.finalize compared
    · change (get s .rdi).toNat ≤ 64
      rw [countNat]
      omega
    let checked := compare compared (get compared .rdi) 64
    apply overflow_zero_setup_runs e (root - 256) hc.finalize checked
    intro flags
    let t := zeroSetup checked (63 - get checked .rax) flags
    have count : t.regs.rdx.toBitVec = BitVec.ofNat 64 (64 - (state.buffered.val + 1)) := by
      change 63 - get s .rax = _
      rw [entered.oldCount]
      bv_omega
    have dest : t.regs.rdi.toBitVec =
        entry.regs.rsi.toBitVec + BitVec.ofNat 64 (state.buffered.val + 1) := by
      change get s .rdi + get s .r14 = _
      rw [entered.newCount]
      change BitVec.ofNat 64 (state.buffered.val + 1) + s.regs.r14.toBitVec = _
      rw [entered.regs.state, BitVec.add_comm]
    have live : BufferPost root entry state ra (delimiterBuffer state) state.chaining t :=
      ⟨entered.memory, entered.regs, entered.buffer, entered.chaining⟩
    apply zero_buffer_runs e root hc entry state ra pre true t (delimiterBuffer state) state.chaining live
      (state.buffered.val + 1) (64 - (state.buffered.val + 1)) (by omega) dest count rfl
    intro first firstPost
    apply compress_buffer_runs e root hc compress entry state ra pre true first _ state.chaining firstPost
    intro compressed compressPost
    apply reset_buffer_runs e root hc entry state ra pre compressed _ _ compressPost
    intro reset resetPost zero
    apply final_padding_runs e root hc compress entry state ra pre reset _ _ resetPost 0 (by decide) zero
    simp only [finalize, finalizeRun, spill, ↓reduceDIte]
    rfl
  · have branch : (get s .rdi).toNat ≤ 56 := by rw [countNat]; omega
    simp only [branch, ↓reduceIte]
    let compared := compare s (get s .rdi) 56
    have live : BufferPost root entry state ra (delimiterBuffer state) state.chaining compared :=
      ⟨entered.memory, entered.regs, entered.buffer, entered.chaining⟩
    apply final_padding_runs e root hc compress entry state ra pre compared _ _ live
      (state.buffered.val + 1) (by omega) entered.newCount
    simp only [finalize, finalizeRun, spill, ↓reduceDIte]
    rfl

end SszX86.Hash.Finalize

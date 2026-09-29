import SszX86.HashFinalizeCompression
import SszX86.HashEndian

namespace SszX86.Hash.Finalize
open SszNative.HashStream

/-- The final eight padding bytes are obtained by the real load/shift/swap/store. -/
theorem length_buffer_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s) (P : MachineState → Prop)
    (next : ∀ t, BufferPost root entry state ra
      (overwrite buf 56 (finalLengthBytes state.byteLen) (by simp)) chain t →
      Eventually (step e) P (t, root - 256 + 131)) :
    Eventually (step e) P (s, root - 256 + 116) := by
  let loaded := put s .rax state.byteLen.toBitVec
  apply load_length_runs e (root - 256) hc.finalize s state.byteLen.toBitVec P
  · simpa only [get, UintCodec.Large.get, Reg64s.get64, live.regs.state]
      using live.memory.byteLen
  apply shift_length_runs e (root - 256) hc.finalize loaded P
  intro flags
  let shifted := putF loaded .rax (state.byteLen.toBitVec <<< (3 : Nat)) flags
  let swapped := put shifted .rax (swap64 (state.byteLen.toBitVec <<< (3 : Nat)))
  let result := lengthState swapped
  apply swap_length_runs e (root - 256) hc.finalize shifted P
  apply store_length_runs e (root - 256) hc.finalize swapped P
  · change ∃ old, Mem.loadInt s.dmem (s.regs.r14.toBitVec + 56) 8 = some old
    rw [live.regs.state]
    exact UintCodec.Large.mapped_load _ _ 112 56 8 live.memory.stateMapped (by decide)
  have mem : result.dmem = Mem.storeInt s.dmem (entry.regs.rsi.toBitVec + 56) 8
      (swap64 (state.byteLen.toBitVec <<< (3 : Nat))).toInt := by
    change Mem.storeInt s.dmem (s.regs.r14.toBitVec + 56) 8 _ = _
    rw [live.regs.state]
  have memory : MemoryLive root entry state ra result.dmem := by
    rw [mem]
    exact state_store_live root entry state ra pre _ live.memory 56 8 (by decide) _
  have regs : RegsLive entry result := live.regs
  have buffer : BytesAt result.dmem entry.regs.rsi.toBitVec
      (overwrite buf 56 (finalLengthBytes state.byteLen) (by simp)).toList := by
    rw [mem]
    apply bytesAt_overwrite _ _ _ buf 56 (finalLengthBytes state.byteLen) (by simp)
    · have h := pre.statePhysical
      unfold Physical at h ⊢
      omega
    · exact live.buffer
    · simpa only [length_store_bytes] using storeInt_bytes s.dmem
        (entry.regs.rsi.toBitVec + 56) 8 (swap64 (state.byteLen.toBitVec <<< (3 : Nat))).toInt (by decide)
    · simpa only [finalLengthBytes_length] using storeInt_frame s.dmem
        (entry.regs.rsi.toBitVec + 56) 8 (swap64 (state.byteLen.toBitVec <<< (3 : Nat))).toInt
  have chaining : ChainingAt result.dmem (entry.regs.rsi.toBitVec + 64) chain := by
    rw [mem]
    exact state_store_preserve _ _ pre.statePhysical 56 8 64 (chainingBytes chain)
      (by decide) (by simp) (Or.inl (by decide)) _ live.chaining
  exact next result ⟨memory, regs, buffer, chaining⟩

end SszX86.Hash.Finalize

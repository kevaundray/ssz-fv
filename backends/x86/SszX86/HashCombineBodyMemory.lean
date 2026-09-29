import SszX86.HashCombineBody
import SszX86.HashStateUpdate

namespace SszX86.Hash.Combine
open SszNative.HashStream

theorem compression_stack (s : MachineData) (chaining : Vector UInt32 8)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState)
    (post : CompressionCallPost s chaining block ra t) :
    t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec := by
  simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec,
    BitVec.sub_add_cancel] using post.returned.2.1

theorem compression_saved (s : MachineData) (chaining : Vector UInt32 8)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState)
    (post : CompressionCallPost s chaining block ra t) : Saved s t.1 :=
  post.returned.2.2

/-- The actual helper replaces only chaining; exact buffer and both counters
survive, so direct-loop induction does not erase the stale buffer tail. -/
theorem compressed_state (s : MachineData) (state : Model)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (physical : Physical (s.regs.rsp.toBitVec + 8) 112)
    (chainReg : s.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 72)
    (stackState : Disjoint (s.regs.rsp.toBitVec - 168)
      (s.regs.rsp.toBitVec + 8) 168 112)
    (post : CompressionCallPost s state.chaining block ra t) :
    StateAt t.1.dmem (s.regs.rsp.toBitVec + 8)
      {state with chaining := compressBuffer state.chaining block} := by
  have chainAddress : s.regs.rsp.toBitVec + 72 = (s.regs.rsp.toBitVec + 8) + 64 := by
    bv_omega
  apply stateAt_replace_chaining s.dmem t.1.dmem (s.regs.rsp.toBitVec + 8) state _
    (fun a => InSpan a (s.regs.rsp.toBitVec - 168) 168) physical stored
  · simpa only [chainReg, chainAddress] using post.state
  · simpa only [chainReg, chainAddress] using post.frame
  · intro i hi inside
    rcases inside with ⟨j, hj, equal⟩
    exact stackState j hj i hi equal.symm

/-- A full-block call transports the original physical source borrow unchanged. -/
theorem compressed_memory (root : Int64) (s : MachineData)
    (source : BitVec 64) (input : ByteArray) (chaining : Vector UInt32 8)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (chainReg : s.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 72)
    (post : CompressionCallPost s chaining block ra t) :
    DrainMemory root t.1.dmem t.1.regs.rsp.toBitVec source input := by
  rw [compression_stack s chaining block ra t post]
  exact DrainMemory.after root s.dmem t.1.dmem s.regs.rsp.toBitVec source input memory
    (compression_frame_drain s chaining block ra t chainReg post) post.mapped

end SszX86.Hash.Combine

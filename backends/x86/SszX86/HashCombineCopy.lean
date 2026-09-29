import SszX86.HashCombineDrainMemory

namespace SszX86.Hash.Combine

inductive CopySite where
  | leftResidual | bufferedRight | rightResidual

def CopySite.pc : CopySite → Nat
  | .leftResidual => 228 | .bufferedRight => 278 | .rightResidual => 388

def CopySite.next : CopySite → Nat
  | .leftResidual => 234 | .bufferedRight => 284 | .rightResidual => 394

/-- All three copies use the proved real helper, including its empty-input path. -/
theorem copy_call_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (site : CopySite) (s : MachineData) (bytes : List UInt8)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 bytes.length)
    (bound : bytes.length < 2 ^ 64)
    (source : BytesAt s.dmem s.regs.rsi.toBitVec bytes)
    (output : Mapped s.dmem s.regs.rdi.toBitVec bytes.length)
    (slot : Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (apart : Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes.length bytes.length)
    (sourceStack : Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8)
    (outputStack : Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    Eventually (step e) (Hash.CopyPost s (root + Int64.ofNat site.next).toBitVec bytes)
      (s, root + Int64.ofNat site.pc) := by
  cases site with
  | leftResidual =>
    apply combine_call228_cps e root hc.combine s _ slot
    exact Hash.copy_helper_runs e (root + 127872) hc.memcpy s _ bytes
      count bound source output apart sourceStack outputStack
  | bufferedRight =>
    apply combine_call278_cps e root hc.combine s _ slot
    exact Hash.copy_helper_runs e (root + 127872) hc.memcpy s _ bytes
      count bound source output apart sourceStack outputStack
  | rightResidual =>
    apply combine_call388_cps e root hc.combine s _ slot
    exact Hash.copy_helper_runs e (root + 127872) hc.memcpy s _ bytes
      count bound source output apart sourceStack outputStack

/-- Construct copy ownership from the original allocation, not a copied or
concatenated input. Source lengths and destination counts need not be equal. -/
theorem copy_slice_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (site : CopySite) (s : MachineData) (source : BitVec 64) (input : ByteArray)
    (start dst count : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (sourceBound : start + count ≤ input.size) (bufferBound : dst + count ≤ 64)
    (sourceReg : s.regs.rsi.toBitVec = source + BitVec.ofNat 64 start)
    (destReg : s.regs.rdi.toBitVec = (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 dst)
    (countReg : s.regs.rdx.toBitVec = BitVec.ofNat 64 count) :
    Eventually (step e)
      (Hash.CopyPost s (root + Int64.ofNat site.next).toBitVec
        ((input.data.toList.drop start).take count))
      (s, root + Int64.ofNat site.pc) := by
  have length : ((input.data.toList.drop start).take count).length = count := by
    simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
    omega
  have slotAddress : s.regs.rsp.toBitVec - 168 + BitVec.ofNat 64 160 =
      s.regs.rsp.toBitVec - 8 := by bv_omega
  apply copy_call_runs e root hc site s
  · simpa only [length] using countReg
  · rw [length]
    omega
  · rw [sourceReg]
    exact bytesAt_slice _ _ _ start count
      (by simpa only [Array.length_toList, ByteArray.size_data] using sourceBound) memory.bytes
  · rw [destReg, length]
    exact mapped_subrange _ _ 112 dst count memory.state (by omega)
  · have slot := mapped_subrange _ _ 168 160 8 memory.stack.2 (by decide)
    simpa only [slotAddress] using slot
  · rw [sourceReg, destReg, length]
    exact disjoint_subrange _ _ input.size 112 start count dst count
      memory.sourceState sourceBound (by omega)
  · rw [sourceReg, length, ← slotAddress]
    exact disjoint_subrange _ _ input.size 168 start count 160 8
      memory.sourceStack sourceBound (by decide)
  · rw [destReg, length, ← slotAddress]
    exact disjoint_subrange _ _ 112 168 dst count 160 8
      (disjoint_symm _ _ _ _ memory.stackState) (by omega) (by decide)

/-- The real helper's register frame includes all six ABI callee-saved words. -/
theorem copy_saved (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (t : MachineState) (post : Hash.CopyPost s ra bytes t) : Saved s t.1 := by
  have regs := post.returned.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply UInt64.toBitVec_inj.1
  · exact regs .rbx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact regs .rbp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact regs .r12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact regs .r13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact regs .r14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact regs .r15 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

theorem copy_stack (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (t : MachineState) (post : Hash.CopyPost s ra bytes t) :
    t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec := by
  simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec,
    BitVec.sub_add_cancel] using post.returned.2.2.1

end SszX86.Hash.Combine

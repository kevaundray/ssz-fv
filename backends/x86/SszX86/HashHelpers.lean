import SszX86.HashCalls
import SszX86.HashMemoryUpdate

namespace SszX86.Hash

/-- Scratch ownership survives real helpers, including bytes not currently live. -/
def MappedPreserved (before after : DataMem) : Prop :=
  ∀ p n, Mapped before p n → Mapped after p n

structure CopyPost (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (t : MachineState) : Prop extends Emit.CopyPost s ra bytes t where
  «mapped» : MappedPreserved s.dmem t.1.dmem
  callFrame : MemoryFrame (callState s ra).dmem t.1.dmem
    (fun a => InSpan a s.regs.rdi.toBitVec bytes.length)

structure ZeroPost (s : MachineData) (ra : BitVec 64) (n : Nat)
    (t : MachineState) : Prop extends NatMul.MemsetCall.Post s ra n t where
  «mapped» : MappedPreserved s.dmem t.1.dmem
  callFrame : MemoryFrame (callState s ra).dmem t.1.dmem
    (fun a => InSpan a s.regs.rdi.toBitVec n)

/-- Reusing the accepted real memcpy proof, with its exact complement retained. -/
theorem copy_helper_runs (e : Executable) (helper : Int64)
    (code : Emit.MemcpyCodeAt e helper) (s : MachineData) (ra : BitVec 64)
    (bytes : List UInt8) (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 bytes.length)
    (bound : bytes.length < 2 ^ 64) (source : BytesAt s.dmem s.regs.rsi.toBitVec bytes)
    (mapping : Mapped s.dmem s.regs.rdi.toBitVec bytes.length)
    (apart : Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes.length bytes.length)
    (sourceStack : Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8)
    (outputStack : Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    Eventually (step e) (CopyPost s ra bytes) (callState s ra, helper) := by
  have source' := Emit.call_source s ra bytes source sourceStack
  have mapped' : Mapped (callState s ra).dmem s.regs.rdi.toBitVec bytes.length :=
    UintCodec.Large.mapped_store _ _ _ _ _ _ mapping
  obtain ⟨old, frame, length, owned⟩ := Emit.copy_memory_of_mapped
    (callState s ra).dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes bound source' mapped' apart
  have run := memcpy_correct helper (callState s ra) bytes old frame ra length count bound owned
    (Emit.call_return_slot s ra) (by
      intro i hi j hj
      exact Ne.symm (outputStack j hj i hi))
  apply eventually_weaken (step e) _ _ _ _ (Emit.memcpy_eventually e helper code _ _ run)
  intro t post
  have output : BytesAt t.1.dmem s.regs.rdi.toBitVec bytes :=
    Emit.listBytesAt_of_sep t.1.dmem s.regs.rdi.toBitVec bytes _ (by omega) post.2.1
  have helperFrame : MemoryFrame (callState s ra).dmem t.1.dmem
      (fun a => InSpan a s.regs.rdi.toBitVec bytes.length) := by
    intro a outside
    apply post.2.2 a
    intro inside
    exact outside ((mem_At_iff _ _ _).1 inside)
  refine ⟨⟨post.1, output, ?_⟩, ?_, helperFrame⟩
  · intro a outside
    rw [helperFrame a (fun h => outside (Or.inl h))]
    exact storeInt_frame s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt a
      (fun h => outside (Or.inr h))
  · intro p n hm
    apply mapped_overwrite (callState s ra).dmem t.1.dmem _ bytes output helperFrame p n
    exact UintCodec.Large.mapped_store _ _ _ _ _ _ hm

/-- Reusing the accepted real memset proof, never a padding-result premise. -/
theorem zero_helper_runs (e : Executable) (helper : Int64)
    (code : NatMul.MemsetCall.MemsetCodeAt e helper)
    (s : MachineData) (ra : BitVec 64) (n : Nat)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 n)
    (zero : s.regs.rsi = 0) (bound : n < 2 ^ 64)
    (mapping : Mapped s.dmem s.regs.rdi.toBitVec n)
    (apart : Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) n 8) :
    Eventually (step e) (ZeroPost s ra n) (callState s ra, helper) := by
  have mapped' : Mapped (callState s ra).dmem s.regs.rdi.toBitVec n :=
    UintCodec.Large.mapped_store _ _ _ _ _ _ mapping
  obtain ⟨old, frame, length, owned⟩ := NatMul.MemsetCall.fill_memory_of_mapped
    (callState s ra).dmem s.regs.rdi.toBitVec n bound mapped'
  have run := memset_correct helper (callState s ra) n old frame ra length count bound owned
    (Emit.call_return_slot s ra) (by
      intro i hi j hj
      exact Ne.symm (apart j hj i hi))
  have byte : memsetByte (callState s ra) = 0 := by
    simp [memsetByte, callState, Emit.callState, zero]
  rw [byte] at run
  apply eventually_weaken (step e) _ _ _ _
    (NatMul.MemsetCall.memset_eventually e helper code _ _ run)
  intro t post
  have output : BytesAt t.1.dmem s.regs.rdi.toBitVec (List.replicate n 0) :=
    Emit.listBytesAt_of_sep t.1.dmem s.regs.rdi.toBitVec _ _ (by simpa using Nat.le_of_lt bound) post.2.1
  have helperFrame : MemoryFrame (callState s ra).dmem t.1.dmem
      (fun a => InSpan a s.regs.rdi.toBitVec n) := by
    intro a outside
    apply post.2.2 a
    intro inside
    have h := (mem_At_iff _ _ _).1 inside
    obtain ⟨i, hi, address⟩ := h
    apply outside
    refine ⟨i, ?_, ?_⟩
    · simpa only [List.length_replicate] using hi
    · change a = s.regs.rdi.toBitVec + BitVec.ofNat 64 i at address
      exact address
  refine ⟨⟨post.1, output, ?_⟩, ?_, helperFrame⟩
  · intro a outside
    rw [helperFrame a (fun h => outside (Or.inl h))]
    exact storeInt_frame s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt a
      (fun h => outside (Or.inr h))
  · intro p n' hm
    apply mapped_overwrite (callState s ra).dmem t.1.dmem _ (List.replicate n 0) output
      (by simpa only [List.length_replicate] using helperFrame) p n'
    exact UintCodec.Large.mapped_store _ _ _ _ _ _ hm

end SszX86.Hash

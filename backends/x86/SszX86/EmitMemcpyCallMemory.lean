import SszX86.EmitMemcpyMemory

namespace SszX86.Emit
open UintCodec BoolCodec

def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

theorem call_source (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (source : ListBytesAt s.dmem s.regs.rsi.toBitVec bytes)
    (apart : Large.Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    ListBytesAt (callState s ra).dmem s.regs.rsi.toBitVec bytes := by
  intro i hi
  simp only [callState, Mem.storeInt]
  rw [memmove_store_lookup_outside]
  · exact source i hi
  · intro j hj
    exact apart i hi j (by simpa only [Int.toBytes_length] using hj)

theorem call_return_slot (s : MachineData) (ra : BitVec 64) :
    Mem.loadInt (callState s ra).dmem (callState s ra).regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  simp only [callState, UInt64.toBitVec_ofBitVec]
  rw [load_store_same _ _ 8 _ (by decide)]
  simp only [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]

structure CopyPost (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (t : MachineState) : Prop where
  returned : MemcpyReturned (callState s ra) ra t
  output : ListBytesAt t.1.dmem s.regs.rdi.toBitVec bytes
  frame : MemoryFrame s.dmem t.1.dmem (fun a =>
    InSpan a s.regs.rdi.toBitVec bytes.length ∨ InSpan a (s.regs.rsp.toBitVec - 8) 8)

/-- All helper ownership is constructed from the pre-CALL source, mapped
arbitrary destination, and separation from the one writable return slot. -/
theorem copy_helper_runs (e : Executable) (helper : Int64) (hcode : MemcpyCodeAt e helper)
    (s : MachineData) (ra : BitVec 64) (bytes : List UInt8)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 bytes.length)
    (bound : bytes.length < 2 ^ 64)
    (source : ListBytesAt s.dmem s.regs.rsi.toBitVec bytes)
    (hmap : Large.Mapped s.dmem s.regs.rdi.toBitVec bytes.length)
    (apart : Large.Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes.length bytes.length)
    (sourceStack : Large.Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8)
    (outputStack : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    Eventually (step e) (CopyPost s ra bytes) (callState s ra, helper) := by
  have source' := call_source s ra bytes source sourceStack
  have hmap' : Large.Mapped (callState s ra).dmem s.regs.rdi.toBitVec bytes.length :=
    Large.mapped_store _ _ _ _ _ _ hmap
  obtain ⟨old, frame, length, owned⟩ := copy_memory_of_mapped
    (callState s ra).dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes bound source' hmap' apart
  have run := memcpy_correct helper (callState s ra) bytes old frame ra length count bound owned
    (call_return_slot s ra) (by
      intro i hi j hj
      exact Ne.symm (outputStack j hj i hi))
  apply eventually_weaken (step e) _ _ _ _ (memcpy_eventually e helper hcode _ _ run)
  intro t post
  refine ⟨post.1, listBytesAt_of_sep t.1.dmem s.regs.rdi.toBitVec bytes _
    (by omega) post.2.1, ?_⟩
  intro a outside
  have notOutput : a ∉ bytes.At s.regs.rdi.toBitVec := by
    intro inside
    exact outside (Or.inl ((mem_At_iff _ _ _).1 inside))
  rw [post.2.2 a notOutput]
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside (Or.inr ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩)

end SszX86.Emit

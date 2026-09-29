import SszX86.HashCombineReturn
import SszX86.HashCombineDrainMemory
import SszX86.DispatchMemory
import SszX86.EmitReturnMemory

namespace SszX86.Hash.Combine

structure Live (root : Int64) (entry : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (m : DataMem) : Prop where
  leftBytes : BytesAt m entry.regs.rsi.toBitVec left.data.toList
  rightBytes : BytesAt m entry.regs.rcx.toBitVec right.data.toList
  tables : TablesAt m root
  output : Mapped m entry.regs.rdi.toBitVec 32
  stack : StackAt m entry.regs.rsp.toBitVec 368
  saves : SavedAt m (entry.regs.rsp.toBitVec - 168) entry
  returnSlot : Mem.loadInt m entry.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  frame : MemoryFrame entry.dmem m (CombineWritable entry)

theorem drain_subset (entry : MachineData) (a : BitVec 64)
    (inside : DrainWritable (entry.regs.rsp.toBitVec - 168) a) :
    InSpan a (entry.regs.rsp.toBitVec - 368) 368 := by
  rcases inside with ⟨i, hi, equal⟩ | ⟨i, hi, equal⟩
  · refine ⟨208 + i, by omega, ?_⟩
    rw [equal]
    bv_omega
  · refine ⟨32 + i, by omega, ?_⟩
    rw [equal]
    bv_omega

theorem savedAt_frame (m m' : DataMem) (sp : BitVec 64) (entry : MachineData)
    (saved : SavedAt m sp entry) (frame : MemoryFrame m m' (DrainWritable sp)) :
    SavedAt m' sp entry := by
  have readWord (offset : Nat) (low : 120 ≤ offset) (high : offset ≤ 160) :
      Mem.loadInt m' (sp + BitVec.ofNat 64 offset) 8 =
        Mem.loadInt m (sp + BitVec.ofNat 64 offset) 8 := by
    apply Emit.frame_load m m' (DrainWritable sp) frame
    intro i hi inside
    rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ <;> bv_omega
  exact ⟨(readWord 120 (by decide) (by decide)).trans saved.rbx,
    (readWord 128 (by decide) (by decide)).trans saved.r12,
    (readWord 136 (by decide) (by decide)).trans saved.r13,
    (readWord 144 (by decide) (by decide)).trans saved.r14,
    (readWord 152 (by decide) (by decide)).trans saved.r15,
    (readWord 160 (by decide) (by decide)).trans saved.rbp⟩

/-- Every loop and local state operation updates live borrows independently;
left and right may name overlapping or identical physical intervals. -/
theorem Live.after (root : Int64) (entry : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root entry left right ra)
    (m m' : DataMem) (live : Live root entry left right ra m)
    (frame : MemoryFrame m m' (DrainWritable (entry.regs.rsp.toBitVec - 168)))
    (mapping : MappedPreserved m m') : Live root entry left right ra m' := by
  have safe (p : BitVec 64) (n : Nat)
      (apart : Disjoint p (entry.regs.rsp.toBitVec - 368) n 368) :
      ∀ i < n, ¬ DrainWritable (entry.regs.rsp.toBitVec - 168) (p + BitVec.ofNat 64 i) := by
    intro i hi inside
    rcases drain_subset entry _ inside with ⟨j, hj, equal⟩
    exact apart i hi j hj equal
  refine ⟨?_, ?_, ?_, mapping _ _ live.output,
    ⟨live.stack.1, mapping _ _ live.stack.2⟩,
    savedAt_frame m m' _ entry live.saves frame, ?_, ?_⟩
  · exact bytesAt_frame m m' _ _ _ live.leftBytes frame
      (by simpa only [Array.length_toList, ByteArray.size_data] using safe _ _ pre.leftStack)
  · exact bytesAt_frame m m' _ _ _ live.rightBytes frame
      (by simpa only [Array.length_toList, ByteArray.size_data] using safe _ _ pre.rightStack)
  · constructor
    · exact bytesAt_frame m m' _ _ _ live.tables.1 frame
        (by simpa only [initialBytes] using safe _ _ pre.tablesStack.1)
    · exact bytesAt_frame m m' _ _ _ live.tables.2 frame
        (by simpa only [roundsBytes] using safe _ _ pre.tablesStack.2)
  · rw [Emit.frame_load m m' _ frame _ 8 (by
      intro i hi inside
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ <;> bv_omega)]
    exact live.returnSlot
  · intro a outside
    exact (frame a (fun h => outside (Or.inr (drain_subset entry a h)))).trans
      (live.frame a outside)

/-- Saved words are consequences of the six actual PUSH stores. -/
theorem saved_live (root : Int64) (entry : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root entry left right ra) :
    Live root entry left right ra (Dispatch.savedMem entry) := by
  have frame : MemoryFrame entry.dmem (Dispatch.savedMem entry)
      (fun a => InSpan a (entry.regs.rsp.toBitVec - 48) 48) := by
    intro a outside
    apply Dispatch.saved_lookup entry a
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  have safe (p : BitVec 64) (n : Nat)
      (apart : Disjoint p (entry.regs.rsp.toBitVec - 368) n 368) :
      ∀ i < n, ¬ InSpan (p + BitVec.ofNat 64 i) (entry.regs.rsp.toBitVec - 48) 48 := by
    intro i hi inside
    rcases inside with ⟨j, hj, equal⟩
    have h := apart i hi (320 + j) (by omega)
    apply h
    rw [equal]
    bv_omega
  have saved := Dispatch.saved_at entry ra pre.returnSlot.2
  refine ⟨?_, ?_, ?_, Dispatch.saved_mapped _ _ _ pre.output,
    ⟨pre.stack.1, Dispatch.saved_mapped _ _ _ pre.stack.2⟩, ?_, ?_, ?_⟩
  · exact bytesAt_frame _ _ _ _ _ pre.left frame
      (by simpa only [Array.length_toList, ByteArray.size_data] using safe _ _ pre.leftStack)
  · exact bytesAt_frame _ _ _ _ _ pre.right frame
      (by simpa only [Array.length_toList, ByteArray.size_data] using safe _ _ pre.rightStack)
  · constructor
    · exact bytesAt_frame _ _ _ _ _ pre.tables.1 frame
        (by simpa only [initialBytes] using safe _ _ pre.tablesStack.1)
    · exact bytesAt_frame _ _ _ _ _ pre.tables.2 frame
        (by simpa only [roundsBytes] using safe _ _ pre.tablesStack.2)
  · have address (off : BitVec 64) : entry.regs.rsp.toBitVec - 168 + off =
        entry.regs.rsp.toBitVec - 360 + (off + 192) := by bv_omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.1
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.2.1
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.2.2.1
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.2.2.2.1
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.2.2.2.2.1
    · simpa only [address, BitVec.reduceAdd, Dispatch.saved] using saved.2.2.2.2.2.1
  · rw [Dispatch.saved_load entry _ 8 (by intro i hi j hj; bv_omega)]
    exact pre.returnSlot.2
  · apply frame_mono _ _ _ _ frame
    intro a inside
    right
    rcases inside with ⟨i, hi, equal⟩
    refine ⟨320 + i, by omega, ?_⟩
    rw [equal]
    bv_omega

/-- Either read-only source receives the same local-state ownership. Its borrow
is checked only against writable stack, never against the other source. -/
theorem live_drainMemory (root : Int64) (entry : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root entry left right ra) (m : DataMem)
    (live : Live root entry left right ra m) (source : BitVec 64) (input : ByteArray)
    (bytes : BytesAt m source input.data.toList) (physical : Physical source input.size)
    (apart : Disjoint source (entry.regs.rsp.toBitVec - 368) input.size 368) :
    DrainMemory root m (entry.regs.rsp.toBitVec - 168) source input := by
  have stateAddress : (entry.regs.rsp.toBitVec - 168) + 8 =
      (entry.regs.rsp.toBitVec - 368) + BitVec.ofNat 64 208 := by bv_omega
  have childAddress : (entry.regs.rsp.toBitVec - 168) - 168 =
      (entry.regs.rsp.toBitVec - 368) + BitVec.ofNat 64 32 := by bv_omega
  refine ⟨bytes, physical, ?_, ?_, ?_, live.tables, pre.tablePhysical,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold Physical
    have low := pre.stack.1
    have high := entry.regs.rsp.toBitVec.isLt
    bv_omega
  · exact stack_subrange m entry.regs.rsp.toBitVec 368 168 168 live.stack (by decide)
  · rw [stateAddress]
    exact mapped_subrange _ _ 368 208 112 live.stack.2 (by decide)
  · rw [stateAddress]
    have h := disjoint_subrange _ _ input.size 368 0 input.size 208 112 apart
      (by omega) (by decide)
    simpa only [BitVec.add_zero] using h
  · rw [childAddress]
    have h := disjoint_subrange _ _ input.size 368 0 input.size 32 168 apart
      (by omega) (by decide)
    simpa only [BitVec.add_zero] using h
  · intro i hi j hj equal
    bv_omega
  · rw [stateAddress]
    constructor
    · have h := disjoint_subrange _ _ 32 368 0 32 208 112 pre.tablesStack.1
        (by decide) (by decide)
      simpa only [BitVec.add_zero] using h
    · have h := disjoint_subrange _ _ 256 368 0 256 208 112 pre.tablesStack.2
        (by decide) (by decide)
      simpa only [BitVec.add_zero] using h
  · rw [childAddress]
    constructor
    · have h := disjoint_subrange _ _ 32 368 0 32 32 168 pre.tablesStack.1
        (by decide) (by decide)
      simpa only [BitVec.add_zero] using h
    · have h := disjoint_subrange _ _ 256 368 0 256 32 168 pre.tablesStack.2
        (by decide) (by decide)
      simpa only [BitVec.add_zero] using h

end SszX86.Hash.Combine

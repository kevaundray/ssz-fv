import SszX86.HashHelpers

namespace SszX86.Hash

/-- Pre-CALL ownership includes the eight bytes written by CALL itself. -/
structure CompressionCallPre (root : Int64) (s : MachineData)
    (chaining : Vector UInt32 8) (block : Vector UInt8 64) : Prop where
  state : ChainingAt s.dmem s.regs.rdi.toBitVec chaining
  block : BytesAt s.dmem s.regs.rsi.toBitVec block.toList
  tables : TablesAt s.dmem root
  statePhysical : Physical s.regs.rdi.toBitVec 32
  blockPhysical : Physical s.regs.rsi.toBitVec 64
  tablePhysical : TablesPhysical root
  stack : StackAt s.dmem s.regs.rsp.toBitVec 168
  stateBlock : Disjoint s.regs.rdi.toBitVec s.regs.rsi.toBitVec 32 64
  stackState : Disjoint (s.regs.rsp.toBitVec - 168) s.regs.rdi.toBitVec 168 32
  stackBlock : Disjoint (s.regs.rsp.toBitVec - 168) s.regs.rsi.toBitVec 168 64
  tablesState : TablesDisjoint root s.regs.rdi.toBitVec 32
  tablesStack : TablesDisjoint root (s.regs.rsp.toBitVec - 168) 168

structure CompressionCallPost (s : MachineData) (chaining : Vector UInt32 8)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState) : Prop where
  returned : Returned (callState s ra) ra t
  state : ChainingAt t.1.dmem s.regs.rdi.toBitVec
    (SszNative.HashStream.compressBuffer chaining block)
  frame : MemoryFrame s.dmem t.1.dmem (fun a =>
    InSpan a s.regs.rdi.toBitVec 32 ∨ InSpan a (s.regs.rsp.toBitVec - 168) 168)
  «mapped» : MappedPreserved s.dmem t.1.dmem

theorem initialBytes_length : initialBytes.length = 32 := by rfl

private def roundTail0 : List UInt8 := roundsBytes

private theorem roundTail0_head_length : (roundTail0.take 32).length = 32 := by decide

private def roundTail1 : List UInt8 := roundTail0.drop 32

private theorem roundTail1_head_length : (roundTail1.take 32).length = 32 := by decide

private def roundTail2 : List UInt8 := roundTail1.drop 32

private theorem roundTail2_head_length : (roundTail2.take 32).length = 32 := by decide

private def roundTail3 : List UInt8 := roundTail2.drop 32

private theorem roundTail3_head_length : (roundTail3.take 32).length = 32 := by decide

private def roundTail4 : List UInt8 := roundTail3.drop 32

private theorem roundTail4_head_length : (roundTail4.take 32).length = 32 := by decide

private def roundTail5 : List UInt8 := roundTail4.drop 32

private theorem roundTail5_head_length : (roundTail5.take 32).length = 32 := by decide

private def roundTail6 : List UInt8 := roundTail5.drop 32

private theorem roundTail6_head_length : (roundTail6.take 32).length = 32 := by decide

private def roundTail7 : List UInt8 := roundTail6.drop 32

private theorem roundTail7_head_length : (roundTail7.take 32).length = 32 := by decide

private theorem roundTail7_end : roundTail7.drop 32 = [] := by decide

private theorem roundTail7_length : roundTail7.length = 32 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail7)
  rw [List.length_append] at split
  rw [roundTail7_head_length, roundTail7_end, List.length_nil, Nat.add_zero] at split
  exact split.symm

private theorem roundTail6_length : roundTail6.length = 64 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail6)
  rw [List.length_append] at split
  change (roundTail6.take 32).length + roundTail7.length = roundTail6.length at split
  rw [roundTail6_head_length, roundTail7_length] at split
  exact split.symm

private theorem roundTail5_length : roundTail5.length = 96 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail5)
  rw [List.length_append] at split
  change (roundTail5.take 32).length + roundTail6.length = roundTail5.length at split
  rw [roundTail5_head_length, roundTail6_length] at split
  exact split.symm

private theorem roundTail4_length : roundTail4.length = 128 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail4)
  rw [List.length_append] at split
  change (roundTail4.take 32).length + roundTail5.length = roundTail4.length at split
  rw [roundTail4_head_length, roundTail5_length] at split
  exact split.symm

private theorem roundTail3_length : roundTail3.length = 160 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail3)
  rw [List.length_append] at split
  rw [← roundTail4] at split
  rw [roundTail3_head_length, roundTail4_length] at split
  exact split.symm

private theorem roundTail2_length : roundTail2.length = 192 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail2)
  rw [List.length_append] at split
  rw [← roundTail3] at split
  rw [roundTail2_head_length, roundTail3_length] at split
  exact split.symm

private theorem roundTail1_length : roundTail1.length = 224 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail1)
  rw [List.length_append] at split
  rw [← roundTail2] at split
  rw [roundTail1_head_length, roundTail2_length] at split
  exact split.symm

private theorem roundTail0_length : roundTail0.length = 256 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail0)
  rw [List.length_append] at split
  rw [← roundTail1] at split
  rw [roundTail0_head_length, roundTail1_length] at split
  exact split.symm

theorem roundsBytes_length : roundsBytes.length = 256 := roundTail0_length

private theorem call_preserves_bytes (s : MachineData) (ra p : BitVec 64)
    (bytes : List UInt8) (h : BytesAt s.dmem p bytes)
    (apart : Disjoint p (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    BytesAt (callState s ra).dmem p bytes := by
  apply bytesAt_frame s.dmem (callState s ra).dmem p bytes
    (fun a => InSpan a (s.regs.rsp.toBitVec - 8) 8) h
    (storeInt_frame _ _ _ _)
  intro i hi inside
  obtain ⟨j, hj, equal⟩ := inside
  exact apart i hi j hj equal

/-- Convert only current ownership into the compression helper's entry precondition. -/
theorem compression_call_pre (e : Executable) (root : Int64)
    (code : Compress.CodeAt e (root - 912)) (s : MachineData) (ra : BitVec 64)
    (chaining : Vector UInt32 8) (block : Vector UInt8 64)
    (pre : CompressionCallPre root s chaining block) :
    CompressionPre e root (callState s ra) chaining block ra := by
  have address : (s.regs.rsp.toBitVec - 8) - 160 = s.regs.rsp.toBitVec - 168 := by bv_omega
  have slot (p : BitVec 64) (n : Nat)
      (h : Disjoint (s.regs.rsp.toBitVec - 168) p 168 n) :
      Disjoint p (s.regs.rsp.toBitVec - 8) n 8 := by
    intro i hi j hj equal
    have h' := h (160 + j) (by omega) i hi
    apply h'
    have shift : s.regs.rsp.toBitVec - 168 + BitVec.ofNat 64 (160 + j) =
        s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j := by bv_omega
    exact shift.trans equal.symm
  have stack := stack_subrange s.dmem s.regs.rsp.toBitVec 168 8 160 pre.stack (by decide)
  refine ⟨code, ?_, ?_, ?_, pre.statePhysical, pre.blockPhysical, pre.tablePhysical,
    ?_, ?_, pre.stateBlock, ?_, ?_, pre.tablesState, ?_⟩
  · change ChainingAt (callState s ra).dmem s.regs.rdi.toBitVec chaining
    exact call_preserves_bytes s ra _ _ pre.state
      (by simpa only [chainingBytes_length] using slot _ _ pre.stackState)
  · change BytesAt (callState s ra).dmem s.regs.rsi.toBitVec block.toList
    exact call_preserves_bytes s ra _ _ pre.block
      (by simpa only [Vector.length_toList] using slot _ _ pre.stackBlock)
  · constructor
    · apply call_preserves_bytes s ra _ _ pre.tables.1
      have h := slot _ _ (disjoint_symm _ _ _ _ pre.tablesStack.1)
      simpa only [initialBytes_length] using h
    · apply call_preserves_bytes s ra _ _ pre.tables.2
      have h := slot _ _ (disjoint_symm _ _ _ _ pre.tablesStack.2)
      simpa only [roundsBytes_length] using h
  · refine ⟨stack.1, ?_⟩
    exact UintCodec.Large.mapped_store _ _ _ _ _ _ stack.2
  · refine ⟨?_, Emit.call_return_slot s ra⟩
    dsimp [Physical, callState, Emit.callState]
    have hs := pre.stack.1
    bv_omega
  · simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec, address] using pre.stackState
  · intro i hi j hj
    simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec, address] using
      pre.stackBlock i (by omega) j hj
  · constructor <;> intro i hi j hj
    · simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec, address] using
        pre.tablesStack.1 i hi j (by omega)
    · simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec, address] using
        pre.tablesStack.2 i hi j (by omega)

/-- The sole trusted premise is invoked exactly at its actual linked entry. -/
theorem compression_helper_runs (e : Executable) (root : Int64)
    (code : Compress.CodeAt e (root - 912)) (correct : CompressionCorrect e root)
    (s : MachineData) (ra : BitVec 64) (chaining : Vector UInt32 8) (block : Vector UInt8 64)
    (pre : CompressionCallPre root s chaining block) :
    Eventually (step e) (CompressionCallPost s chaining block ra)
      (callState s ra, root - 912) := by
  have run := correct (callState s ra) chaining block ra
    (compression_call_pre e root code s ra chaining block pre)
  have address : (s.regs.rsp.toBitVec - 8) - 160 = s.regs.rsp.toBitVec - 168 := by bv_omega
  apply eventually_weaken (step e) _ _ _ _ run
  intro t post
  refine ⟨post.returned, post.state, ?_, ?_⟩
  · intro a outside
    rw [post.frame a (by
      intro h
      rcases h with hs | hs
      · exact outside (Or.inl hs)
      · obtain ⟨i, hi, equal⟩ := hs
        exact outside (Or.inr ⟨i, by omega,
          by simpa only [callState, Emit.callState, UInt64.toBitVec_ofBitVec, address] using equal⟩))]
    apply storeInt_frame s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt a
    intro hs
    obtain ⟨i, hi, equal⟩ := hs
    apply outside
    right
    refine ⟨160 + i, by omega, ?_⟩
    rw [equal]
    bv_omega
  · intro p n mapping i hi
    let a := p + BitVec.ofNat 64 i
    by_cases state : InSpan a s.regs.rdi.toBitVec 32
    · obtain ⟨j, hj, equal⟩ := state
      have hmap := bytesAt_mapped t.1.dmem s.regs.rdi.toBitVec _ post.state
      have byte := hmap j (by simpa only [chainingBytes_length] using hj)
      simpa only [← equal] using byte
    · by_cases stack : InSpan a (s.regs.rsp.toBitVec - 168) 160
      · obtain ⟨j, hj, equal⟩ := stack
        have byte := post.stack.2 j hj
        change ∃ b, t.1.dmem.get?
          ((s.regs.rsp.toBitVec - 8) - 160 + BitVec.ofNat 64 j) = some b at byte
        rw [address, ← equal] at byte
        exact byte
      · have unchanged := post.frame a (by
          intro h
          rcases h with h | h
          · exact state h
          · exact stack (by simpa only [callState, Emit.callState,
              UInt64.toBitVec_ofBitVec, address] using h))
        have mapped' : Mapped (callState s ra).dmem p n :=
          UintCodec.Large.mapped_store _ _ _ _ _ _ mapping
        obtain ⟨b, hb⟩ := mapped' i hi
        exact ⟨b, unchanged.trans hb⟩

end SszX86.Hash

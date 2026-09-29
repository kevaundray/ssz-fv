import SszX86.HashCompressionCall
import SszX86.HashCombineModel
import SszX86.HashCombineExec

namespace SszX86.Hash.Combine
open SszNative.HashStream

/-- The state and call stack are writable; the raw source is an independent
read-only borrow. No relation between the two combine sources is imposed. -/
def DrainWritable (sp : BitVec 64) (a : BitVec 64) : Prop :=
  InSpan a (sp + 8) 112 ∨ InSpan a (sp - 168) 168

structure DrainMemory (root : Int64) (m : DataMem) (sp source : BitVec 64)
    (input : ByteArray) : Prop where
  bytes : BytesAt m source input.data.toList
  sourcePhysical : Physical source input.size
  statePhysical : Physical (sp + 8) 112
  stack : StackAt m sp 168
  state : Mapped m (sp + 8) 112
  tables : TablesAt m root
  tablePhysical : TablesPhysical root
  sourceState : Disjoint source (sp + 8) input.size 112
  sourceStack : Disjoint source (sp - 168) input.size 168
  stackState : Disjoint (sp - 168) (sp + 8) 168 112
  tablesState : TablesDisjoint root (sp + 8) 112
  tablesStack : TablesDisjoint root (sp - 168) 168

private theorem borrowed_safe (sp p : BitVec 64) (n : Nat)
    (state : Disjoint p (sp + 8) n 112)
    (stack : Disjoint p (sp - 168) n 168) :
    ∀ i < n, ¬ DrainWritable sp (p + BitVec.ofNat 64 i) := by
  intro i hi inside
  rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
  · exact state i hi j hj equal
  · exact stack i hi j hj equal

/-- Physical slicing is valid even at an empty one-past-the-end interval. -/
theorem physical_slice (p : BitVec 64) (n offset count : Nat)
    (physical : Physical p n) (bound : offset + count ≤ n) :
    Physical (p + BitVec.ofNat 64 offset) count := by
  unfold Physical at physical ⊢
  by_cases empty : count = 0
  · subst count
    have := (p + BitVec.ofNat 64 offset).isLt
    omega
  · have strict : offset < 2 ^ 64 := by omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt strict]
    have addBound : p.toNat + offset < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt addBound]
    omega

/-- A helper's exact bounded frame transports every current ownership fact. -/
theorem DrainMemory.after (root : Int64) (m m' : DataMem) (sp source : BitVec 64)
    (input : ByteArray) (before : DrainMemory root m sp source input)
    (frame : MemoryFrame m m' (DrainWritable sp))
    (mapping : MappedPreserved m m') : DrainMemory root m' sp source input := by
  refine ⟨?_, before.sourcePhysical, before.statePhysical,
    ⟨before.stack.1, mapping _ _ before.stack.2⟩, mapping _ _ before.state,
    ?_, before.tablePhysical, before.sourceState, before.sourceStack,
    before.stackState, before.tablesState, before.tablesStack⟩
  · exact bytesAt_frame m m' source input.data.toList _ before.bytes frame
      (by simpa only [Array.length_toList, ByteArray.size_data] using
        borrowed_safe sp source input.size before.sourceState before.sourceStack)
  · constructor
    · apply bytesAt_frame m m' _ _ _ before.tables.1 frame
      simpa only [initialBytes] using
        borrowed_safe sp (initialAddress root) 32 before.tablesState.1 before.tablesStack.1
    · apply bytesAt_frame m m' _ _ _ before.tables.2 frame
      simpa only [roundsBytes] using
        borrowed_safe sp (roundsAddress root) 256 before.tablesState.2 before.tablesStack.2

theorem inputBlock_bytes (m : DataMem) (source : BitVec 64)
    (input : ByteArray) (start : Nat) (bound : start + 64 ≤ input.size)
    (bytes : BytesAt m source input.data.toList) :
    BytesAt m (source + BitVec.ofNat 64 start) (inputBlock input start bound).toList := by
  intro i hi
  have small : i < 64 := by simpa only [Vector.length_toList] using hi
  have sourceBound : start + i < input.data.toList.length := by
    simp only [Array.length_toList, ByteArray.size_data]
    omega
  rw [memmove_addr_add]
  rw [bytes (start + i) sourceBound]
  simp only [List.getElem?_eq_getElem sourceBound, List.getElem?_eq_getElem hi,
    Vector.getElem_toList, inputBlock, Vector.getElem_ofFn,
    Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

/-- A direct loop's compression precondition is constructed solely from the
current exact state and the next physical 64-byte source interval. -/
theorem direct_compression_pre (root : Int64) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stateAt : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainingReg : s.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.rsi.toBitVec = source + BitVec.ofNat 64 start)
    (full : start + 64 ≤ input.size) :
    CompressionCallPre root s state.chaining (inputBlock input start full) := by
  have chainAddress : s.regs.rsp.toBitVec + 72 = (s.regs.rsp.toBitVec + 8) + 64 := by
    bv_omega
  refine ⟨?_, ?_, memory.tables, ?_, ?_, memory.tablePhysical,
    memory.stack, ?_, ?_, ?_, ?_, memory.tablesStack⟩
  · rw [chainingReg, chainAddress]
    exact stateAt_chaining _ _ _ stateAt
  · rw [sourceReg]
    exact inputBlock_bytes _ _ _ _ full memory.bytes
  · rw [chainingReg, chainAddress]
    exact physical_slice _ 112 64 32 memory.statePhysical (by decide)
  · rw [sourceReg]
    exact physical_slice _ input.size start 64 memory.sourcePhysical full
  · rw [chainingReg, chainAddress, sourceReg]
    exact disjoint_subrange _ _ 112 input.size 64 32 start 64
      (disjoint_symm _ _ _ _ memory.sourceState) (by decide) full
  · rw [chainingReg, chainAddress]
    have h := disjoint_subrange _ _ 168 112 0 168 64 32
      memory.stackState (by decide) (by decide)
    simpa only [BitVec.add_zero] using h
  · rw [sourceReg]
    have h := disjoint_subrange _ _ 168 input.size 0 168 start 64
      (disjoint_symm _ _ _ _ memory.sourceStack) (by decide) full
    simpa only [BitVec.add_zero] using h
  · rw [chainingReg, chainAddress]
    constructor
    · have h := disjoint_subrange _ _ 32 112 0 32 64 32
        memory.tablesState.1 (by decide) (by decide)
      simpa only [BitVec.add_zero] using h
    · have h := disjoint_subrange _ _ 256 112 0 256 64 32
        memory.tablesState.2 (by decide) (by decide)
      simpa only [BitVec.add_zero] using h

/-- The compression helper cannot write the live source or any stale buffer
byte; its caller-visible footprint is contained in the ordinary drain frame. -/
theorem compression_frame_drain (s : MachineData) (state : Vector UInt32 8)
    (block : Vector UInt8 64) (ra : BitVec 64) (t : MachineState)
    (chain : s.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 72)
    (post : CompressionCallPost s state block ra t) :
    MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec) := by
  apply frame_mono _ _ _ _ post.frame
  intro a inside
  rcases inside with ⟨i, hi, equal⟩ | stack
  · left
    refine ⟨64 + i, by omega, ?_⟩
    rw [equal, chain]
    bv_omega
  · exact Or.inr stack

end SszX86.Hash.Combine

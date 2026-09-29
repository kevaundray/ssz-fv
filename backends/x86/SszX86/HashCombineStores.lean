import SszX86.HashCombineEntry
import SszX86.HashCombineDrainMemory
import SszX86.HashStateUpdate

namespace SszX86.Hash.Combine
open SszNative.HashStream

theorem storeWord_frame (s : MachineData) (offset : Nat) (value : BitVec 64)
    (low : 8 ≤ offset) (high : offset + 8 ≤ 120) :
    MemoryFrame s.dmem (storeWord s offset value).dmem (DrainWritable s.regs.rsp.toBitVec) := by
  apply frame_mono _ _ _ _ (storeInt_frame _ _ _ _)
  intro a inside
  rcases inside with ⟨i, hi, equal⟩
  left
  refine ⟨offset - 8 + i, by omega, ?_⟩
  rw [equal]
  bv_omega

theorem storeWord_mapping (s : MachineData) (offset : Nat) (value : BitVec 64) :
    MappedPreserved s.dmem (storeWord s offset value).dmem := by
  intro p n mapping
  exact Large.mapped_store _ _ _ _ _ _ mapping

theorem storeWord_memory (root : Int64) (s : MachineData) (source : BitVec 64)
    (input : ByteArray) (offset : Nat) (value : BitVec 64)
    (low : 8 ≤ offset) (high : offset + 8 ≤ 120)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input) :
    DrainMemory root (storeWord s offset value).dmem s.regs.rsp.toBitVec source input :=
  DrainMemory.after root _ _ _ _ _ memory
    (storeWord_frame s offset value low high) (storeWord_mapping s offset value)

theorem state_buffered_word (s : MachineData) (state : Model)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state) :
    Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 104) 8 =
      some (Int.ofBytes (wordBytes (BitVec.ofNat 64 state.buffered.val))) := by
  have location : (s.regs.rsp.toBitVec + 8) + 96 = s.regs.rsp.toBitVec + 104 := by bv_omega
  have small : state.buffered.val < 2 ^ 64 := by have := state.buffered.isLt; omega
  simpa only [location, wordBytes, uintBytes_eq_toBytes, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small] using stateAt_buffered _ _ _ stored

theorem state_length_word (s : MachineData) (state : Model)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state) :
    Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 112) 8 =
      some (Int.ofBytes (wordBytes state.byteLen.toBitVec)) := by
  have location : (s.regs.rsp.toBitVec + 8) + 104 = s.regs.rsp.toBitVec + 112 := by bv_omega
  simpa only [location, wordBytes, uintBytes_eq_toBytes, UInt64.toNat_toBitVec] using
    stateAt_byteLen _ _ _ stored

/-- A raw count64 does not occur in any premise: buffer compression requires
only the two actual read/write fields and ordinary allocation ownership. -/
theorem buffer_compression_pre (root : Int64) (s : MachineData)
    (words : Vector UInt32 8) (buffer : Vector UInt8 64)
    (chainReg : s.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 72)
    (bufferReg : s.regs.rsi.toBitVec = s.regs.rsp.toBitVec + 8)
    (chaining : ChainingAt s.dmem (s.regs.rsp.toBitVec + 72) words)
    (block : BytesAt s.dmem (s.regs.rsp.toBitVec + 8) buffer.toList)
    (physical : Physical (s.regs.rsp.toBitVec + 8) 112)
    (stack : StackAt s.dmem s.regs.rsp.toBitVec 168)
    (stackState : Disjoint (s.regs.rsp.toBitVec - 168) (s.regs.rsp.toBitVec + 8) 168 112)
    (tables : TablesAt s.dmem root) (tablePhysical : TablesPhysical root)
    (tablesState : TablesDisjoint root (s.regs.rsp.toBitVec + 8) 112)
    (tablesStack : TablesDisjoint root (s.regs.rsp.toBitVec - 168) 168) :
    CompressionCallPre root s words buffer := by
  have chainAddress : s.regs.rsp.toBitVec + 72 = (s.regs.rsp.toBitVec + 8) + 64 := by
    bv_omega
  refine ⟨?_, ?_, tables, ?_, ?_, tablePhysical, stack, ?_, ?_, ?_, ?_, tablesStack⟩
  · simpa only [chainReg] using chaining
  · simpa only [bufferReg] using block
  · rw [chainReg, chainAddress]
    exact physical_slice _ 112 64 32 physical (by decide)
  · rw [bufferReg]
    unfold Physical at physical ⊢
    omega
  · rw [chainReg, bufferReg]
    intro i hi j hj equal
    bv_omega
  · rw [chainReg, chainAddress]
    have h := disjoint_subrange _ _ 168 112 0 168 64 32 stackState (by decide) (by decide)
    simpa only [BitVec.add_zero] using h
  · rw [bufferReg]
    intro i hi j hj
    exact stackState i hi j (by omega)
  · rw [chainReg, chainAddress]
    constructor
    · have h := disjoint_subrange _ _ 32 112 0 32 64 32 tablesState.1 (by decide) (by decide)
      simpa only [BitVec.add_zero] using h
    · have h := disjoint_subrange _ _ 256 112 0 256 64 32 tablesState.2 (by decide) (by decide)
      simpa only [BitVec.add_zero] using h

end SszX86.Hash.Combine

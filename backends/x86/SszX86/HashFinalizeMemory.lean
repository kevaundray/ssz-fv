import SszX86.HashFinalizeReturn
import SszX86.HashHelpers
import SszX86.HashCompressionCall
import SszX86.EmitReturnMemory

namespace SszX86.Hash.Finalize

/-- Local work excludes the saved registers, original RET slot, and byte counter. -/
def WorkWritable (entry : MachineData) (a : BitVec 64) : Prop :=
  InSpan a entry.regs.rdi.toBitVec 32 ∨
  InSpan a entry.regs.rsi.toBitVec 104 ∨
  InSpan a (entry.regs.rsp.toBitVec - 192) 168


theorem store_mappedPreserved (m : DataMem) (p : BitVec 64) (n : Nat) (v : Int) :
    MappedPreserved m (Mem.storeInt m p n v) := by
  intro q k mapping
  exact UintCodec.Large.mapped_store m q p k n v mapping

theorem work_subset (entry : MachineData) :
    ∀ a, WorkWritable entry a → FinalizeWritable entry a := by
  intro a h
  rcases h with h | h | h
  · exact Or.inl h
  · rcases h with ⟨i, hi, equal⟩
    exact Or.inr (Or.inl ⟨i, by omega, equal⟩)
  · rcases h with ⟨i, hi, equal⟩
    exact Or.inr (Or.inr ⟨i, by omega, equal⟩)

theorem saved_outside_work (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root entry state ra) (i : Nat) (hi : i < 24) :
    ¬ WorkWritable entry (entry.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 i) := by
  intro inside
  have address : entry.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 i =
      (entry.regs.rsp.toBitVec - 192) + BitVec.ofNat 64 (176 + i) := by bv_omega
  rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
  · exact pre.stackOutput (176 + i) (by omega) j hj (address.symm.trans equal)
  · exact pre.stackState (176 + i) (by omega) j (by omega) (address.symm.trans equal)
  · have spBound := pre.stack.1
    have spPhysical := pre.returnSlot.1
    unfold Physical at spPhysical
    bv_omega

theorem length_outside_work (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root entry state ra) (i : Nat) (hi : i < 8) :
    ¬ WorkWritable entry (entry.regs.rsi.toBitVec + 104 + BitVec.ofNat 64 i) := by
  intro inside
  have address : entry.regs.rsi.toBitVec + 104 + BitVec.ofNat 64 i =
      entry.regs.rsi.toBitVec + BitVec.ofNat 64 (104 + i) := by bv_omega
  rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
  · exact pre.stateOutput (104 + i) (by omega) j hj (address.symm.trans equal)
  · have physical := pre.statePhysical
    unfold Physical at physical
    bv_omega
  · exact pre.stackState j (by omega) (104 + i) (by omega) (equal.symm.trans address)

theorem table_outside_work (entry : MachineData)
    (p : BitVec 64) (n : Nat)
    (out : Disjoint p entry.regs.rdi.toBitVec n 32)
    (st : Disjoint p entry.regs.rsi.toBitVec n 112)
    (stack : Disjoint p (entry.regs.rsp.toBitVec - 192) n 192)
    (i : Nat) (hi : i < n) : ¬ WorkWritable entry (p + BitVec.ofNat 64 i) := by
  intro inside
  rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
  · exact out i hi j hj equal
  · exact st i hi j (by omega) equal
  · exact stack i hi j (by omega) equal

/-- Ordinary memory observations maintained throughout the consuming wrapper. -/
structure MemoryLive (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (m : DataMem) : Prop where
  stateMapped : Mapped m entry.regs.rsi.toBitVec 112
  output : Mapped m entry.regs.rdi.toBitVec 32
  stack : StackAt m entry.regs.rsp.toBitVec 192
  saved : SavedAt m (entry.regs.rsp.toBitVec - 24)
    entry.regs.rbx.toBitVec entry.regs.r14.toBitVec ra
  byteLen : Mem.loadInt m (entry.regs.rsi.toBitVec + 104) 8 =
    some (state.byteLen.toNat : Int)
  tables : TablesAt m root
  frame : MemoryFrame entry.dmem m (FinalizeWritable entry)

theorem memory_update (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root entry state ra)
    (before after : DataMem) (live : MemoryLive root entry state ra before)
    (frame : MemoryFrame before after (WorkWritable entry))
    (mapping : MappedPreserved before after) : MemoryLive root entry state ra after := by
  refine ⟨mapping _ _ live.stateMapped, mapping _ _ live.output,
    ⟨live.stack.1, mapping _ _ live.stack.2⟩, ?_, ?_, ?_, ?_⟩
  · have readSame (off : Nat) (bound : off + 8 ≤ 24) :
        Mem.loadInt after (entry.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 off) 8 =
        Mem.loadInt before (entry.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 off) 8 := by
      apply Emit.frame_load before after (WorkWritable entry) frame
      intro i hi
      rw [memmove_addr_add]
      exact saved_outside_work root entry state ra pre (off + i) (by omega)
    have l0 := readSame 0 (by decide)
    have l8 := readSame 8 (by decide)
    have l16 := readSame 16 (by decide)
    have aZero : entry.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 0 =
        entry.regs.rsp.toBitVec - 16 := by bv_omega
    rw [aZero] at l0
    simp only [show BitVec.ofNat 64 8 = (8 : BitVec 64) by rfl,
      show BitVec.ofNat 64 16 = (16 : BitVec 64) by rfl] at l8 l16
    have a0 : entry.regs.rsp.toBitVec - 24 + 8 = entry.regs.rsp.toBitVec - 16 := by bv_omega
    have a8 : entry.regs.rsp.toBitVec - 24 + 16 = entry.regs.rsp.toBitVec - 16 + 8 := by bv_omega
    have a16 : entry.regs.rsp.toBitVec - 24 + 24 = entry.regs.rsp.toBitVec - 16 + 16 := by bv_omega
    simpa only [SavedAt, a0, a8, a16, l0, l8, l16] using live.saved
  · rw [Emit.frame_load before after (WorkWritable entry) frame _ 8
      (length_outside_work root entry state ra pre)]
    exact live.byteLen
  · constructor
    · exact bytesAt_frame before after (initialAddress root) initialBytes
        (WorkWritable entry) live.tables.1 frame (by
          intro i hi
          exact table_outside_work entry _ 32
            pre.tablesOutput.1 pre.tablesState.1 pre.tablesStack.1 i
            (by simpa only [initialBytes_length] using hi))
    · exact bytesAt_frame before after (roundsAddress root) roundsBytes
        (WorkWritable entry) live.tables.2 frame (by
          intro i hi
          exact table_outside_work entry _ 256
            pre.tablesOutput.2 pre.tablesState.2 pre.tablesStack.2 i
            (by simpa only [roundsBytes_length] using hi))
  · intro a outside
    rw [frame a (fun h => outside (work_subset entry a h))]
    exact live.frame a outside

/-- Registers reserved by the wrapper while caller-saved scratch registers vary. -/
structure RegsLive (entry current : MachineData) : Prop where
  output : current.regs.rbx = entry.regs.rdi
  state : current.regs.r14 = entry.regs.rsi
  stack : current.regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 24
  rbp : current.regs.rbp = entry.regs.rbp
  r12 : current.regs.r12 = entry.regs.r12
  r13 : current.regs.r13 = entry.regs.r13
  r15 : current.regs.r15 = entry.regs.r15

end SszX86.Hash.Finalize

import SszX86.HashFinalizeMemory
import SszX86.HashMemoryUpdate

namespace SszX86.Hash.Finalize
open SszNative.HashStream

/-- All three stack stores preserve every old mapping. -/
theorem saved_mapped (s : MachineData) : MappedPreserved s.dmem (savedMem s) := by
  intro p n mapping
  unfold savedMem
  repeat' first | exact mapping | apply UintCodec.Large.mapped_store

theorem saved_frame (s : MachineData) :
    MemoryFrame s.dmem (savedMem s) (fun a => InSpan a (s.regs.rsp.toBitVec - 24) 24) := by
  intro a outside
  have unchanged (m : DataMem) (off : Nat) (lo : 8 ≤ off) (hi : off ≤ 24) (v : Int) :
      (Mem.storeInt m (s.regs.rsp.toBitVec - BitVec.ofNat 64 off) 8 v).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro j hj equal
    have hj' : j < 8 := by simpa only [Int.toBytes_length] using hj
    apply outside
    refine ⟨24 - off + j, by omega, ?_⟩
    rw [equal]
    bv_omega
  unfold savedMem
  rw [unchanged _ 24 (by decide) (by decide), unchanged _ 16 (by decide) (by decide),
    unchanged _ 8 (by decide) (by decide)]

private theorem stack_apart (m : DataMem) (sp : BitVec 64) (a b : Nat)
    (ha : a ≤ 24) (hb : b ≤ 24) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) (v : Int) :
    Mem.loadInt (Mem.storeInt m (sp - BitVec.ofNat 64 b) 8 v)
      (sp - BitVec.ofNat 64 a) 8 = Mem.loadInt m (sp - BitVec.ofNat 64 a) 8 := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

private theorem stored_word (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 =
      some (Int.ofBytes (wordBytes value)) := by
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact load_store_same m p 8 value.toInt (by decide)

theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 24)
      s.regs.rbx.toBitVec s.regs.r14.toBitVec ra := by
  have address (off : BitVec 64) : s.regs.rsp.toBitVec - 24 + off =
      s.regs.rsp.toBitVec - (24 - off) := by bv_omega
  simp only [SavedAt, address, BitVec.reduceSub]
  refine ⟨?_, ?_, ?_⟩
  · unfold savedMem
    rw [stack_apart _ s.regs.rsp.toBitVec 16 24 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  · unfold savedMem
    rw [stack_apart _ s.regs.rsp.toBitVec 8 24 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 16 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  · have unchanged := Emit.frame_load s.dmem (savedMem s) _ (saved_frame s)
      s.regs.rsp.toBitVec 8 (by
        intro i hi inside
        obtain ⟨j, hj, equal⟩ := inside
        bv_omega)
    simpa only [BitVec.sub_zero, unchanged] using ret

theorem saved_stateAt (root : Int64) (s : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root s state ra) : StateAt (savedMem s) s.regs.rsi.toBitVec state := by
  apply bytesAt_frame s.dmem (savedMem s) s.regs.rsi.toBitVec _ _ pre.state (saved_frame s)
  intro i hi inside
  obtain ⟨j, hj, equal⟩ := inside
  have hi' : i < 112 := by simpa only [Vector.length_toList] using hi
  have addr : s.regs.rsp.toBitVec - 24 + BitVec.ofNat 64 j =
      s.regs.rsp.toBitVec - 192 + BitVec.ofNat 64 (168 + j) := by bv_omega
  exact pre.stackState (168 + j) (by omega) i hi' (addr.symm.trans equal.symm)

theorem saved_memoryLive (root : Int64) (s : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root s state ra) : MemoryLive root s state ra (savedMem s) := by
  have state' := saved_stateAt root s state ra pre
  refine ⟨stateAt_mapped _ _ _ state', saved_mapped s _ _ pre.output,
    ⟨pre.stack.1, saved_mapped s _ _ pre.stack.2⟩, saved_at s ra pre.returnSlot.2,
    ?_, ?_, ?_⟩
  · rw [stateAt_byteLen _ _ _ state', scalar_bytes_value 8 state.byteLen.toNat
      (by exact state.byteLen.toBitVec.isLt)]
  · have preserve (p : BitVec 64) (bytes : List UInt8)
        (before : BytesAt s.dmem p bytes)
        (apart : Disjoint p (s.regs.rsp.toBitVec - 192) bytes.length 192) :
        BytesAt (savedMem s) p bytes := by
      apply bytesAt_frame s.dmem (savedMem s) p bytes _ before (saved_frame s)
      intro i hi inside
      obtain ⟨j, hj, equal⟩ := inside
      apply apart i hi (168 + j) (by omega)
      rw [equal]
      bv_omega
    exact ⟨preserve _ _ pre.tables.1 (by simpa [initialBytes] using pre.tablesStack.1),
      preserve _ _ pre.tables.2 (by simpa [roundsBytes] using pre.tablesStack.2)⟩
  · apply frame_mono s.dmem (savedMem s) _ _ (saved_frame s)
    intro a inside
    obtain ⟨i, hi, equal⟩ := inside
    refine Or.inr (Or.inr ⟨168 + i, by omega, ?_⟩)
    rw [equal]
    bv_omega

theorem state_store_work (entry : MachineData) (offset storeWidth : Nat)
    (bound : offset + storeWidth ≤ 104) :
    ∀ a, InSpan a (entry.regs.rsi.toBitVec + BitVec.ofNat 64 offset) storeWidth →
      WorkWritable entry a := by
  intro a inside
  obtain ⟨i, hi, equal⟩ := inside
  refine Or.inr (Or.inl ⟨offset + i, by omega, ?_⟩)
  simpa only [memmove_addr_add] using equal

/-- Uniform ownership transfer for a scalar store in the consumed state. -/
theorem state_store_live (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root entry state ra)
    (m : DataMem) (live : MemoryLive root entry state ra m)
    (offset storeWidth : Nat) (bound : offset + storeWidth ≤ 104) (value : Int) :
    MemoryLive root entry state ra
      (Mem.storeInt m (entry.regs.rsi.toBitVec + BitVec.ofNat 64 offset) storeWidth value) := by
  apply memory_update root entry state ra pre m _ live
  · exact frame_mono _ _ _ _ (storeInt_frame m _ storeWidth value)
      (state_store_work entry offset storeWidth bound)
  · exact store_mappedPreserved _ _ _ _

end SszX86.Hash.Finalize

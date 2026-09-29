import SszX86.HashFinalizeStart

namespace SszX86.Hash.Finalize
open SszNative.HashStream WordNormalize

/-- A bounded store leaves a disjoint native-state field byte-exact. -/
theorem state_store_preserve (m : DataMem) (p : BitVec 64)
    (physical : Physical p 112) (offset storeWidth field : Nat) (bytes : List UInt8)
    (writeBound : offset + storeWidth ≤ 112) (readBound : field + bytes.length ≤ 112)
    (apart : offset + storeWidth ≤ field ∨ field + bytes.length ≤ offset)
    (value : Int) (before : BytesAt m (p + BitVec.ofNat 64 field) bytes) :
    BytesAt (Mem.storeInt m (p + BitVec.ofNat 64 offset) storeWidth value)
      (p + BitVec.ofNat 64 field) bytes := by
  apply bytesAt_frame m _ _ bytes _ before (storeInt_frame _ _ _ _)
  intro i hi inside
  obtain ⟨j, hj, equal⟩ := inside
  unfold Physical at physical
  simp only [memmove_addr_add] at equal
  bv_omega

structure PrefixPost (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (s : MachineData) : Prop where
  memory : MemoryLive root entry state ra s.dmem
  regs : RegsLive entry s
  buffer : BytesAt s.dmem entry.regs.rsi.toBitVec (delimiterBuffer state).toList
  chaining : ChainingAt s.dmem (entry.regs.rsi.toBitVec + 64) state.chaining
  oldCount : get s .rax = BitVec.ofNat 64 state.buffered.val
  newCount : get s .rdi = BitVec.ofNat 64 (state.buffered.val + 1)

/-- Entry through the delimiter, incremented count store, and first padding test.
Both panic guards are discharged from the original Fin64 count. -/
theorem prefix_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra) (P : MachineState → Prop)
    (next : ∀ s, PrefixPost root entry state ra s →
      Eventually (step e) P (s, root - 256 + 40)) :
    Eventually (step e) P (entry, root - 256) := by
  let n := BitVec.ofNat 64 state.buffered.val
  let s0 := savedState entry
  let s1 := put s0 .rbx (get entry .rdi)
  let s2 := put s1 .rdi n
  let s3 := compare s2 n 63
  let s4 := delimiterState s3
  let s5 := put s4 .rax n
  let s6 := advanceState s5
  have countBound := state.buffered.isLt
  have nn : n.toNat = state.buffered.val := by
    simp only [n, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : state.buffered.val < 2^64)]
  have increment : n + 1 = BitVec.ofNat 64 (state.buffered.val + 1) := by
    dsimp [n]
    bv_omega
  have oldState := saved_stateAt root entry state ra pre
  have live0 := saved_memoryLive root entry state ra pre
  have oldBuffer := stateAt_buffer _ _ _ oldState
  have oldChaining := stateAt_chaining _ _ _ oldState
  have oldCount : Mem.loadInt (savedMem entry) (entry.regs.rsi.toBitVec + 96) 8 =
      some (n.toNat : Int) := by
    rw [stateAt_buffered _ _ _ oldState,
      scalar_bytes_value 8 state.buffered.val (by omega), nn]
  have map0 := stateAt_mapped _ _ _ oldState
  have delimiterMapped : ∃ old, Mem.loadInt s3.dmem (get s3 .rsi + get s3 .rdi) 1 = some old := by
    change ∃ old, Mem.loadInt (savedMem entry) (entry.regs.rsi.toBitVec + n) 1 = some old
    exact UintCodec.Large.mapped_load _ _ 112 state.buffered.val 1 map0 (by omega)
  have mem4 : s4.dmem = Mem.storeInt (savedMem entry)
      (entry.regs.rsi.toBitVec + BitVec.ofNat 64 state.buffered.val) 1 (-128) := rfl
  have live4 : MemoryLive root entry state ra s4.dmem := by
    rw [mem4]
    exact state_store_live root entry state ra pre _ live0 state.buffered.val 1 (by omega) (-128)
  have count4 : Mem.loadInt s4.dmem (get s4 .rsi + 96) 8 = some (n.toNat : Int) := by
    change Mem.loadInt (Mem.storeInt (savedMem entry)
      (entry.regs.rsi.toBitVec + n) 1 (-128)) (entry.regs.rsi.toBitVec + 96) 8 = _
    rw [load_store_disjoint]
    · exact oldCount
    · intro i hi j hj
      have physical := pre.statePhysical
      unfold Physical at physical
      dsimp [n]
      bv_omega
  have buffer4 : BytesAt s4.dmem entry.regs.rsi.toBitVec (delimiterBuffer state).toList := by
    rw [mem4]
    apply bytesAt_overwrite _ _ _ state.buffer state.buffered.val [0x80]
      (by simp; omega)
    · have h := pre.statePhysical
      unfold Physical at h ⊢
      omega
    · exact oldBuffer
    · simpa only [show Int.toBytes 1 (-128) = [0x80] by decide] using
        storeInt_bytes (savedMem entry) (entry.regs.rsi.toBitVec + n) 1 (-128) (by decide)
    · simpa only [List.length_cons, List.length_nil] using
        storeInt_frame (savedMem entry) (entry.regs.rsi.toBitVec + n) 1 (-128)
  have chain4 : ChainingAt s4.dmem (entry.regs.rsi.toBitVec + 64) state.chaining := by
    rw [mem4]
    exact state_store_preserve _ _ pre.statePhysical state.buffered.val 1 64
      (chainingBytes state.chaining) (by omega) (by simp) (Or.inl (by omega)) (-128) oldChaining
  have mem6 : s6.dmem = Mem.storeInt s4.dmem (entry.regs.rsi.toBitVec + 96) 8 (n + 1).toInt := rfl
  have live6 : MemoryLive root entry state ra s6.dmem := by
    rw [mem6]
    exact state_store_live root entry state ra pre _ live4 96 8 (by decide) _
  have buffer6 : BytesAt s6.dmem entry.regs.rsi.toBitVec (delimiterBuffer state).toList := by
    rw [mem6]
    simpa only [BitVec.add_zero] using
      state_store_preserve _ _ pre.statePhysical 96 8 0 (delimiterBuffer state).toList
        (by decide) (by simp) (Or.inr (by simp)) (n + 1).toInt
        (by simpa only [BitVec.add_zero] using buffer4)
  have chain6 : ChainingAt s6.dmem (entry.regs.rsi.toBitVec + 64) state.chaining := by
    rw [mem6]
    exact state_store_preserve _ _ pre.statePhysical 96 8 64 (chainingBytes state.chaining)
      (by decide) (by simp) (Or.inr (by simp)) (n + 1).toInt chain4
  have regs6 : RegsLive entry s6 := by
    constructor <;> rfl
  have post : PrefixPost root entry state ra s6 :=
    ⟨live6, regs6, buffer6, chain6, rfl, increment⟩
  apply pushes_runs e (root - 256) hc.finalize entry P
  · simpa only [BitVec.sub_zero] using
      (stack_subrange entry.dmem entry.regs.rsp.toBitVec 192 0 24 pre.stack (by decide)).2
  apply capture_output_runs
  apply load_buffered_runs e (root - 256) hc.finalize s1 n P
  · exact oldCount
  apply check_buffered_runs e (root - 256) hc.finalize s2 P
  · change n.toNat ≤ 63
    rw [nn]
    omega
  apply delimiter_runs e (root - 256) hc.finalize s3 P delimiterMapped
  apply reload_buffered_runs e (root - 256) hc.finalize s4 n P count4
  apply advance_runs e (root - 256) hc.finalize s5 P
  · exact ⟨_, count4⟩
  exact next s6 post

end SszX86.Hash.Finalize

import SszArm.HashCombineRightGuard
import SszArm.HashCombineBuffered

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

@[simp] theorem bufferedSetup_program (s : ArmState) : (bufferedSetup s).program = s.program := by
  simp only [bufferedSetup, block_program]

@[simp] theorem bufferedSetup_error (s : ArmState) : read_err (bufferedSetup s) = read_err s := by
  simp only [bufferedSetup, block_error]

@[simp] theorem bufferedSetup_memory (s : ArmState) : (bufferedSetup s).mem = s.mem := by
  simp [bufferedSetup, bufferedSetupOps, block, Op.effect, put, next, state_simp_rules]

theorem bufferedSetup_register (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [0#5, 1#5, 20#5, 21#5]) :
    r (.GPR reg) (bufferedSetup s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h20 : reg ≠ 20#5 := by simp_all
  have h21 : reg ≠ 21#5 := by simp_all
  simp [bufferedSetup, bufferedSetupOps, block, Op.effect, put, next,
    state_simp_rules, h0, h1, h20, h21]

@[simp] theorem bufferedSetup_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (bufferedSetup s) = r (.SFP reg) s := by
  simp [bufferedSetup, bufferedSetupOps, block, Op.effect, put, next, state_simp_rules]

theorem bufferedSetup_values (s : ArmState) :
    read_pc (bufferedSetup s) = read_pc s + 16#64 ∧
    r (.GPR 0#5) (bufferedSetup s) = r (.GPR 24#5) s + 64#64 ∧
    r (.GPR 1#5) (bufferedSetup s) = r (.GPR 31#5) s ∧
    r (.GPR 20#5) (bufferedSetup s) = r (.GPR 20#5) s - r (.GPR 23#5) s ∧
    r (.GPR 21#5) (bufferedSetup s) = r (.GPR 21#5) s + r (.GPR 23#5) s := by
  simp [bufferedSetup, bufferedSetupOps, block, Op.effect, put, next,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem reset_program (s : ArmState) : (reset s).program = s.program := by
  simp only [reset, block_program]

@[simp] theorem reset_error (s : ArmState) : read_err (reset s) = read_err s := by
  simp only [reset, block_error]

theorem reset_register (s : ArmState) (reg : BitVec 5)
    (notSP : reg ≠ 31#5) (not9 : reg ≠ 9#5) (not10 : reg ≠ 10#5) :
    r (.GPR reg) (reset s) = r (.GPR reg) s := by
  simp [reset, resetOps, block, Op.effect, put, load, store, next,
    state_simp_rules, notSP, not9, not10]

@[simp] theorem reset_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (reset s) = r (.SFP reg) s := by
  simp [reset, resetOps, block, Op.effect, put, load, store, next, state_simp_rules]

def resetMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s + 96#64) 0#64
    (write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s))

theorem reset_memory (s : ArmState) : (reset s).mem = (resetMemory s).mem := by
  simp [reset, resetOps, block, Op.effect, put, load, store, next,
    resetMemory, state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc]

def resetWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 31#5) s).toNat + 96, 8)]

theorem reset_frame (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 31#5) s).toNat + 104 ≤ 2^64) :
    MemoryFrame (resetWrites s) s (reset s) := by
  intro address outside
  have scratch := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [resetWrites])
  have header := outside ((r (.GPR 31#5) s).toNat + 96, 8) (by simp [resetWrites])
  rw [reset_memory]
  simp only [resetMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]

theorem reset_buffered (s : ArmState) (physical : (r (.GPR 31#5) s).toNat + 104 ≤ 2^64) :
    read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) (reset s) = 0#64 := by
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (reset_memory s))]
  exact read_write_bytes _ 8 _ _ (by bv_omega)

theorem buffered_full_correct (origin s : ArmState) (base : BitVec 64)
    (left right : ByteArray) (consumed : Nat) (consumedBound : consumed ≤ right.size)
    (buffer : Vector UInt8 64) (words : Vector UInt32 8) (byteLen : UInt64)
    (code : CodeAt origin base) (data : DataAt origin base) (compression : CompressionCorrect base)
    (owned : CombineOwned origin base left right) (activation : Activation origin s)
    (pc : read_pc s = base + 248#64)
    (bufferAt : BytesAt s (r (.GPR 31#5) s) ⟨buffer.toArray⟩)
    (chaining : ChainingAt s (r (.GPR 31#5) s + 64#64) words)
    (lengthAt : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s = byteLen.toBitVec)
    (cursor : r (.GPR 21#5) s = r (.GPR 3#5) origin)
    (count : (r (.GPR 20#5) s).toNat = right.size)
    (taken : (r (.GPR 23#5) s).toNat = consumed) :
    ∃ fuel, let t := run fuel s
      Activation origin t ∧ read_pc t = base + 364#64 ∧
      StateAt t (r (.GPR 31#5) t)
        (SszNative.HashStream.drain buffer (SszNative.HashStream.compressBuffer words buffer)
          byteLen right consumed consumedBound).state := by
  have geometry := activation.physical owned.stackLow
  let a := bufferedSetup s
  obtain ⟨aPC, a0, a1, a20, a21⟩ := bufferedSetup_values s
  have aSP : r (.GPR 31#5) a = r (.GPR 31#5) s :=
    bufferedSetup_register s 31#5 (by decide)
  have aCode := (activation.code code).of_program_eq (bufferedSetup_program s)
  have aData : DataAt a base := by
    have before := activation.data owned data
    refine ⟨?_, ?_, before.initialBound, before.roundsBound⟩
    · simpa only [TableAt, BytesAt, a, bufferedSetup_memory] using before.initial
    · simpa only [TableAt, BytesAt, a, bufferedSetup_memory] using before.rounds
  have aError := (bufferedSetup_error s).trans activation.error
  have aAligned : CheckSPAlignment a := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, aSP] using activation.aligned
  have aCallPC : read_pc a = base + 264#64 := by rw [aPC, pc]; bv_omega
  have aWrites : compressionWrites a = directWrites s := by
    simp only [compressionWrites, directWrites, stackSpan, aSP, a0]
  have contained := direct_contained_body s activation.statePointer (by omega)
  have outer := activation.contained owned.stackLow
  have included : ∀ span ∈ compressionWrites a, ∃ big ∈ combineWrites origin,
      big.1 ≤ span.1 ∧ span.1 + span.2 ≤ big.1 + big.2 := by
    intro span member
    rw [aWrites] at member
    obtain ⟨middle, inMiddle, lo, hi⟩ := contained span member
    obtain ⟨big, inBig, lower, upper⟩ := outer middle inMiddle
    exact ⟨big, inBig, by omega, by omega⟩
  have bufferOwned : Protected (compressionWrites a) (r (.GPR 31#5) s).toNat 64 := by
    rw [aWrites]
    right
    intro span member
    simp only [directWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · right; simp only [stackSpan]; omega
    · left; rw [activation.statePointer]; bv_omega
  have aOwned : CompressionOwned a base words ⟨buffer.toArray⟩ := by
    refine ⟨vectorByteArray_size buffer, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [a0, activation.statePointer]
      intro i
      rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (bufferedSetup_memory s)) 4]
      exact chaining i
    · simpa only [BytesAt, a1, a, bufferedSetup_memory] using bufferAt
    · rw [a0, activation.statePointer]; bv_omega
    · rw [a1]; omega
    · rw [aSP]; omega
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      right
      simp only [stackSpan, aSP, a0, activation.statePointer]
      bv_omega
    · simpa only [a1] using bufferOwned
    · exact protected_writes_mono owned.roundsOwned included
  obtain ⟨compressionFuel, returned, newChaining, compressionFrame⟩ :=
    compression_call_correct .buffered a base words ⟨buffer.toArray⟩ aCode aData compression
      aCallPC aError aAligned aOwned
  let m := run (compressionFuel + 1) a
  have mSP : r (.GPR 31#5) m = r (.GPR 31#5) s :=
    returned.sp.trans ((compressEntry_register .buffered a 31#5 (by decide)).trans aSP)
  have preserved (reg : BitVec 5) (lo : 19 ≤ reg.toNat) (hi : reg.toNat ≤ 29) :
      r (.GPR reg) m = r (.GPR reg) a :=
    (returned.registers reg lo (by omega)).trans
      (compressEntry_register .buffered a reg (by bv_omega))
  have mPC : read_pc m = base + 268#64 := by
    rw [returned.pc, compressEntry_link, aCallPC]
    bv_omega
  have mLocal : LocalPost s m := by
    refine ⟨returned.error, returned.program.trans
      ((compressEntry_program .buffered a).trans (bufferedSetup_program s)), mSP, ?_, ?_, ?_, ?_, ?_⟩
    · exact (preserved 19#5 (by decide) (by decide)).trans (bufferedSetup_register s 19#5 (by decide))
    · exact (preserved 24#5 (by decide) (by decide)).trans (bufferedSetup_register s 24#5 (by decide))
    · intro reg lo hi
      exact (preserved reg (by omega) (by omega)).trans
        (bufferedSetup_register s reg (by simp; bv_omega))
    · intro reg lo hi
      rw [returned.vectors reg lo hi]
      simp only [compressEntry, CompressSite.op, Op.effect, call, state_simp_rules,
        bufferedSetup_vector]
    · intro address outside
      have inner : ∀ span ∈ compressionWrites a,
          address.toNat < span.1 ∨ span.1 + span.2 ≤ address.toNat := by
        intro span member
        rw [aWrites] at member
        obtain ⟨big, inBig, lo, hi⟩ := contained span member
        have apart := outside big inBig
        omega
      exact (compressionFrame address inner).trans (congrFun (bufferedSetup_memory s) address)
  have mActivation := activation.after owned.stackLow mLocal
  have mBuffer : BytesAt m (r (.GPR 31#5) m) ⟨buffer.toArray⟩ := by
    rw [mSP]
    apply bytesAt_frame compressionFrame
    · rw [vectorByteArray_size]; omega
    · simpa only [vectorByteArray_size] using bufferOwned
    · simpa only [BytesAt, a, bufferedSetup_memory] using bufferAt
  have mChaining : ChainingAt m (r (.GPR 31#5) m + 64#64)
      (SszNative.HashStream.compressBuffer words buffer) := by
    simpa only [mSP, a0, activation.statePointer, SszNative.HashStream.compressBuffer] using newChaining
  have mLength : read_mem_bytes 8 (r (.GPR 31#5) m + 104#64) m = byteLen.toBitVec := by
    rw [mSP, read_frame _ 8 compressionFrame (by bv_omega)]
    · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (bufferedSetup_memory s)) 8]
      exact lengthAt
    · rw [aWrites]
      right
      intro span member
      simp only [directWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · right; simp only [stackSpan]; bv_omega
      · right; rw [activation.statePointer]; bv_omega
  have mCursor : r (.GPR 21#5) m = r (.GPR 3#5) origin + BitVec.ofNat 64 consumed := by
    rw [preserved 21#5 (by decide) (by decide), a21, cursor]
    bv_omega
  have mCount : (r (.GPR 20#5) m).toNat = right.size - consumed := by
    rw [preserved 20#5 (by decide) (by decide), a20]
    bv_omega
  have mGeometry := mActivation.physical owned.stackLow
  have resetFrame := reset_frame m (by omega) (by omega)
  have resetContained : ∀ span ∈ resetWrites m, ∃ outer ∈ bodyWrites m,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [resetWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨stackSpan m 192, by simp [bodyWrites], ?_, ?_⟩ <;> simp only [stackSpan] <;> omega
    · exact ⟨((r (.GPR 31#5) m).toNat, 224), by simp [bodyWrites], by omega, by omega⟩
  have resetLocal : LocalPost m (reset m) := by
    refine ⟨(reset_error m).trans returned.error, reset_program m, reset_sp m,
      reset_register m 19#5 (by decide) (by decide) (by decide),
      reset_register m 24#5 (by decide) (by decide) (by decide), ?_, ?_,
      frame_mono resetFrame resetContained⟩
    · intro reg lo hi
      exact reset_register m reg (by bv_omega) (by bv_omega) (by bv_omega)
    · intro reg lo hi
      rw [reset_vector]
  have resetActivation := mActivation.after owned.stackLow resetLocal
  have resetPC : read_pc (reset m) = base + 308#64 := by rw [reset_pc, mPC]; bv_omega
  have untouched (address bytes : Nat)
      (lo : (r (.GPR 31#5) m).toNat ≤ address)
      (hi : address + bytes ≤ (r (.GPR 31#5) m).toNat + 96 ∨
        (r (.GPR 31#5) m).toNat + 104 ≤ address) :
      Protected (resetWrites m) address bytes := by
    right
    intro span member
    simp only [resetWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega
  have finalBuffer : BytesAt (reset m) (r (.GPR 31#5) (reset m)) ⟨buffer.toArray⟩ := by
    rw [reset_sp]
    exact bytesAt_frame resetFrame (by rw [vectorByteArray_size]; omega)
      (by rw [vectorByteArray_size]; exact untouched _ _ (by omega) (Or.inl (by omega))) mBuffer
  have finalChaining : ChainingAt (reset m) (r (.GPR 31#5) (reset m) + 64#64)
      (SszNative.HashStream.compressBuffer words buffer) := by
    rw [reset_sp]
    exact mChaining.frame resetFrame (by bv_omega)
      (untouched _ _ (by bv_omega) (Or.inl (by bv_omega)))
  have finalLength : read_mem_bytes 8 (r (.GPR 31#5) (reset m) + 104#64) (reset m) = byteLen.toBitVec := by
    rw [reset_sp, read_frame _ 8 resetFrame (by bv_omega)
      (untouched _ _ (by bv_omega) (Or.inr (by bv_omega)))]
    exact mLength
  obtain ⟨drainFuel, drainPost⟩ := right_guard_drain_correct origin (reset m) base left right
    consumed consumedBound buffer (SszNative.HashStream.compressBuffer words buffer) byteLen
    code data compression owned resetActivation resetPC finalBuffer finalChaining finalLength
    (by rw [reset_register m 21#5 (by decide) (by decide) (by decide)]; exact mCursor)
    (by rw [reset_register m 20#5 (by decide) (by decide) (by decide)]; exact mCount)
  refine ⟨4 + (compressionFuel + 1) + 10 + drainFuel, ?_⟩
  rw [run_plus, run_plus, run_plus,
    bufferedSetup_run s base (activation.code code) activation.error activation.aligned pc,
    reset_run m base (mActivation.code code) mActivation.error mActivation.aligned mPC]
  exact drainPost

end SszArm.Hash.Combine

import SszArm.HashCombinePrelude
import SszArm.HashCombineDrain

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

def leftValue (left right : ByteArray) : StreamState :=
  { (SszNative.HashStream.update SszNative.HashStream.new left).state with
    byteLen := (SszNative.HashStream.update SszNative.HashStream.new left).state.byteLen + UInt64.ofNat right.size }

def leftLengthOps : List Op := [.p180, .p184, .p188, .p192]

@[irreducible] def leftLength (s : ArmState) : ArmState := block leftLengthOps s

theorem leftLength_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 180#64) : run 4 s = leftLength s := by
  have follows : Follows base leftLengthOps s := by
    change r .PC s = _ at pc
    simp [Follows, leftLengthOps, Op.row, Op.effect, load, put, save, next,
      state_simp_rules, pc, BitVec.add_assoc, aligned]
  rw [leftLength]
  exact runs leftLengthOps s base code error follows

@[simp] theorem leftLength_program (s : ArmState) : (leftLength s).program = s.program := by
  simp only [leftLength, block_program]

@[simp] theorem leftLength_error (s : ArmState) : read_err (leftLength s) = read_err s := by
  simp only [leftLength, block_error]

@[simp] theorem leftLength_register (s : ArmState) (reg : BitVec 5) (not8 : reg ≠ 8#5) :
    r (.GPR reg) (leftLength s) = r (.GPR reg) s := by
  simp [leftLength, leftLengthOps, block, Op.effect, load, put, save, next,
    state_simp_rules, not8]

@[simp] theorem leftLength_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (leftLength s) = r (.SFP reg) s := by
  simp [leftLength, leftLengthOps, block, Op.effect, load, put, save, next, state_simp_rules]

private theorem length_store_memory (s : ArmState) (address : BitVec 64)
    (value : BitVec 128) :
    (write_mem_bytes 16 address value s).mem =
      Memory.write_bytes 16 address value s.mem := by
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes]

theorem leftLength_memory (s : ArmState) : (leftLength s).mem =
    (write_mem_bytes 16 (r (.GPR 31#5) s + 96#64)
      ((read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s + r (.GPR 20#5) s) ++ r (.GPR 22#5) s) s).mem := by
  simp [leftLength, leftLengthOps, block, Op.effect, load, put, save, next, state_simp_rules]
  simp only [length_store_memory, ArmState.mem_w_eq_mem]

theorem leftLength_frame (s : ArmState) (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    MemoryFrame [((r (.GPR 31#5) s).toNat + 96, 16)] s (leftLength s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat + 96, 16) (by simp)
  rw [leftLength_memory]
  exact BoolCodec.write_mem_bytes_frame _ _ 16 _ address (by bv_omega) (by bv_omega)

theorem leftLength_fields (s : ArmState) (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) (leftLength s) = r (.GPR 22#5) s ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) (leftLength s) =
      read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s + r (.GPR 20#5) s := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (leftLength_memory s)
  rw [reads 8, reads 8]
  rw [UintCodec.Tail.write_pair_words s (r (.GPR 31#5) s + 96#64)
    (r (.GPR 22#5) s)
    (read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s + r (.GPR 20#5) s)
    (by bv_omega)]
  have highAddress : r (.GPR 31#5) s + 96#64 + 8#64 =
      r (.GPR 31#5) s + 104#64 := by bv_omega
  rw [highAddress]
  constructor
  · rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8
      (r (.GPR 31#5) s + 96#64) (r (.GPR 31#5) s + 104#64) _
      (by bv_omega) (by bv_omega) (by bv_omega)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)
  · exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

theorem leftLength_pc (s : ArmState) (base : BitVec 64) (pc : read_pc s = base + 180#64) :
    read_pc (leftLength s) = if r (.GPR 22#5) s = 0#64 then base + 308#64 else base + 196#64 := by
  change r .PC s = _ at pc
  simp [leftLength, leftLengthOps, block, Op.effect, load, put, save, next,
    state_simp_rules, pc, BitVec.add_assoc]

structure LeftPost (origin t : ArmState) (base : BitVec 64) (left right : ByteArray) : Prop where
  pc : read_pc t = if (leftValue left right).buffered.val = 0 then base + 308#64 else base + 196#64
  error : read_err t = .None
  program : t.program = origin.program
  aligned : CheckSPAlignment t
  sp : r (.GPR 31#5) t = bodySP origin
  x19 : r (.GPR 19#5) t = r (.GPR 0#5) origin
  x20 : r (.GPR 20#5) t = r (.GPR 4#5) origin
  x21 : r (.GPR 21#5) t = r (.GPR 3#5) origin
  x22 : (r (.GPR 22#5) t).toNat = (leftValue left right).buffered.val
  x24 : r (.GPR 24#5) t = r (.GPR 31#5) t
  x25 : r (.GPR 25#5) t = r (.GPR 31#5) t
  saved : Saved origin t
  state : StateAt t (r (.GPR 31#5) t) (leftValue left right)
  frame : MemoryFrame (combineWrites origin) origin t
  data : DataAt t base

theorem left_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    ∃ fuel, LeftPost s (run fuel s) base left right := by
  obtain ⟨prefixFuel, ready⟩ := prelude_correct s base left right code data pc error aligned owned
  let p := run prefixFuel s
  change PreludePost s p base left right at ready
  let value := (SszNative.HashStream.update SszNative.HashStream.new left).state
  have model :
      (SszNative.HashStream.drain SszNative.HashStream.new.buffer
        SszNative.HashStream.new.chaining (UInt64.ofNat left.size) left 0 (Nat.zero_le _)).state = value := by
    simp [value, SszNative.HashStream.update, SszNative.HashStream.new]
  have low := owned.stackLow
  have pNat : (r (.GPR 31#5) p).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [ready.sp]; simp only [bodySP]; bv_omega
  have physical : (r (.GPR 31#5) p).toNat + 304 ≤ 2^64 := by
    have upper := (r (.GPR 31#5) s).isLt
    rw [pNat]; omega
  have contained : ∀ span ∈ drainWrites p, ∃ outer ∈ combineWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [drainWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
        simp only [stackSpan, pNat] <;> omega
  have bufferContained : ∀ span ∈ [((r (.GPR 31#5) p).toNat, 64)],
      ∃ outer ∈ combineWrites s,
        outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, pNat] <;> omega
  have pData : DataAt p base := data.frame ready.frame owned.initialOwned owned.roundsOwned
  obtain ⟨drainFuel, drained, qData, qCount, qBuffer, qChaining, qLength⟩ :=
    drain_correct .left p base (r (.GPR 1#5) s) left 0 (Nat.zero_le _)
      SszNative.HashStream.new.buffer SszNative.HashStream.new.chaining (UInt64.ofNat left.size)
      (code.of_program_eq ready.program) pData compression
      (by simpa only [Side.start, Side.stop, Nat.sub_zero] using ready.pc)
      ready.error ready.aligned (ready.directOwned owned) ready.x24 (by omega)
      (protected_writes_mono owned.leftOwned bufferContained)
      (protected_writes_mono owned.initialOwned contained)
      (protected_writes_mono owned.roundsOwned contained)
      ready.state.buffer ready.state.byteLen
      (by
        have cursor := ready.x23
        simp only [Side.cursor]
        arm_word_nf at cursor ⊢
        simpa only [BitVec.add_zero] using cursor)
      (by
        have count := (congrArg BitVec.toNat ready.x22).trans owned.leftLength
        simp only [Side.count, Nat.sub_zero]
        arm_word_nf at count ⊢
        exact count)
  simp only [model, Side.count] at qCount qBuffer qChaining qLength
  let q := run drainFuel p
  have qCountWord : (r (.GPR 22#5) q).toNat = value.buffered.val := by
    arm_word_nf at qCount ⊢
    exact qCount
  have qSP : r (.GPR 31#5) q = r (.GPR 31#5) p := drained.sp
  have qNat : (r (.GPR 31#5) q).toNat = (r (.GPR 31#5) s).toNat - 304 := by rw [qSP, pNat]
  have qPhysical : (r (.GPR 31#5) q).toNat + 304 ≤ 2^64 := by rw [qSP]; exact physical
  have qProgram : q.program = s.program := drained.program.trans ready.program
  have qAligned : CheckSPAlignment q := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, qSP] using ready.aligned
  have qPC : read_pc q = base + 180#64 := by simpa only [Side.tailReturn] using drained.pc
  have qRegs (reg : BitVec 5) (lo : 19 ≤ reg.toNat) (hi : reg.toNat ≤ 29)
      (not22 : reg ≠ 22#5) (not23 : reg ≠ 23#5) (not25 : reg ≠ 25#5) :
      r (.GPR reg) q = r (.GPR reg) p :=
    drained.registers reg lo hi not22 not23 not25
  have q19 := (qRegs 19#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.x19
  have q20 := (qRegs 20#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.x20
  have q21 := (qRegs 21#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.x21
  have q24 : r (.GPR 24#5) q = r (.GPR 31#5) q :=
    ((qRegs 24#5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.x24).trans qSP.symm
  have q25 : r (.GPR 25#5) q = r (.GPR 31#5) q := (drained.leftBuffer rfl).trans qSP.symm
  have qFrame : MemoryFrame (combineWrites s) s q :=
    ready.frame.trans (frame_mono drained.frame contained)
  have qSaved : Saved s q := ready.saved.of_frame drained.frame physical
    (by
      right
      intro span member
      simp only [drainWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [stackSpan] <;> bv_omega)
    qSP
    (by intro reg lo hi; exact qRegs reg (by omega) (by omega) (by bv_omega) (by bv_omega) (by bv_omega))
    drained.vectors
  have localFrame := leftLength_frame q (by omega)
  have localContained : ∀ span ∈ [((r (.GPR 31#5) q).toNat + 96, 16)],
      ∃ outer ∈ combineWrites s,
        outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, qNat] <;> omega
  have frame : MemoryFrame (combineWrites s) s (leftLength q) :=
    qFrame.trans (frame_mono localFrame localContained)
  have saved : Saved s (leftLength q) := qSaved.of_frame localFrame qPhysical
    (by
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      bv_omega)
    (leftLength_register q 31#5 (by decide))
    (by intro reg lo hi; exact leftLength_register q reg (by bv_omega))
    (by intro reg lo hi; rw [leftLength_vector])
  have readonly (address bytes : Nat)
      (lo : (r (.GPR 31#5) q).toNat ≤ address)
      (hi : address + bytes ≤ (r (.GPR 31#5) q).toNat + 96) :
      Protected [((r (.GPR 31#5) q).toNat + 96, 16)] address bytes := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    omega
  have buffer : BytesAt (leftLength q) (r (.GPR 31#5) q) ⟨value.buffer.toArray⟩ :=
    bytesAt_frame localFrame (by rw [vectorByteArray_size]; omega)
      (by rw [vectorByteArray_size]; exact readonly _ _ (by omega) (by omega))
      (by simpa only [qSP] using qBuffer)
  have chaining : ChainingAt (leftLength q) (r (.GPR 31#5) q + 64#64) value.chaining :=
    (show ChainingAt q (r (.GPR 31#5) q + 64#64) value.chaining by
      simpa only [qSP] using qChaining).frame localFrame (by bv_omega)
      (readonly _ _ (by bv_omega) (by bv_omega))
  obtain ⟨storedCount, storedLength⟩ := leftLength_fields q (by omega)
  have rightWord : r (.GPR 4#5) s = BitVec.ofNat 64 right.size := by
    have length := owned.rightLength
    bv_omega
  have represented : StateAt (leftLength q) (r (.GPR 31#5) (leftLength q)) (leftValue left right) := by
    rw [leftLength_register q 31#5 (by decide)]
    refine ⟨buffer, chaining, ?_, ?_⟩
    · rw [storedCount]
      change r (.GPR 22#5) q = BitVec.ofNat 64 value.buffered.val
      simpa only [BitVec.ofNat_toNat] using congrArg (BitVec.ofNat 64) qCountWord
    · rw [storedLength, qSP, qLength, q20, rightWord]
      rfl
  have execution : run (prefixFuel + drainFuel + 4) s = leftLength q := by
    rw [run_plus, run_plus]
    exact leftLength_run q base (code.of_program_eq qProgram) drained.error qAligned qPC
  refine ⟨prefixFuel + drainFuel + 4, ?_⟩
  rw [execution]
  refine ⟨?_, (leftLength_error q).trans drained.error, (leftLength_program q).trans qProgram,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, saved, represented, frame,
    data.frame frame owned.initialOwned owned.roundsOwned⟩
  · rw [leftLength_pc q base qPC]
    have zero : r (.GPR 22#5) q = 0#64 ↔ value.buffered.val = 0 := by
      constructor
      · intro equal
        exact qCountWord.symm.trans (congrArg BitVec.toNat equal)
      · intro equal
        exact BitVec.eq_of_toNat_eq (qCountWord.trans equal)
    change (if r (.GPR 22#5) q = 0#64 then base + 308#64 else base + 196#64) =
      (if value.buffered.val = 0 then base + 308#64 else base + 196#64)
    simp only [zero]
  · simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      leftLength_register q 31#5 (by decide)] using qAligned
  · exact (leftLength_register q 31#5 (by decide)).trans (qSP.trans ready.sp)
  · exact (leftLength_register q 19#5 (by decide)).trans q19
  · exact (leftLength_register q 20#5 (by decide)).trans q20
  · exact (leftLength_register q 21#5 (by decide)).trans q21
  · simpa only [leftLength_register q 22#5 (by decide), leftValue] using qCountWord
  · rw [leftLength_register q 24#5 (by decide), leftLength_register q 31#5 (by decide)]
    exact q24
  · rw [leftLength_register q 25#5 (by decide), leftLength_register q 31#5 (by decide)]
    exact q25

end SszArm.Hash.Combine

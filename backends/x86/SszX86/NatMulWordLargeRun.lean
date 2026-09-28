import SszX86.NatMulWordLargeRunState
import SszX86.NatMulWordLargeLoop
import SszX86.NatMulWordTailCps
import SszX86.NatMulWordAllocatedReturn
import SszX86.NatMulWordLargeMemoryResources

namespace SszX86.NatMulWord
open SszNative UintCodec

private theorem mapped_fill (m : DataMem) (dst : BitVec 64) (index count : Nat)
    (words : List (BitVec 64)) (hm : Large.Mapped m dst count) :
    Large.Mapped (Large.fillMem m dst index words) dst count := by
  induction words generalizing m index with
  | nil => exact hm
  | cons limb limbs ih => exact ih _ _ (Large.mapped_store _ _ _ _ _ _ hm)

/-- Complete arbitrary-width helper multiplication from the real paired-loop
entry. Only the already executed first store is an input memory equality. -/
theorem large_run_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra) (r : Arena.Reservation)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor))
    (large : 1 < operand.wordCount)
    (work : WorkFrame s t.dmem (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (cursor : widthLoad t.dmem (s.regs.r8.toNat+16) 8 = some r.used)
    (outputMapped : OutputMapped t)
    (destinationMapped : Large.Mapped t.dmem (BitVec.ofNat 64 r.pointer) (8*(operand.wordCount+1)))
    (prefix : DataMem)
    (memory : t.dmem = Large.fillMem prefix (BitVec.ofNat 64 r.pointer) 0 [(firstResult operand factor).1])
    (registers : LargeLoopRegisters s t operand factor address r)
    (lowLoad : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some ((firstResult operand factor).1.toNat : Int))
    (startLoad : Mem.loadInt t.dmem (t.regs.rsp.toBitVec+8#64) 8 =
      some ((BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toNat : Int))
    (pointerGeometry : address+BitVec.ofNat 64 (Arena.start address.toNat used.toNat) = BitVec.ofNat 64 r.pointer) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base+466) := by
  have representation : ∃ source words, operand = NatOperand.large source words := by
    cases operand with
    | small limb =>
      have bound := Limbs.sigWords_le_length [limb]
      change 1 < Limbs.sigWords [limb] at large
      simp only [List.length_cons, List.length_nil] at bound
      omega
    | large source words => exact ⟨source, words, rfl⟩
  obtain ⟨source, words, rfl⟩ := representation
  let operand := NatOperand.large source words
  let dst := BitVec.ofNat 64 r.pointer
  let count := operand.wordCount
  let written := SszNative.NatMul.wordWritten operand factor
  let paired := pairedResult operand factor
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have pointerNat : dst.toNat = r.pointer := allocated_pointer_nat s operand factor address capacity used ra owned r allocated
  have writtenLength : written.length = count+1 := SszNative.NatMul.wordWritten_length operand factor
  have modelLength : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length = count+1 := by
    rw [model]
    exact writtenLength
  have span : dst.toNat+8*(count+1) ≤ 2^64 := by
    rw [pointerNat]
    simpa only [modelLength] using bounds.2.2.2.2.2
  have countBound : count+2 < 2^64 := by omega
  have geometry := unrolled_geometry count large
  have pairedLength : paired.1.length = 2*(count/2) := LimbMul.inner_length _ _ _ _ _
  have input := operand_preserved s operand factor address capacity used ra owned t.dmem
    (work.to_frame owned.stack_low)
  have apart : NatAdd.Carry.Apart operand dst (8*(count+1)) := by
    apply Body.apart_bytes
    · exact owned.operand_at.2.2.1
    · exact span
    · rw [pointerNat]
      have protected := owned.operand_owned.arena
      have usedBound := owned.used_bound
      rw [modelLength] at bounds
      unfold Body.Apart at *
      omega
  have finish (u : MachineData)
      (whole : u.dmem = Large.fillMem prefix dst 0 written)
      (buffer : NatMul.BufferFrame t.dmem u.dmem r.pointer
        (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length))
      (sp : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64)
      (out : u.regs.rdi = s.regs.rdi) (simd : u.zmms = s.zmms)
      (pointer : u.regs.r14.toBitVec = dst)
      (counter : u.regs.rbx.toBitVec = BitVec.ofNat 64 (count+2)) :
      Eventually (step e) (Post s operand factor address capacity used ra) (u, base+741) := by
    apply allocated_return_cps e base hc s u operand factor address capacity used ra owned r written model
      (work.buffer r allocated buffer)
    · rw [whole, ← pointerNat]
      exact Large.fill_wordsAt prefix dst written (by simpa only [writtenLength] using span)
    · rw [buffer_cursor_load s operand factor address capacity used ra owned r allocated _ _ buffer]
      exact cursor
    · exact sp
    · exact out
    · exact simd
    · unfold OutputMapped at outputMapped ⊢
      rw [out]
      apply buffer_output_mapped s operand factor address capacity used ra owned r allocated _ _ buffer
      simpa only [registers.output] using outputMapped
    · exact pointer
    · simpa only [writtenLength, Nat.add_assoc] using counter
    · have unchanged := buffer_stack_load s operand factor address capacity used ra owned r allocated _ _ buffer 0 8 (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at unchanged
      rw [sp, unchanged, ← registers.sp, lowLoad]
      simp only [written, word_written_first, List.getElem?_cons_zero, Option.getD_some]
  apply pairs_cps e base hc source dst factor words (count+1) (by omega) apart
    (Post s operand factor address capacity used ra) (count/2) (by omega) 1 (by decide) (by omega)
    t (firstResult operand factor).2 (LimbMul.step_carry_lt _ _ _ _ (by decide))
    registers.input registers.payload registers.factorReg registers.destination
    (by simpa only [Nat.add_sub_cancel_left] using registers.paired)
    registers.index registers.carry input destinationMapped
  intro u stable pairMemory pairIndex _ pairCarry
  have pairMemory' : u.dmem = Large.fillMem t.dmem dst 1 paired.1 := pairMemory
  have pairFrame : NatMul.BufferFrame t.dmem u.dmem r.pointer
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length) := by
    rw [pairMemory', modelLength, ← pointerNat]
    exact NatMul.fill_buffer_frame _ _ _ _ _ span (by rw [pairedLength]; omega)
  have pairFull : u.dmem = Large.fillMem prefix dst 0 ((firstResult operand factor).1 :: paired.1) := by
    rw [pairMemory', memory]
    rfl
  have pairMapped : Large.Mapped u.dmem dst (8*(count+1)) := by
    rw [pairMemory']
    exact mapped_fill _ _ _ _ _ destinationMapped
  have pairInput := operand_preserved s operand factor address capacity used ra owned u.dmem
    ((work.buffer r allocated pairFrame).to_frame owned.stack_low)
  have pairStart : Mem.loadInt u.dmem (u.regs.rsp.toBitVec+8#64) 8 =
      some ((BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toNat : Int) := by
    have unchanged := buffer_stack_load s operand factor address capacity used ra owned r allocated _ _ pairFrame 8 8 (by decide)
    rw [← registers.sp] at unchanged
    simpa only [stable.rsp] using unchanged.trans startLoad
  apply Tail.index_cps e base hc u
  intro indexFlags
  apply Tail.pointer_cps e base hc _ (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)) pairStart
  intro pointerFlags
  let v := Tail.pointerState (Tail.indexState u indexFlags)
    (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)) pointerFlags
  have vMemory : v.dmem = u.dmem := rfl
  have vPointer : v.regs.r14.toBitVec = dst := by
    simpa only [v, Tail.pointerState, Tail.indexState, UInt64.toBitVec_ofBitVec,
      stable.r14, registers.arenaBase] using pointerGeometry
  have vIndex : v.regs.r8.toBitVec = BitVec.ofNat 64 (1+2*(count/2)) := by
    simp only [v, Tail.pointerState, Tail.indexState, UInt64.toBitVec_ofBitVec, pairIndex]
    bv_omega
  have vParity : Tail.even v ↔ count%2 = 0 := by
    simpa only [Tail.even, v, Tail.pointerState, Tail.indexState, stable.r15, registers.count] using
      NatAdd.Carry.parity_test count
  have vSp : v.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64 := by
    simpa only [v, Tail.pointerState, Tail.indexState, stable.rsp] using registers.sp
  have vOut : v.regs.rdi = s.regs.rdi := stable.rdi.trans registers.output
  have vSimd : v.zmms = s.zmms := stable.zmms.trans registers.simd
  have vCounter : v.regs.rbx.toBitVec = BitVec.ofNat 64 (count+2) := by
    simpa only [v, Tail.pointerState, Tail.indexState, stable.rbx] using registers.counter
  have vCarry : v.regs.r10.toBitVec = BitVec.ofNat 64 paired.2 := pairCarry
  apply Tail.finish_cps e base hc v
  · intro odd inside
    have oddCount : count%2 ≠ 0 := fun h => odd (vParity.mpr h)
    have index : 1+2*(count/2) = count := by omega
    have indexNat : v.regs.r8.toNat = count := by
      change v.regs.r8.toBitVec.toNat = count
      rw [vIndex, index]
      exact Nat.mod_eq_of_lt (by omega)
    have lengthBound : words.length < 2^64 := by have := input.2.2.1; omega
    have lengthNat : v.regs.r9.toNat = words.length := by
      change v.regs.r9.toBitVec.toNat = words.length
      change u.regs.r9.toBitVec.toNat = words.length
      rw [stable.r9, registers.payload]
      exact Nat.mod_eq_of_lt lengthBound
    have loaded := (source_word u.dmem source words count pairInput).1 (by omega)
    have zero := final_input_zero operand
    change (words[count]?.getD 0) = 0 at zero
    rw [zero] at loaded
    simpa only [vMemory, vIndex, index, v, Tail.pointerState, Tail.indexState,
      stable.rsi, registers.input, show (0 : BitVec 64).toNat = 0 by rfl] using loaded
  · intro odd
    have oddCount : count%2 ≠ 0 := fun h => odd (vParity.mpr h)
    have index : 1+2*(count/2) = count := by omega
    have addressEq : Tail.address v = dst+BitVec.ofNat 64 (8*count) := by
      simp only [Tail.address, vPointer, vIndex, index, BitVec.ofNat_mul, Nat.mul_comm]
    rw [addressEq]
    exact Delimited.Reservation.mapped_subrange u.dmem dst (8*(count+1)) (8*count) 8 pairMapped (by omega)
  · intro even flags
    have evenCount := vParity.mp even
    apply finish {v with status := flags}
    · simpa only [written, word_written_pairs, evenCount, ↓reduceIte, List.append_nil, vMemory] using pairFull
    · exact pairFrame
    · exact vSp
    · exact vOut
    · exact vSimd
    · exact vPointer
    · exact vCounter
  · intro odd flags
    have oddCount : count%2 ≠ 0 := fun h => odd (vParity.mpr h)
    have index : 1+2*(count/2) = count := by omega
    have addressEq : Tail.address v = dst+BitVec.ofNat 64 (8*count) := by
      simp only [Tail.address, vPointer, vIndex, index, BitVec.ofNat_mul, Nat.mul_comm]
    have storedMemory : (Tail.storedState v flags).dmem =
        Large.fillMem u.dmem dst count [BitVec.ofNat 64 paired.2] := by
      simp only [Tail.storedState, addressEq, vMemory, vCarry, Large.fillMem]
    have lastFrame : NatMul.BufferFrame u.dmem (Tail.storedState v flags).dmem r.pointer
        (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length) := by
      rw [storedMemory, modelLength, ← pointerNat]
      exact NatMul.fill_buffer_frame _ _ _ _ _ span (by simp; omega)
    apply finish (Tail.storedState v flags)
    · rw [storedMemory, pairFull]
      rw [written, word_written_pairs, if_neg oddCount, ← List.cons_append, NatAdd.Carry.fill_append]
      simp only [List.length_cons, pairedLength, Nat.zero_add]
      rw [index]
    · exact pairFrame.trans lastFrame
    · exact vSp
    · exact vOut
    · exact vSimd
    · exact vPointer
    · exact vCounter

end SszX86.NatMulWord

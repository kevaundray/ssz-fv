import SszX86.NatMulWordLargeMemoryInitializedState

namespace SszX86.NatMulWord.LargeMemory
open SszNative UintCodec

structure Initialized (original : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (r : Arena.Reservation) (m : DataMem) : Prop where
  memory : m = Large.fillMem (prefixMem original operand factor address used r)
    (BitVec.ofNat 64 r.pointer) 0 [low operand factor]
  work : WorkFrame original m (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad m (original.regs.r8.toNat+16) 8 =
    some (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).used
  operand_at : operand.At (widthLoad m)
  output_mapped : Large.Mapped m original.regs.rdi.toBitVec 72
  free_mapped : Large.Mapped m (address+used) (capacity.toNat-used.toNat)
  destination_mapped : Large.Mapped m (BitVec.ofNat 64 r.pointer) (8*(operand.wordCount+1))
  locals_mapped : Large.Mapped m (original.regs.rsp.toBitVec-64) 16
  low_load : Mem.loadInt m (original.regs.rsp.toBitVec-64) 8 = some ((low operand factor).toNat : Int)
  start_load : Mem.loadInt m ((original.regs.rsp.toBitVec-64)+8#64) 8 = some (Arena.start address.toNat used.toNat : Int)
  first_limb : widthLoad m r.pointer 8 = some (low operand factor).toNat

theorem prefix_fill_mapped (original : MachineData) (operand : NatOperand)
    (factor address used : BitVec 64) (r : Arena.Reservation) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped (pushedMem original) p n) :
    Large.Mapped (Large.fillMem (prefixMem original operand factor address used r)
      (BitVec.ofNat 64 r.pointer) 0 [low operand factor]) p n := by
  unfold Large.fillMem prefixMem
  apply Large.mapped_store
  apply Large.mapped_store
  apply Large.mapped_store
  exact Large.mapped_store _ _ _ _ _ _ hm

/-- The entire mapped suffix is retained; only its first product word has been
initialized at this cut. Remaining destination values are never assumed. -/
theorem initialized (original current : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned original operand factor address capacity used ra)
    (ready : MultiplyReady original current operand factor)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor))
    (guardFlags mulFlags : StatusFlags) :
    Initialized original operand factor address capacity used r
      (state current operand address used guardFlags mulFlags).dmem := by
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have length : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length =
      operand.wordCount+1 := by
    rw [model]
    exact SszNative.NatMul.wordWritten_length operand factor
  have bounds := allocation_bounds original operand factor address capacity used ra owned r allocated
  have pointerNat := allocated_pointer_nat original operand factor address capacity used ra owned r allocated
  have checks := ((Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved).1
  have usedNat : (BitVec.ofNat 64 r.used).toNat = r.used := Nat.mod_eq_of_lt (by
    have fit := bounds.2.2.2.2.1
    have capacityBound := capacity.isLt
    omega)
  have startNat : (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toNat = Arena.start address.toNat used.toNat :=
    Nat.mod_eq_of_lt checks.2.2.2.1
  have memory := state_memory original current operand factor address capacity used ready r reserved guardFlags mulFlags
  have cursorWork := cursor_work original current operand factor address capacity used ra owned ready r reserved model guardFlags
  rw [cursor_memory original current operand factor address capacity used ready r reserved guardFlags] at cursorWork
  have lowWork := cursorWork.store_local owned.stack_low 0 8 (by decide) (low operand factor).toInt
  simp only [BitVec.add_zero] at lowWork
  have prefixWork : WorkFrame original (prefixMem original operand factor address used r)
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) :=
    lowWork.store_local owned.stack_low 8 8 (by decide)
      (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toInt
  have buffer : NatMul.BufferFrame (prefixMem original operand factor address used r)
      (Large.fillMem (prefixMem original operand factor address used r) (BitVec.ofNat 64 r.pointer) 0 [low operand factor])
      r.pointer (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length) := by
    have written := NatMul.fill_buffer_frame (prefixMem original operand factor address used r)
      (BitVec.ofNat 64 r.pointer) 0
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length)
      [low operand factor] (by rw [pointerNat]; exact bounds.2.2.2.2.2) (by
        simp only [List.length_singleton, Nat.zero_add]
        rw [length]
        omega)
    simpa only [pointerNat] using written
  have work : WorkFrame original (state current operand address used guardFlags mulFlags).dmem
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) := by
    rw [memory]
    exact prefixWork.buffer r allocated buffer
  have mappedAfter (p : BitVec 64) (n : Nat) (hm : Large.Mapped (pushedMem original) p n) :
      Large.Mapped (state current operand address used guardFlags mulFlags).dmem p n := by
    rw [memory]
    exact prefix_fill_mapped original operand factor address used r p n hm
  have initialFree := pushed_mapped original _ _ owned.free_mapped
  have destination := large_destination_mapped original operand factor address capacity used ra owned
    (pushedMem original) initialFree r (SszNative.NatMul.wordWritten operand factor) model
  rw [SszNative.NatMul.wordWritten_length] at destination
  have initialLocals : Large.Mapped (pushedMem original) (original.regs.rsp.toBitVec-64) 16 := by
    intro i hi
    exact pushed_mapped original _ _ owned.stack_mapped i (by omega)
  let cursorMem := Mem.storeInt (pushedMem original) (original.regs.r8.toBitVec+16#64) 8 (BitVec.ofNat 64 r.used).toInt
  let lowMem := Mem.storeInt cursorMem (original.regs.rsp.toBitVec-64) 8 (low operand factor).toInt
  have cursorFirst : widthLoad cursorMem (original.regs.r8.toNat+16) 8 = some r.used := by
    have stored := Measure.Bits.stored_word_load (pushedMem original) (original.regs.r8.toBitVec+16#64) (BitVec.ofNat 64 r.used)
    change widthLoad cursorMem (original.regs.r8.toBitVec.toNat+16) 8 = some r.used
    simp only [widthLoad, width_address, cursorMem, stored, Option.map_some, Int.toNat_natCast, usedNat]
  have cursorLow := cursor_after_local original operand factor address capacity used ra owned cursorMem 0 8 (by decide)
    (low operand factor).toInt
  simp only [BitVec.add_zero] at cursorLow
  have cursorStart := cursor_after_local original operand factor address capacity used ra owned lowMem 8 8 (by decide)
    (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toInt
  have prefixCursor : widthLoad (prefixMem original operand factor address used r) (original.regs.r8.toNat+16) 8 = some r.used :=
    cursorStart.trans (cursorLow.trans cursorFirst)
  have lowStored := Measure.Bits.stored_word_load cursorMem (original.regs.rsp.toBitVec-64) (low operand factor)
  have lowUntouched := local_spill_load lowMem (original.regs.rsp.toBitVec-64) 0 8 (by decide) (by decide) (by decide)
    (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toInt
  simp only [BitVec.add_zero] at lowUntouched
  have prefixLow : Mem.loadInt (prefixMem original operand factor address used r) (original.regs.rsp.toBitVec-64) 8 =
      some ((low operand factor).toNat : Int) := lowUntouched.trans lowStored
  have prefixStart : Mem.loadInt (prefixMem original operand factor address used r) ((original.regs.rsp.toBitVec-64)+8#64) 8 =
      some (Arena.start address.toNat used.toNat : Int) := by
    have stored := Measure.Bits.stored_word_load lowMem ((original.regs.rsp.toBitVec-64)+8#64)
      (BitVec.ofNat 64 (Arena.start address.toNat used.toNat))
    simpa only [startNat] using stored
  refine ⟨memory, work, ?_, operand_preserved original operand factor address capacity used ra owned _
    (work.to_frame owned.stack_low), mappedAfter _ _ (pushed_mapped original _ _ owned.output_mapped),
    mappedAfter _ _ initialFree, mappedAfter _ _ destination, mappedAfter _ _ initialLocals, ?_, ?_, ?_⟩
  · rw [memory, allocation_cursor operand factor address capacity used r allocated]
    exact (buffer_cursor_load original operand factor address capacity used ra owned r allocated _ _ buffer).trans prefixCursor
  · rw [memory]
    have unchanged := buffer_stack_load original operand factor address capacity used ra owned r allocated _ _ buffer 0 8 (by decide)
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans prefixLow
  · rw [memory]
    exact (buffer_stack_load original operand factor address capacity used ra owned r allocated _ _ buffer 8 8 (by decide)).trans prefixStart
  · rw [memory]
    have written := Large.fill_wordsAt (prefixMem original operand factor address used r) (BitVec.ofNat 64 r.pointer)
      [low operand factor] (by
        rw [pointerNat]
        have finish := bounds.2.2.2.2.2
        rw [length] at finish
        simp only [List.length_singleton]
        omega)
    have first := written ⟨0, by decide⟩
    change widthLoad (Large.fillMem (prefixMem original operand factor address used r)
      (BitVec.ofNat 64 r.pointer) 0 [low operand factor]) (BitVec.ofNat 64 r.pointer).toNat 8 =
      some (low operand factor).toNat at first
    rwa [pointerNat] at first

end SszX86.NatMulWord.LargeMemory

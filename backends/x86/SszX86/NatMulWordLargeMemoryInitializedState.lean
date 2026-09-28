import SszX86.NatMulWordLargeMemoryResources
import SszX86.NatMulWordPrepared
import SszX86.NatMulWordReserveLarge
import SszX86.NatMulWordStartLarge

namespace SszX86.NatMulWord.LargeMemory
open SszNative UintCodec

abbrev low (operand : NatOperand) (factor : BitVec 64) : BitVec 64 :=
  (LimbMul.step factor (SszNative.NatMul.lowWord operand) 0 0).1

/-- The actual PC310 store, before the original multiply at PC314. -/
def cursorState (current : MachineData) (address used : BitVec 64) (flags : StatusFlags) : MachineData :=
  let reserved := LargeReservation.reservedState current address used flags
  {reserved with dmem := Mem.storeInt reserved.dmem (reserved.regs.r8.toBitVec+16#64) 8 reserved.regs.rax.toBitVec.toInt}

abbrev productState (current : MachineData) (operand : NatOperand) (address used : BitVec 64)
    (guardFlags mulFlags : StatusFlags) : MachineData :=
  initialProductState (cursorState current address used guardFlags) (SszNative.NatMul.lowWord operand) mulFlags

/-- Exact PC336 state after cursor commit, MUL, two spills, and destination[0]. -/
def state (current : MachineData) (operand : NatOperand) (address used : BitVec 64)
    (guardFlags mulFlags : StatusFlags) : MachineData :=
  let product := productState current operand address used guardFlags mulFlags
  {product with dmem := initialStores product}

/-- The three non-buffer stores preceding the first written product limb. -/
def prefixMem (original : MachineData) (operand : NatOperand) (factor address used : BitVec 64)
    (r : Arena.Reservation) : DataMem :=
  let m := Mem.storeInt (pushedMem original) (original.regs.r8.toBitVec+16#64) 8 (BitVec.ofNat 64 r.used).toInt
  let m := Mem.storeInt m (original.regs.rsp.toBitVec-64) 8 (low operand factor).toInt
  Mem.storeInt m ((original.regs.rsp.toBitVec-64)+8#64) 8
    (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toInt

theorem cursor_memory (original current : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (ready : MultiplyReady original current operand factor)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (flags : StatusFlags) :
    (cursorState current address used flags).dmem =
      Mem.storeInt (pushedMem original) (original.regs.r8.toBitVec+16#64) 8 (BitVec.ofNat 64 r.used).toInt := by
  obtain ⟨checks, geometry⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved
  have countBound : operand.wordCount < 2^64 := by have := checks.1; omega
  have countNat : current.regs.r15.toNat = operand.wordCount := by
    change current.regs.r15.toBitVec.toNat = operand.wordCount
    rw [ready.count]
    exact Nat.mod_eq_of_lt countBound
  have finish : BitVec.ofNat 64 (Arena.start address.toNat used.toNat+8*(current.regs.r15.toNat+1)) =
      BitVec.ofNat 64 r.used := by
    rw [countNat, geometry]
    rfl
  change Mem.storeInt current.dmem (current.regs.r8.toBitVec+16#64) 8
    (BitVec.ofNat 64 (Arena.start address.toNat used.toNat+8*(current.regs.r15.toNat+1))).toInt = _
  rw [ready.memory, ready.arena, finish]

theorem state_memory (original current : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (ready : MultiplyReady original current operand factor)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (guardFlags mulFlags : StatusFlags) :
    (state current operand address used guardFlags mulFlags).dmem =
      Large.fillMem (prefixMem original operand factor address used r) (BitVec.ofNat 64 r.pointer) 0
        [low operand factor] := by
  have cursor := cursor_memory original current operand factor address capacity used ready r reserved guardFlags
  have multiply : factor * SszNative.NatMul.lowWord operand = low operand factor := by
    simpa only [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero] using
      (word_carry_step factor (SszNative.NatMul.lowWord operand) 0 (by decide)).1
  have productLow : (productState current operand address used guardFlags mulFlags).regs.rax.toBitVec = low operand factor := by
    change current.regs.rcx.toBitVec * SszNative.NatMul.lowWord operand = low operand factor
    rw [ready.factorReg]
    exact multiply
  have productSP : (productState current operand address used guardFlags mulFlags).regs.rsp.toBitVec =
      original.regs.rsp.toBitVec-64 := ready.sp
  have productStart : (productState current operand address used guardFlags mulFlags).regs.r13.toBitVec =
      BitVec.ofNat 64 (Arena.start address.toNat used.toNat) := by
    change (UInt64.ofNat (Arena.start address.toNat used.toNat)).toBitVec = _
    exact UInt64.toBitVec_ofNat' _
  have geometry := ((Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved).2
  have productDestination :
      (productState current operand address used guardFlags mulFlags).regs.r14.toBitVec +
        (productState current operand address used guardFlags mulFlags).regs.r13.toBitVec = BitVec.ofNat 64 r.pointer := by
    change address + (UInt64.ofNat (Arena.start address.toNat used.toNat)).toBitVec = _
    rw [UInt64.toBitVec_ofNat', geometry]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change initialStores (productState current operand address used guardFlags mulFlags) = _
  unfold initialStores
  rw [productSP, productLow, productDestination, productStart]
  change Mem.storeInt (Mem.storeInt (Mem.storeInt (cursorState current address used guardFlags).dmem
    (original.regs.rsp.toBitVec-64) 8 (low operand factor).toInt)
    ((original.regs.rsp.toBitVec-64)+8#64) 8 (BitVec.ofNat 64 (Arena.start address.toNat used.toNat)).toInt)
    (BitVec.ofNat 64 r.pointer) 8 (low operand factor).toInt = _
  rw [cursor]
  simp only [prefixMem, Large.fillMem, Nat.mul_zero, BitVec.add_zero]

theorem cursor_work (original current : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned original operand factor address capacity used ra)
    (ready : MultiplyReady original current operand factor) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor)) (flags : StatusFlags) :
    WorkFrame original (cursorState current address used flags).dmem
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) := by
  rw [cursor_memory original current operand factor address capacity used ready r reserved flags]
  apply (WorkFrame.initial original _).store_cursor r
  · rw [model]
    rfl
  · exact owned.header_bound

theorem cursor_mapped (original current : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (ready : MultiplyReady original current operand factor)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (flags : StatusFlags) (p : BitVec 64) (n : Nat) (hm : Large.Mapped (pushedMem original) p n) :
    Large.Mapped (cursorState current address used flags).dmem p n := by
  rw [cursor_memory original current operand factor address capacity used ready r reserved flags]
  exact Large.mapped_store _ _ _ _ _ _ hm

theorem cursor_operand_at (original current : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned original operand factor address capacity used ra)
    (ready : MultiplyReady original current operand factor) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor)) (flags : StatusFlags) :
    operand.At (widthLoad (cursorState current address used flags).dmem) :=
  operand_preserved original operand factor address capacity used ra owned _
    ((cursor_work original current operand factor address capacity used ra owned ready r reserved model flags).to_frame owned.stack_low)

theorem large_low_load (m : DataMem) (operand : NatOperand) (large : 1 < operand.wordCount)
    (stored : operand.At (widthLoad m)) :
    Mem.loadInt m operand.pointer 8 = some ((SszNative.NatMul.lowWord operand).toNat : Int) := by
  cases operand with
  | small limb =>
    have count := Limbs.sigWords_le_length [limb]
    change 1 < Limbs.sigWords [limb] at large
    simp only [List.length_cons, List.length_nil] at count
    omega
  | large pointer words =>
    have count := Limbs.sigWords_le_length words
    change 1 < Limbs.sigWords words at large
    have positive : 0 < words.length := by omega
    have loaded := widthLoad_eq m _ _ _ (stored.2.2.2 ⟨0, positive⟩)
    change Mem.loadInt m pointer 8 = some ((words[0]?.getD 0).toNat : Int)
    simpa only [Nat.mul_zero, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Fin.getElem_fin, List.getElem?_eq_getElem positive, Option.getD_some] using loaded

theorem cursor_low_load (original current : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned original operand factor address capacity used ra)
    (ready : MultiplyReady original current operand factor) (large : 1 < operand.wordCount)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor))
    (flags : StatusFlags) :
    Mem.loadInt (cursorState current address used flags).dmem
      (cursorState current address used flags).regs.rsi.toBitVec 8 =
      some ((SszNative.NatMul.lowWord operand).toNat : Int) := by
  change Mem.loadInt (cursorState current address used flags).dmem current.regs.rsi.toBitVec 8 = _
  rw [ready.input]
  exact large_low_load _ operand large
    (cursor_operand_at original current operand factor address capacity used ra owned ready r reserved model flags)

end SszX86.NatMulWord.LargeMemory

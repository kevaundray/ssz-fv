import SszX86.NatMulWordLargeStart
import SszX86.NatMulWordLargeMemoryInitialized

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem large_start_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s current : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (ready : MultiplyReady s current operand factor) (large : 1 < operand.wordCount)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat (operand.wordCount+1) = some r)
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatMul.wordWritten operand factor))
    (guardFlags : StatusFlags) (P : MachineState → Prop)
    (next : ∀ mulFlags loopFlags,
      let t := loopStartState (LargeMemory.state current operand address used guardFlags mulFlags) loopFlags
      LargeMemory.Initialized s operand factor address capacity used r t.dmem →
      LargeLoopRegisters s t operand factor address r →
      Eventually (step e) P (t, base+466)) :
    Eventually (step e) P (LargeReservation.reservedState current address used guardFlags, base+310) := by
  have header := pushed_header s operand factor address capacity used ra owned
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have physical : operand.words.length+1 < 2^64 := by
    cases operand with
    | small limb => decide
    | large pointer words => have := owned.operand_at.2.2.1; change words.length+1 < 2^64; omega
  have localMapped : Large.Mapped (pushedMem s) (s.regs.rsp.toBitVec-64) 16 := by
    intro i hi
    exact pushed_mapped s _ _ owned.stack_mapped i (by omega)
  have destinationMapped := allocated_mapped s operand factor address capacity used ra owned (pushedMem s)
    (pushed_mapped s _ _ owned.free_mapped) r allocated
  have destinationFirst : Large.Mapped (pushedMem s) (BitVec.ofNat 64 r.pointer) 8 := by
    have sub := Delimited.Reservation.mapped_subrange (pushedMem s) (BitVec.ofNat 64 r.pointer)
      (8*(SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written.length)
      0 8 destinationMapped (by rw [model, SszNative.NatMul.wordWritten_length]; omega)
    simpa only [BitVec.add_zero] using sub
  apply commit_cursor_cps e base hc
  · exact ⟨used.toNat, by simpa only [LargeReservation.reservedState, ready.memory, ready.arena] using header.2.2⟩
  apply initial_product_cps e base hc (LargeMemory.cursorState current address used guardFlags)
    (SszNative.NatMul.lowWord operand)
    (LargeMemory.cursor_low_load s current operand factor address capacity used ra owned ready large r reserved model guardFlags)
  intro mulFlags
  have initialized := LargeMemory.initialized s current operand factor address capacity used ra owned ready r reserved model guardFlags mulFlags
  apply initial_stores_cps e base hc
  · have transported := LargeMemory.cursor_mapped s current operand factor address capacity used ready r reserved guardFlags _ _ localMapped
    simpa only [LargeMemory.productState, initialProductState, ready.sp] using transported
  · have transported := LargeMemory.cursor_mapped s current operand factor address capacity used ready r reserved guardFlags _ _ destinationFirst
    have geometry := ((Arena.reserve_eq_some_iff_checks _ _ _ _ (by omega) r).mp reserved).2
    have pointer : (LargeMemory.productState current operand address used guardFlags mulFlags).regs.r14.toBitVec+
        (LargeMemory.productState current operand address used guardFlags mulFlags).regs.r13.toBitVec = BitVec.ofNat 64 r.pointer := by
      change address+(UInt64.ofNat (Arena.start address.toNat used.toNat)).toBitVec = _
      rw [UInt64.toBitVec_ofNat', geometry]
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simpa only [pointer] using transported
  apply start_loop_cps e base hc _ (large_loop_many s current operand factor address used ready large physical guardFlags mulFlags)
  intro loopFlags
  exact next mulFlags loopFlags initialized
    (large_loop_registers s current operand factor address capacity used ready r reserved guardFlags mulFlags loopFlags)

end SszX86.NatMulWord

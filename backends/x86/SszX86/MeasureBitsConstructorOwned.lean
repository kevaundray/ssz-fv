import SszX86.MeasureBitsMapped
import SszX86.MeasureBitsLoads
import SszX86.MeasureBitsCalls
import SszX86.NatFromU128Proofs

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

private theorem return_slot_address (position : BitVec 64) (off : Nat) :
    position - 8 + BitVec.ofNat 64 off = position - 16 + BitVec.ofNat 64 (8 + off) := by
  rw [BitVec.ofNat_add]
  bv_omega

/-- Ownership of the real CALL2114 is derived from the original activation and
current verified cursor/header. No helper-exit or future allocation is assumed. -/
theorem constructor_owned (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used current ra : BitVec 64) (wide : BitVec 128)
    (owned : BodyOwned s desc value buffer address capacity used)
    (mapping : MappedExtension s.dmem t.dmem)
    (header : ArenaAt t.dmem s.regs.rcx.toBitVec address capacity current)
    (monotone : used.toNat ≤ current.toNat)
    (currentRange : current.toNat = used.toNat ∨ current.toNat ≤ capacity.toNat)
    (sp : t.regs.rsp = s.regs.rsp)
    (headerReg : t.regs.rcx = s.regs.rcx)
    (outReg : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 24)
    (low : t.regs.rsi.toBitVec = wide.setWidth 64)
    (high : t.regs.rdx.toBitVec = (wide >>> 64).setWidth 64) :
    NatFromU128.Owned (callState t ra) wide address capacity current ra := by
  have stackLow := owned.stackLow
  have stackBound := owned.stackBound
  have stackHeader := body_stack_header_apart s desc value buffer address capacity used owned
  have returnNat : (t.regs.rsp.toBitVec - 8).toNat = s.regs.rsp.toNat - 8 := by
    rw [sp, ← UInt64.toNat_toBitVec]
    rw [← UInt64.toNat_toBitVec] at stackLow
    bv_omega
  have outputNat : t.regs.rdi.toNat = s.regs.rsp.toNat + 24 := by
    rw [← UInt64.toNat_toBitVec, outReg, ← UInt64.toNat_toBitVec]
    rw [← UInt64.toNat_toBitVec] at stackBound
    bv_omega
  have cursorTail : current.toNat - used.toNat + (capacity.toNat - current.toNat) ≤
      capacity.toNat - used.toNat := by
    rcases currentRange with same | within <;> omega
  have freeMapped := Delimited.Reservation.mapped_subrange s.dmem (address + used)
    (capacity.toNat - used.toNat) (current.toNat - used.toNat)
    (capacity.toNat - current.toNat) owned.freeMapped cursorTail
  have freeAddress : address + used + BitVec.ofNat 64 (current.toNat - used.toNat) =
      address + current := by bv_omega
  rw [freeAddress] at freeMapped
  have headerReads := arena_loads t.dmem s.regs.rcx.toBitVec address capacity current header
  have headerSafe : ∀ a, InSpan a s.regs.rcx.toBitVec 24 →
      ¬ InSpan a (t.regs.rsp.toBitVec - 8) 8 := by
    rintro a ⟨i, hi, rfl⟩ ⟨j, hj, equal⟩
    apply owned.headerStack i hi (8 + j) (by omega)
    rw [sp] at equal
    have addressEq : s.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j =
        s.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 (8 + j) :=
      return_slot_address s.regs.rsp.toBitVec j
    exact equal.trans addressEq
  have keep (off : Nat) (within : off + 8 ≤ 24) :
      Mem.loadInt (callState t ra).dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt t.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 off) 8 :=
    frame_load_window t.dmem (callState t ra).dmem _
      (store_frame t.dmem (t.regs.rsp.toBitVec - 8) 8 ra.toInt)
      s.regs.rcx.toBitVec off 8 24 within headerSafe
  have freeHeader := owned.freeHeader
  have freeStack := owned.freeStack
  refine {
    low := low
    high := high
    header := ⟨?_, ?_, ?_⟩
    arena_bound := owned.arenaBound
    arena_nonzero := owned.arenaNonzero
    free_mapped := ?_
    header_bound := ?_
    output_bound := ?_
    output_mapped := ?_
    return_bound := ?_
    return_load := ?_
    output_header := ?_
    output_return := ?_
    free_output := ?_
    free_header := ?_
    free_return := ?_
    cursor_return := ?_ }
  · simpa only [callState, headerReg, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (keep 0 (by decide)).trans (by simpa only [BitVec.add_zero] using headerReads.1)
  · simpa only [callState, headerReg] using (keep 8 (by decide)).trans headerReads.2.1
  · simpa only [callState, headerReg] using (keep 16 (by decide)).trans headerReads.2.2
  · exact Large.mapped_store _ _ _ _ _ _ (mapping _ _ freeMapped)
  · simpa only [callState, headerReg] using owned.headerBound
  · dsimp only [callState]
    rw [outputNat]
    omega
  · dsimp only [NatFromU128.OutputMapped, callState]
    rw [outReg]
    exact Large.mapped_store _ _ _ _ _ _
      (mapping _ _ (body_work_mapped s desc value buffer address capacity used owned 24 68 (by decide)))
  · dsimp only [callState]
    rw [UInt64.toNat_ofBitVec, returnNat]
    omega
  · exact Delimited.stored_return_load t.dmem (t.regs.rsp.toBitVec - 8) ra
  · dsimp only [callState]
    rw [outputNat, headerReg]
    unfold Body.Apart at stackHeader ⊢
    omega
  · dsimp only [callState]
    rw [outputNat]
    change Body.Apart (s.regs.rsp.toNat + 24) 68 (t.regs.rsp.toBitVec - 8).toNat 8
    rw [returnNat]
    unfold Body.Apart
    omega
  · dsimp only [callState]
    rw [outputNat]
    unfold Body.Apart at freeStack ⊢
    rcases currentRange with same | within <;> omega
  · dsimp only [callState]
    rw [headerReg]
    unfold Body.Apart at freeHeader ⊢
    rcases currentRange with same | within <;> omega
  · dsimp only [callState]
    rw [UInt64.toNat_ofBitVec, returnNat]
    unfold Body.Apart at freeStack ⊢
    rcases currentRange with same | within <;> omega
  · dsimp only [callState]
    rw [headerReg]
    change Body.Apart (s.regs.rcx.toNat + 16) 8 (t.regs.rsp.toBitVec - 8).toNat 8
    rw [returnNat]
    unfold Body.Apart at stackHeader ⊢
    omega

/-- The CALL store itself is mapped by the existing sixteen-byte lowering
activation, not by an independently postulated helper stack. -/
theorem constructor_return_mapped (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (mapping : MappedExtension s.dmem t.dmem) (sp : t.regs.rsp = s.regs.rsp) :
    ∃ old, Mem.loadInt t.dmem (t.regs.rsp.toBitVec - 8) 8 = some old := by
  have hm := mapping _ _ owned.localMapped
  have result := Large.mapped_load t.dmem (s.regs.rsp.toBitVec - 16) 232 8 8 hm (by decide)
  have same : s.regs.rsp.toBitVec - 16 + 8#64 = s.regs.rsp.toBitVec - 8 := by bv_omega
  simpa only [sp, same] using result

end SszX86.Measure.Bits

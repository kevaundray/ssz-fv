import SszX86.NatMulReservePost

namespace SszX86.NatMul.Reservation
open UintCodec

private theorem stack_disjoint (sp : BitVec 64) (a b : Nat)
    (ha : a + 8 ≤ 40) (hb : b + 8 ≤ 40) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
    Large.Disjoint (sp + BitVec.ofNat 64 a) (sp + BitVec.ofNat 64 b) 8 8 := by
  intro i hi j hj
  bv_omega

private theorem cursor_disjoint (s : MachineData) (offset : Nat) (inside : offset + 8 ≤ 40)
    (apart : Large.Disjoint s.regs.rsp.toBitVec (s.regs.r9.toBitVec + 16#64) 40 8) :
    Large.Disjoint (s.regs.rsp.toBitVec + BitVec.ofNat 64 offset)
      (s.regs.r9.toBitVec + 16#64) 8 8 := by
  intro i hi j hj
  simpa only [memmove_addr_add] using apart (offset + i) (by omega) j hj

/-- Each local spill is observed after all five actual stores. Values are
established from the original registers, not hypotheses on initialized memory. -/
theorem prepared_spills (s : MachineData)
    (apart : Large.Disjoint s.regs.rsp.toBitVec (s.regs.r9.toBitVec + 16#64) 40 8) :
    Mem.loadInt (preparedMem s) s.regs.rsp.toBitVec 8 = some (s.regs.rax.toNat : Int) ∧
    Mem.loadInt (preparedMem s) (s.regs.rsp.toBitVec + 16#64) 8 = some (s.regs.rsi.toNat : Int) ∧
    Mem.loadInt (preparedMem s) (s.regs.rsp.toBitVec + 24#64) 8 = some (s.regs.rdi.toNat : Int) ∧
    Mem.loadInt (preparedMem s) (s.regs.rsp.toBitVec + 32#64) 8 = some (s.regs.rcx.toNat : Int) := by
  have apart0 (off : Nat) (lo : 8 ≤ off) (hi : off + 8 ≤ 40) :
      Large.Disjoint (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) s.regs.rsp.toBitVec 8 8 := by
    simpa using stack_disjoint s.regs.rsp.toBitVec off 0 hi (by decide) (Or.inr lo)
  have apart16_32 := stack_disjoint s.regs.rsp.toBitVec 16 32 (by decide) (by decide) (by decide)
  have apart24_32 := stack_disjoint s.regs.rsp.toBitVec 24 32 (by decide) (by decide) (by decide)
  have apart24_16 := stack_disjoint s.regs.rsp.toBitVec 24 16 (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Measure.Bits.stored_word_load _ _ _
  · unfold preparedMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (apart0 16 (by decide) (by decide)),
      BoolCodec.load_store_disjoint _ _ _ _ _ _ apart16_32]
    exact Measure.Bits.stored_word_load _ _ _
  · unfold preparedMem cursorMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (apart0 24 (by decide) (by decide)),
      BoolCodec.load_store_disjoint _ _ _ _ _ _ apart24_32,
      BoolCodec.load_store_disjoint _ _ _ _ _ _ apart24_16,
      BoolCodec.load_store_disjoint _ _ _ _ _ _ (cursor_disjoint s 24 (by decide) apart)]
    exact Measure.Bits.stored_word_load _ _ _
  · unfold preparedMem
    rw [BoolCodec.load_store_disjoint _ _ _ _ _ _ (apart0 32 (by decide) (by decide))]
    exact Measure.Bits.stored_word_load _ _ _

/-- The helper's buffer writes and its pushed return slot preserve every local
word in the caller's forty-byte frame. -/
theorem helper_stack_load (s : MachineData) (ra : BitVec 64) (n : Nat) (t : MachineState)
    (post : MemsetCall.Post s ra n t) (offset : Nat) (inside : offset + 8 ≤ 40)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rdi.toBitVec 40 n) :
    Mem.loadInt t.1.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 offset) 8 =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 offset) 8 := by
  apply memmove_loadInt_congr
  intro i hi
  apply post.frame
  rintro (⟨j, hj, equal⟩ | ⟨j, hj, equal⟩)
  · have sep := apart (offset + i) (by omega) j hj
    apply sep
    simpa only [memmove_addr_add] using equal
  · bv_omega

end SszX86.NatMul.Reservation

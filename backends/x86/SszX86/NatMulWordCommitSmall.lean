import SszX86.NatMulWordReserveSmall
import SszX86.NatMulWordOutput

namespace SszX86.NatMulWord
open UintCodec

abbrev commitMem := NatFromU128.commitMem

def smallCommitted (s : MachineData) : MachineData :=
  {s with
    dmem := commitMem s.dmem s.regs.r8.toBitVec
      (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec) s.regs.r9.toBitVec
      s.regs.rax.toBitVec s.regs.rdx.toBitVec
    regs := {s.regs with r8 := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec)}}

/-- The real cursor store precedes both result limbs; the alignment padding is
never stored, and the original low/high product registers supply the bytes. -/
theorem commit_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some old)
    (payload : Large.Mapped s.dmem (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (smallCommitted s, base + 597)) :
    Eventually (step e) P (s, base + 580) := by
  natmulword_step 4:29 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact header
  simp only [Effects.All]
  natmulword_step 4:30 using hc
  natmulword_step 4:31 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  natmulword_step 5:0 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Large.mapped_load
      (dst := s.regs.rcx.toBitVec + s.regs.rsi.toBitVec)
      (capacity := 16) (offset := 8) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  simpa [smallCommitted, commitMem, NatFromU128.commitMem, BitVec.add_assoc] using next

theorem small_allocated_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec s.regs.r8.toBitVec 2}, base + 687)) :
    Eventually (step e) P (s, base + 597) := by
  natmulword_output 5:1 at 0 width 8 using hc mapped hm
  natmulword_output 5:2 at 8 width 8 using hc mapped hm
  natmulword_output 5:3 at 64 width 4 using hc mapped hm
  natmulword_step 5:4 using hc
  simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using next

theorem small_inline_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec 0 s.regs.rax.toBitVec}, base + 687)) :
    Eventually (step e) P (s, base + 407) := by
  natmulword_output 3:10 at 0 width 8 using hc mapped hm
  natmulword_output 3:11 at 8 width 8 using hc mapped hm
  natmulword_output 3:12 at 64 width 4 using hc mapped hm
  natmulword_step 3:13 using hc
  simpa [successMem, NatAdd.successMem, NatAdd.pairMem] using next

end SszX86.NatMulWord

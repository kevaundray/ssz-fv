import SszX86.NatMulWordNormalizePhase
import SszX86.NatMulWordLargeMemoryFinish

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- The full allocation is scanned without rewriting it; the exact native pair
is published and the original saved registers and caller RET slot are restored.
All result and input ownership follows from the initial Owned and write frame. -/
theorem allocated_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation) (words : List (BitVec 64))
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r words)
    (work : WorkFrame s t.dmem (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (written : NatMemory.wordsAt (widthLoad t.dmem) r.pointer words)
    (cursor : widthLoad t.dmem (s.regs.r8.toNat+16) 8 = some r.used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64)
    (output : t.regs.rdi = s.regs.rdi) (simd : t.zmms = s.zmms)
    (hm : OutputMapped t)
    (pointer : t.regs.r14.toBitVec = BitVec.ofNat 64 r.pointer)
    (counter : t.regs.rbx.toBitVec = BitVec.ofNat 64 (words.length+1))
    (lowLoad : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some ((words[0]?.getD 0).toNat : Int)) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base+741) := by
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have exactPointer := allocated_pointer_nat s operand factor address capacity used ra owned r allocated
  have extent : r.pointer+8*words.length ≤ 2^64 := by
    simpa only [model, NatArithmetic.committed] using bounds.2.2.2.2.2
  have bound : words.length+1 < 2^64 := by omega
  have stored : NatMemory.wordsAt (widthLoad t.dmem) t.regs.r14.toNat words := by
    change NatMemory.wordsAt (widthLoad t.dmem) t.regs.r14.toBitVec.toNat words
    rw [pointer, exactPointer]
    exact written
  apply normalize_result_cps e base hc t words bound counter lowLoad stored
  intro u memory stack out vectors pairPointer pairPayload
  apply allocated_publish_cps e base hc u
  · unfold OutputMapped at hm ⊢
    rw [memory, out]
    exact hm
  apply finish_cps e base hc s _ operand factor address capacity used ra owned
  apply large_finished s operand factor address capacity used ra owned r words model
    t.dmem work written cursor
  · simp only [memory, out, output, pairPointer, pairPayload, pointer]
  · simpa only [stack] using sp
  · exact vectors.trans simd

end SszX86.NatMulWord

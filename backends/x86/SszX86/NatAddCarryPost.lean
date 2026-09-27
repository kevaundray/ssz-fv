import SszX86.NatAddCarryMath

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The caller-visible arrival facts before from_words starts at 1325. -/
structure Post (s : MachineData) (left right : NatOperand) (dst : BitVec 64)
    (t : MachineData) : Prop where
  count : t.regs.rax.toBitVec = BitVec.ofNat 64 (SszNative.NatAdd.count left right)
  pointer : t.regs.r10.toBitVec = dst
  first : t.regs.r9.toBitVec = (SszNative.NatAdd.writtenWords left right).head?.getD 0
  out : t.regs.rdi = s.regs.rdi
  sp : t.regs.rsp = s.regs.rsp
  simd : t.zmms = s.zmms
  written : NatMemory.wordsAt (widthLoad t.dmem) dst.toNat
    (SszNative.NatAdd.writtenWords left right)
  left_original : left.At (widthLoad t.dmem)
  right_original : right.At (widthLoad t.dmem)
  frame : ∀ a : BitVec 64,
    Body.Outside a.toNat dst.toNat (8*(SszNative.NatAdd.count left right+1)) →
      t.dmem.get? a = s.dmem.get? a

/-- The first store remains in R9 on both concrete loop shapes. -/
theorem written_first (left right : NatOperand) :
    (SszNative.NatAdd.writtenWords left right).head?.getD 0 =
      (LimbAdd.step (limbAt left.words 0) (limbAt right.words 0) 0).1 := by
  rw [SszNative.NatAdd.writtenWords_native_loop]
  simp only [LimbAdd.loop, List.head?_cons, Option.getD_some]
  simp only [List.head?_eq_getElem?, limbAt]

/-- Exact sequential writes imply all ownership and footprint arrival facts. -/
theorem post_of_fill (s t : MachineData) (left right : NatOperand) (dst : BitVec 64)
    (leftOwned : left.At (widthLoad s.dmem)) (rightOwned : right.At (widthLoad s.dmem))
    (leftApart : Apart left dst (8*(SszNative.NatAdd.count left right+1)))
    (rightApart : Apart right dst (8*(SszNative.NatAdd.count left right+1)))
    (bound : dst.toNat + 8*(SszNative.NatAdd.count left right+1) ≤ 2^64)
    (rax : t.regs.rax.toBitVec = BitVec.ofNat 64 (SszNative.NatAdd.count left right))
    (r10 : t.regs.r10.toBitVec = dst)
    (r9 : t.regs.r9.toBitVec =
      (LimbAdd.step (limbAt left.words 0) (limbAt right.words 0) 0).1)
    (rdi : t.regs.rdi = s.regs.rdi) (rsp : t.regs.rsp = s.regs.rsp)
    (simd : t.zmms = s.zmms)
    (memory : t.dmem = Large.fillMem s.dmem dst 0 (SszNative.NatAdd.writtenWords left right)) :
    Post s left right dst t := by
  refine ⟨rax, r10, r9.trans (written_first left right).symm, rdi, rsp, simd, ?_, ?_, ?_, ?_⟩
  · rw [memory]
    apply Large.fill_wordsAt
    simpa only [SszNative.NatAdd.writtenWords_length] using bound
  · rw [memory]
    apply fill_preserves s.dmem left dst 0 (8*(SszNative.NatAdd.count left right+1))
      _ leftOwned leftApart
    simp [SszNative.NatAdd.writtenWords_length]
  · rw [memory]
    apply fill_preserves s.dmem right dst 0 (8*(SszNative.NatAdd.count left right+1))
      _ rightOwned rightApart
    simp [SszNative.NatAdd.writtenWords_length]
  · intro a outside
    rw [memory]
    apply Large.fill_frame
    intro i lo hi
    apply Body.outside_byte dst a _ i bound outside
    simpa only [Nat.zero_add, SszNative.NatAdd.writtenWords_length] using hi

end SszX86.NatAdd.Carry

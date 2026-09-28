import SszX86.BitVectorWorldAllocation

namespace SszX86.BitVector
open SszNative UintCodec

theorem Protected.division {s u : MachineData} {address capacity used : BitVec 64} {p n : Nat}
    (owned : Protected s address capacity used p n)
    (low : 72 ≤ s.regs.rsp.toNat)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r8 = s.regs.rbx) : NatDivision.Protected u address capacity used p n := by
  refine ⟨owned.bound, ?_, ?_, ?_, owned.arena⟩
  · have apart := owned.work
    unfold Body.Apart workStart workSize at apart
    unfold Body.Apart
    omega
  · have apart := owned.work
    unfold Body.Apart workStart workSize at apart
    unfold Body.Apart
    omega
  · simpa only [arena] using owned.cursor

theorem Protected.add {s u : MachineData} {address capacity used : BitVec 64} {p n : Nat}
    (owned : Protected s address capacity used p n)
    (low : 72 ≤ s.regs.rsp.toNat)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r9 = s.regs.rbx) : NatAdd.Protected u address capacity used p n := by
  refine ⟨owned.bound, ?_, ?_, ?_, owned.arena⟩
  · have apart := owned.work
    unfold Body.Apart workStart workSize at apart
    unfold Body.Apart
    omega
  · have apart := owned.work
    unfold Body.Apart workStart workSize at apart
    unfold Body.Apart
    omega
  · simpa only [arena] using owned.cursor

/-- A later real addition preserves every earlier quotient word, even words
removed from the normalized quotient and even when addition returns an error. -/
theorem add_keeps_words (s u : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (owned : NatAdd.Owned u left right address capacity used ra)
    (low : 72 ≤ s.regs.rsp.toNat)
    (output : u.regs.rdi.toNat = s.regs.rsp.toNat + 16)
    (stack : u.regs.rsp.toNat = s.regs.rsp.toNat - 8)
    (arena : u.regs.r9 = s.regs.rbx)
    (t : MachineState) (post : NatAdd.Post u left right address capacity used ra t)
    (pointer : Nat) (words : List (BitVec 64))
    (protectedSpan : Protected s address capacity used pointer (8 * words.length))
    (stored : NatMemory.wordsAt (widthLoad u.dmem) pointer words) :
    NatMemory.wordsAt (widthLoad t.1.dmem) pointer words := by
  intro i
  rw [NatAdd.preserves_load u left right address capacity used ra owned t.1.dmem post.frame
    pointer (8 * words.length) (8 * i.val) 8 (protectedSpan.add low output stack arena)
    (by have := i.isLt; omega)]
  exact stored i

end SszX86.BitVector

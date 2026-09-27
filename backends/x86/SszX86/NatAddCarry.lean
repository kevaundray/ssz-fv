import SszX86.NatAddCarryLarge
import SszX86.NatAddCarrySmall

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The complete actual allocating addition-loop phase, from the pointer dispatch
at 536 to arrival at 1325 before from_words. Both immutable operands retain their
original physical representation and may alias each other. The only separation
is against the exact newly allocated output interval. The mask premise is needed
only by the Small-left paired loop; the allocator installs it at instruction 414. -/
theorem carry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand) (dst : BitVec 64)
    (leftOwned : left.At (widthLoad s.dmem)) (rightOwned : right.At (widthLoad s.dmem))
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (wide : 2 ≤ SszNative.NatAdd.count left right)
    (hm : Large.Mapped s.dmem dst (8*(SszNative.NatAdd.count left right+1)))
    (leftApart : Carry.Apart left dst (8*(SszNative.NatAdd.count left right+1)))
    (rightApart : Carry.Apart right dst (8*(SszNative.NatAdd.count left right+1)))
    (bound : dst.toNat + 8*(SszNative.NatAdd.count left right+1) ≤ 2^64)
    (rsi : Carry.get s .rsi = left.pointer) (rdx : Carry.get s .rdx = left.payload)
    (rcx : Carry.get s .rcx = right.pointer) (r8 : Carry.get s .r8 = right.payload)
    (rax : Carry.get s .rax = BitVec.ofNat 64 (SszNative.NatAdd.count left right))
    (r10 : Carry.get s .r10 = dst) (rbx : Carry.get s .rbx = dst)
    (mask : left.pointer = 0 → Carry.get s .r11 = 2305843009213693950#64)
    (P : MachineState → Prop)
    (hp : ∀ t, Carry.Post s left right dst t → Eventually (step e) P (t, base+1325)) :
    Eventually (step e) P (s, base+536) := by
  have notBothSmall := Carry.not_both_small left right s.dmem leftOwned rightOwned wide
  cases left with
  | small a =>
    cases right with
    | small b =>
      exfalso
      simpa [NatOperand.pointer] using notBothSmall
    | large pointer words =>
      exact Carry.small_cps e base hc s a pointer dst words rightOwned wide hm
        rightApart bound rsi rdx rcx r8 rax r10 rbx (mask rfl) P hp
  | large pointer words =>
    exact Carry.large_cps e base hc s pointer dst words right leftOwned rightOwned
      leftNonzero wide hm leftApart rightApart bound rsi rdx rcx r8 rax r10 P hp

end SszX86.NatAdd

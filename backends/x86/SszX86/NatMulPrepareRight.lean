import SszX86.NatMulPrepareRightLarge
import SszX86.NatMulPrepareRightSmall

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_right_route (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (leftCopy : s.regs.rax.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftCount : s.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount)
    (leftMarker : s.regs.r10.toBitVec = BitVec.ofNat 64 (left.wordCount+1))
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left right base)
      (s, if right.pointer = 0#64 then base + 100 else base + 129) := by
  cases right with
  | small limb =>
    simp only [NatOperand.pointer, ↓reduceIte]
    exact prepare_right_small_scanned e base hc s left limb
      leftPointer leftPayload rightPayload leftMarker leftAt
  | large p words =>
    have nonzero : p ≠ 0#64 := by
      intro hz
      have positive := rightAt.1
      simp [hz] at positive
    simp only [NatOperand.pointer, nonzero, ↓reduceIte]
    exact prepare_right_large e base hc s left p words leftPointer leftPayload leftCopy
      rightPointer rightPayload leftCount leftAt rightAt

end SszX86.NatMul

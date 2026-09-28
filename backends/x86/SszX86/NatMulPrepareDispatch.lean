import SszX86.NatMulPrepareRight

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_scanned_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftCount : s.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount)
    (leftMarker : s.regs.r10.toBitVec = BitVec.ofNat 64 (left.wordCount+1))
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left right base) (s, base + 53) := by
  apply scanned_left_cps e base hc
  · intro zero flags
    have phase := prepare_right_route e base hc (payloadState s flags) left right
      leftPointer leftPayload leftPayload rightPointer rightPayload leftCount leftMarker leftAt rightAt
    have hz : right.pointer = 0#64 := rightPointer.symm.trans zero
    rw [ite_eq_left hz] at phase
    exact eventually_weaken (step e) (Prepared (payloadState s flags) left right base)
      (Prepared s left right base) _
      (fun _ h => Prepared.rebase (s := s) (u := payloadState s flags) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro nonzero flags
    have phase := prepare_right_route e base hc (payloadState s flags) left right
      leftPointer leftPayload leftPayload rightPointer rightPayload leftCount leftMarker leftAt rightAt
    have hn : right.pointer ≠ 0#64 := fun hz => nonzero (rightPointer.trans hz)
    rw [ite_eq_right hn] at phase
    exact eventually_weaken (step e) (Prepared (payloadState s flags) left right base)
      (Prepared s left right base) _
      (fun _ h => Prepared.rebase (s := s) (u := payloadState s flags) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase

theorem prepare_zero_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftZero : left.wordCount = 0)
    (leftMarker : s.regs.r10.toBitVec = BitVec.ofNat 64 (left.wordCount+1))
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left right base) (s, base + 89) := by
  apply zero_left_cps e base hc
  · intro zero flags
    let u := {payloadState s flags with regs := {(payloadState s flags).regs with r12 := 0}}
    have count : u.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount := by simp [u, leftZero]
    have phase := prepare_right_route e base hc u left right
      leftPointer leftPayload leftPayload rightPointer rightPayload count leftMarker leftAt rightAt
    have hz : right.pointer = 0#64 := rightPointer.symm.trans zero
    rw [ite_eq_left hz] at phase
    exact eventually_weaken (step e) (Prepared u left right base) (Prepared s left right base) _
      (fun _ h => Prepared.rebase (s := s) (u := u) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro nonzero flags
    let u := {payloadState s flags with regs := {(payloadState s flags).regs with r12 := 0}}
    have count : u.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount := by simp [u, leftZero]
    have phase := prepare_right_route e base hc u left right
      leftPointer leftPayload leftPayload rightPointer rightPayload count leftMarker leftAt rightAt
    have hn : right.pointer ≠ 0#64 := fun hz => nonzero (rightPointer.trans hz)
    rw [ite_eq_right hn] at phase
    exact eventually_weaken (step e) (Prepared u left right base) (Prepared s left right base) _
      (fun _ h => Prepared.rebase (s := s) (u := u) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase

end SszX86.NatMul

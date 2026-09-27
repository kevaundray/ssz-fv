import SszX86.NatAddPrepareLeftLarge
import SszX86.NatAddPrepareLeftSmall

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Complete allocation-free preparation after the six PUSHes. All operand
representation cases and both ordered zero-normalization scans are included. -/
theorem prepare_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left right base) (s, base + 10) := by
  apply entry_dispatch_cps e base hc s
  intro flags
  cases left with
  | small limb =>
    have zero : s.regs.rsi.toBitVec = 0#64 := leftPointer
    rw [ite_eq_left zero]
    have phase := prepare_left_small e base hc {s with status := flags} limb right
      leftPointer leftPayload rightPointer rightPayload rightAt
    exact eventually_weaken _ _ _ _
      (fun _ h => Prepared.rebase (s := s) (u := {s with status := flags})
        ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  | large p words =>
    have positive := leftAt.1
    have nonzero : s.regs.rsi.toBitVec ≠ 0#64 := by
      intro zero
      have pZero : p = 0#64 := leftPointer.symm.trans zero
      simp [pZero] at positive
    rw [ite_eq_right nonzero]
    have phase := prepare_left_large e base hc {s with status := flags} p words right
      leftPointer leftPayload rightPointer rightPayload leftAt rightAt
    exact eventually_weaken _ _ _ _
      (fun _ h => Prepared.rebase (s := s) (u := {s with status := flags})
        ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase

end SszX86.NatAdd

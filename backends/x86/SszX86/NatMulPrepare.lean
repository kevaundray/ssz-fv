import SszX86.NatMulPrepareLeftLarge
import SszX86.NatMulPrepareLeftSmall

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left right base) (s, base + 14) := by
  apply left_entry_cps e base hc
  · intro zero flags
    cases left with
    | small limb =>
      have phase := prepare_left_small e base hc {s with status := flags} limb right
        leftPointer leftPayload rightPointer rightPayload rightAt
      exact eventually_weaken _ _ _ _
        (fun _ h => Prepared.rebase ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
    | large p words =>
      have positive := leftAt.1
      have hp : p = 0#64 := leftPointer.symm.trans zero
      simp [hp] at positive
  · intro nonzero flags
    cases left with
    | small limb => exact False.elim (nonzero leftPointer)
    | large p words =>
      let u := leftScanState s s.regs.r10.toBitVec (s.regs.rdx.toBitVec + 1) flags
      have count : u.regs.r12.toBitVec = BitVec.ofNat 64 (words.length+1) := by
        change s.regs.rdx.toBitVec + 1 = BitVec.ofNat 64 (words.length+1)
        rw [leftPayload]
        change BitVec.ofNat 64 words.length + 1 = BitVec.ofNat 64 (words.length+1)
        bv_omega
      have phase := prepare_left_large e base hc u p words right
        leftPointer leftPayload rightPointer rightPayload count leftAt rightAt
      exact eventually_weaken _ _ _ _
        (fun _ h => Prepared.rebase ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase

end SszX86.NatMul

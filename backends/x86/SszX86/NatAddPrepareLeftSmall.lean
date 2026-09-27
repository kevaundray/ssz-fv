import SszX86.NatAddPrepareSmallPair
import SszX86.NatAddPrepareRightLarge

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem small_left_right_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 141))
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 75)) :
    Eventually (step e) P (s, base + 70) := by
  have target := hc.targets ("natAdd_u141", 141) (by decide)
  natadd_step 23 using hc
  constructor <;> natadd_step 24 using hc
  all_goals
    by_cases zero : s.regs.rcx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, Effects.All] using small zero _
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _

/-- Small-left preparation includes its explicit zero specialization and still
uses the complete physical right scan whenever the right representation is Large. -/
theorem prepare_left_small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = 0#64)
    (leftPayload : s.regs.rdx.toBitVec = limb)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s (.small limb) right base) (s, base + 60) := by
  apply small_left_cps e base hc s
  · intro zero flags
    have limbZero : limb = 0#64 := leftPayload.symm.trans zero
    have leftCount : (NatOperand.small limb).wordCount = 0 := by
      simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, limbZero, ↓reduceIte]
    apply zero_left_cps e base hc
    · intro pointerZero flags
      cases right with
      | small other =>
        apply right_small_normalize e base hc
        intro flags
        apply Eventually.done
        apply Prepared.zero_left (s := s) leftCount ⟨rfl, rfl, rfl, rfl, rfl⟩
        · simp only [normalized_small, NatOperand.pointer, UInt64.toBitVec_ofNat]
        · simpa only [normalized_small, NatOperand.payload] using rightPayload
        · rfl
      | large p words =>
        have positive := rightAt.1
        have pZero : p = 0#64 := rightPointer.symm.trans pointerZero
        simp [pZero] at positive
    · intro pointerNonzero flags
      cases right with
      | small other => exact False.elim (pointerNonzero rightPointer)
      | large p words =>
        have phase := prepare_right_large e base hc
          ({s with regs := {s.regs with rdx := 0, rax := 0}, status := flags})
          (.small limb) p words leftPointer
          (by simp only [NatOperand.payload, limbZero, UInt64.toBitVec_ofNat]) rightPointer rightPayload
          (by simp only [leftCount, UInt64.toBitVec_ofNat]) (by trivial) rightAt
        exact eventually_weaken _ _ _ _
          (fun _ h => Prepared.rebase (s := s)
            (u := {s with regs := {s.regs with rdx := 0, rax := 0}, status := flags})
            ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro nonzero flags
    have limbNonzero : limb ≠ 0#64 := by simpa only [leftPayload] using nonzero
    have leftCount : (NatOperand.small limb).wordCount = 1 := by
      simp only [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, limbNonzero, ↓reduceIte]
    apply small_left_right_dispatch e base hc
    · intro pointerNonzero flags
      cases right with
      | small other => exact False.elim (pointerNonzero rightPointer)
      | large p words =>
        have phase := prepare_right_large e base hc
          ({s with regs := {s.regs with rax := 1}, status := flags})
          (.small limb) p words leftPointer leftPayload rightPointer rightPayload
          (by simp only [leftCount, UInt64.toBitVec_ofNat]) (by trivial) rightAt
        exact eventually_weaken _ _ _ _
          (fun _ h => Prepared.rebase (s := s)
            (u := {s with regs := {s.regs with rax := 1}, status := flags})
            ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
    · intro pointerZero flags
      cases right with
      | small other =>
        have phase := prepare_small_pair e base hc
          ({s with regs := {s.regs with rax := 1}, status := flags}) limb other leftPayload rightPayload limbNonzero
        exact eventually_weaken _ _ _ _
          (fun _ h => Prepared.rebase (s := s)
            (u := {s with regs := {s.regs with rax := 1}, status := flags})
            ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
      | large p words =>
        have positive := rightAt.1
        have pZero : p = 0#64 := rightPointer.symm.trans pointerZero
        simp [pZero] at positive

end SszX86.NatAdd

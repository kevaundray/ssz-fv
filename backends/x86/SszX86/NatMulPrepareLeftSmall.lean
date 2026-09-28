import SszX86.NatMulPrepareRightLarge

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_left_small (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64) (right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = 0#64)
    (leftPayload : s.regs.rdx.toBitVec = limb)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s (.small limb) right base) (s, base + 63) := by
  apply small_left_dispatch_cps e base hc
  · intro leftZero flags
    have limbZero : limb = 0#64 := leftPayload.symm.trans leftZero
    have countZero : (NatOperand.small limb).wordCount = 0 := by
      simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, limbZero]
    apply empty_left_dispatch_cps e base hc
    · intro rightZero flags'
      apply Eventually.done
      exact .zero (Or.inl countZero) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
    · intro rightNonzero flags'
      cases right with
      | small r => exact False.elim (rightNonzero rightPointer)
      | large p words =>
        let u := emptyLeftState {s with status := flags} flags'
        have copy : u.regs.rax.toBitVec = (NatOperand.small limb).payload := by
          simp only [u, emptyLeftState, NatOperand.payload, limbZero,
            show (0 : UInt64).toBitVec = 0#64 by decide]
        have count : u.regs.r12.toBitVec = BitVec.ofNat 64 (NatOperand.small limb).wordCount := by
          simp [u, emptyLeftState, countZero]
        have phase := prepare_right_large e base hc u (.small limb) p words
          leftPointer leftPayload copy rightPointer rightPayload count trivial rightAt
        exact eventually_weaken (step e) (Prepared u (.small limb) (.large p words) base)
          (Prepared s (.small limb) (.large p words) base) _
          (fun _ h => Prepared.rebase (s := s) (u := u) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro leftNonzero rightNonzero flags
    have limbNonzero : limb ≠ 0#64 := fun hz => leftNonzero (leftPayload.trans hz)
    have countOne : (NatOperand.small limb).wordCount = 1 := by
      simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, limbNonzero]
    cases right with
    | small r => exact False.elim (rightNonzero rightPointer)
    | large p words =>
      have count : (smallLeftState s flags).regs.r12.toBitVec =
          BitVec.ofNat 64 (NatOperand.small limb).wordCount := by simp [smallLeftState, countOne]
      have phase := prepare_right_large e base hc (smallLeftState s flags) (.small limb) p words
        leftPointer leftPayload leftPayload rightPointer rightPayload count trivial rightAt
      exact eventually_weaken (step e) (Prepared (smallLeftState s flags) (.small limb) (.large p words) base)
        (Prepared s (.small limb) (.large p words) base) _
        (fun _ h => Prepared.rebase (s := s) (u := smallLeftState s flags) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro leftNonzero rightZero flags
    have limbNonzero : limb ≠ 0#64 := fun hz => leftNonzero (leftPayload.trans hz)
    have countOne : (NatOperand.small limb).wordCount = 1 := by
      simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, limbNonzero]
    cases right with
    | large p words =>
      have positive := rightAt.1
      have hp : p = 0#64 := rightPointer.symm.trans rightZero
      simp [hp] at positive
    | small r =>
      apply small_right_dispatch_cps e base hc
      · intro zero flags'
        have rZero : r = 0#64 := rightPayload.symm.trans zero
        apply Eventually.done
        apply Prepared.zero
        · right
          simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rZero]
        · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · rfl
      · intro nonzero flags'
        have rNonzero : r ≠ 0#64 := fun hz => nonzero (rightPayload.trans hz)
        have rightOne : (NatOperand.small r).wordCount = 1 := by
          simp [NatOperand.wordCount, NatOperand.words, NatCompare.single_sig, rNonzero]
        apply right_factor_cps e base hc
        apply Eventually.done
        apply Prepared.word_left
        · omega
        · exact rightOne
        · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · exact leftPointer
        · exact leftPayload
        · simpa only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord, NatOperand.words,
            List.getElem?_cons_zero, Option.getD_some] using rightPayload
        · rfl

end SszX86.NatMul

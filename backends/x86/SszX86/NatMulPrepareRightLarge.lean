import SszX86.NatMulPrepareSelected

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_right_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left : NatOperand) (p : BitVec 64) (words : List (BitVec 64))
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (leftCopy : s.regs.rax.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = p)
    (rightPayload : s.regs.r8.toBitVec = BitVec.ofNat 64 words.length)
    (leftCount : s.regs.r12.toBitVec = BitVec.ofNat 64 left.wordCount)
    (leftAt : left.At (widthLoad s.dmem))
    (rightAt : (NatOperand.large p words).At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left (.large p words) base) (s, base + 129) := by
  have extent := rightAt.2.2.1
  have bound : words.length+1 < 2^64 := by omega
  have leftBound := NatAdd.operand_count_bound s.dmem left leftAt
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [rightPointer]
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (rightAt.2.2.2 i)
  apply right_entry_cps e base hc s
  intro initialFlags
  have entryCount : s.regs.r8.toBitVec + 1 = BitVec.ofNat 64 (words.length+1) := by
    rw [rightPayload]
    bv_omega
  have scanned := right_scan e base hc s words bound hm
    (Prepared s left (.large p words) base) words.length (by omega)
    s.regs.r13.toBitVec initialFlags
  rw [entryCount, rightPayload]
  apply scanned
  · intro c flags zero
    apply Eventually.done
    apply Prepared.zero
    · exact Or.inr zero
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rfl
  · intro rightNonzero flags
    have rightPositive : 0 < Limbs.sigWords words := by
      change Limbs.sigWords words ≠ 0 at rightNonzero
      omega
    have rightBound : Limbs.sigWords words < 2^64 := by
      have := Limbs.sigWords_le_length words
      omega
    have firstIndex : 0 < words.length := by
      have := Limbs.sigWords_le_length words
      omega
    let u := rightScanState s (1 - BitVec.ofNat 64 (Limbs.sigWords words))
      (BitVec.ofNat 64 (Limbs.sigWords words)) (BitVec.ofNat 64 (Limbs.sigWords words)) flags
    apply right_count_finish_cps e base hc u (words[0]?.getD 0)
    · intro one
      change Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 =
        some ((words[0]?.getD 0).toNat : Int)
      have loaded := hm ⟨0, firstIndex⟩
      change Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*0)) 8 =
        some (words[0].toNat : Int) at loaded
      simpa only [Nat.mul_zero, BitVec.add_zero,
        List.getElem?_eq_getElem firstIndex, Option.getD_some] using loaded
    · intro zero flags'
      have leftZero : left.wordCount = 0 := by
        change s.regs.r12.toBitVec = 0#64 at zero
        rw [leftCount] at zero
        bv_omega
      apply Eventually.done
      exact .zero (Or.inl leftZero) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
    · intro leftNonzero notone flags'
      have nonzero : left.wordCount ≠ 0 := by
        intro hz
        apply leftNonzero
        change s.regs.r12.toBitVec = 0#64
        simpa only [hz] using leftCount
      have rightMany : 1 < (NatOperand.large p words).wordCount := by
        change 1 < Limbs.sigWords words
        have ne : Limbs.sigWords words ≠ 1 := by
          intro hz
          apply notone
          change BitVec.ofNat 64 (Limbs.sigWords words) = 1#64
          simp only [hz]
        omega
      have phase := prepare_selected e base hc {u with status := flags'} left (.large p words)
        leftPointer leftCopy rightPointer rightPayload leftCount rfl rfl leftAt nonzero rightMany
      exact eventually_weaken (step e) (Prepared {u with status := flags'} left (.large p words) base)
        (Prepared s left (.large p words) base) _
        (fun _ h => Prepared.rebase (s := s) (u := {u with status := flags'}) ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
    · intro leftNonzero one flags'
      have nonzero : left.wordCount ≠ 0 := by
        intro hz
        apply leftNonzero
        change s.regs.r12.toBitVec = 0#64
        simpa only [hz] using leftCount
      have rightOne : (NatOperand.large p words).wordCount = 1 := by
        change BitVec.ofNat 64 (Limbs.sigWords words) = 1#64 at one
        change Limbs.sigWords words = 1
        bv_omega
      apply right_factor_cps e base hc
      apply Eventually.done
      exact .word_left nonzero rightOne ⟨rfl, rfl, rfl, rfl, rfl⟩
        leftPointer leftPayload rfl rfl

end SszX86.NatMul

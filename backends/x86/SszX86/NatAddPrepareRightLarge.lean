import SszX86.NatAddPrepared
import SszX86.NatAddDispatch
import SszX86.NatAddNormalizeLeftPhase
import SszX86.NatAddNormalizeRightPhase

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Right-Large preparation includes its original-length count scan and both
ordered zero branches, including their second normalization scans. -/
theorem prepare_right_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left : NatOperand) (p : BitVec 64) (words : List (BitVec 64))
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = p)
    (rightPayload : s.regs.r8.toBitVec = BitVec.ofNat 64 words.length)
    (leftCount : s.regs.rax.toBitVec = BitVec.ofNat 64 left.wordCount)
    (leftAt : left.At (widthLoad s.dmem))
    (rightAt : (NatOperand.large p words).At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s left (.large p words) base) (s, base + 141) := by
  have positive := rightAt.1
  have extent := rightAt.2.2.1
  have bound : words.length+1 < 2^64 := by omega
  have leftBound := operand_count_bound s.dmem left leftAt
  have pNonzero : p ≠ 0#64 := by intro hz; simp [hz] at positive
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rcx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [rightPointer]
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (rightAt.2.2.2 i)
  have borrowRight (u : MachineData) (frame : ControlFrame s u)
      (pointer : u.regs.rcx.toBitVec = p)
      (payload : u.regs.r8.toBitVec = BitVec.ofNat 64 words.length)
      (zero : left.wordCount = 0) :
      Eventually (step e) (Prepared s left (.large p words) base) (u, base + 333) := by
    apply normalize_right_large_cps e base hc u p words pointer payload
    · simpa only [frame.memory] using rightAt
    · intro v next ptr pay
      exact .done _ (.zero_left zero (frame.trans next) ptr pay rfl)
  have borrowLeft (u : MachineData) (frame : ControlFrame s u)
      (pointer : u.regs.rsi.toBitVec = left.pointer)
      (payload : u.regs.rdx.toBitVec = left.payload)
      (nonzero : left.wordCount ≠ 0) (zero : (NatOperand.large p words).wordCount = 0) :
      Eventually (step e) (Prepared s left (.large p words) base) (u, base + 271) := by
    apply normalize_left_cps e base hc u left pointer payload
    · simpa only [frame.memory] using leftAt
    · intro v next ptr pay
      exact .done _ (.zero_right nonzero zero (frame.trans next) ptr pay rfl)
  have scanned : Eventually (step e) (Prepared s left (.large p words) base)
      (countState s s.regs.rax.toBitVec (BitVec.ofNat 64 (words.length+1))
        s.regs.r11.toBitVec s.status, base + 160) := by
    apply right_count e base hc s s.regs.rax.toBitVec words bound hm _ words.length (by omega)
    · intro y flags zeroRight
      apply right_zero_cps e base hc
      intro flags
      by_cases zeroLeft : left.wordCount = 0
      · have aZero : s.regs.rax.toBitVec = 0#64 := by rw [leftCount, zeroLeft]
        simp only [countState, UInt64.toBitVec_ofBitVec, aZero, ↓reduceIte]
        exact borrowRight _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rightPointer rightPayload zeroLeft
      · have aNonzero : s.regs.rax.toBitVec ≠ 0#64 := by rw [leftCount]; bv_omega
        simp only [countState, UInt64.toBitVec_ofBitVec, aNonzero, ↓reduceIte]
        exact borrowLeft _ ⟨rfl, rfl, rfl, rfl, rfl⟩ leftPointer leftPayload zeroLeft zeroRight
    · intro nonzeroRight flags
      apply right_nonzero_cps e base hc
      intro flags
      by_cases zeroLeft : left.wordCount = 0
      · have aZero : s.regs.rax.toBitVec = 0#64 := by rw [leftCount, zeroLeft]
        simp only [countState, UInt64.toBitVec_ofBitVec, aZero, ↓reduceIte]
        exact borrowRight _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rightPointer rightPayload zeroLeft
      · have aNonzero : s.regs.rax.toBitVec ≠ 0#64 := by rw [leftCount]; bv_omega
        simp only [countState, UInt64.toBitVec_ofBitVec, aNonzero, ↓reduceIte]
        apply Eventually.done
        apply Prepared.counted (s := s) (right := .large p words) zeroLeft nonzeroRight
        · refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, leftPointer, leftPayload,
            rightPointer, rightPayload, leftCount, rfl, ?_⟩
          have lowByte :
              ((BitVec.ofNat 64 (Limbs.significantCount words words.length)).extractLsb' 8 56 ++ 1#8).setWidth 8 = 1#8 :=
            BitVec.setWidth_append_eq_right
              (a := (BitVec.ofNat 64 (Limbs.significantCount words words.length)).extractLsb' 8 56) (b := 1#8)
          change
            (((BitVec.ofNat 64 (Limbs.significantCount words words.length)).extractLsb' 8 56 ++ 1#8).setWidth 8 = 0#8) ↔ p = 0#64
          rw [lowByte]
          simp only [pNonzero, iff_false]
          decide
        · rfl
  apply right_count_entry_cps e base hc s
  simpa only [countState, rightPayload, BitVec.ofNat_add,
    UInt64.ofBitVec_toBitVec] using scanned

end SszX86.NatAdd

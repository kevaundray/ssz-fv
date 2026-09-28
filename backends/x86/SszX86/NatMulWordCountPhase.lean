import SszX86.NatMulWordPrepared
import SszX86.NatMulWordEmpty

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- The entire raw Large count phase, including empty and all-zero physical
lists. Only the true multiword continuation is left to the allocating loop. -/
theorem large_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (p : BitVec 64) (words : List (BitVec 64))
    (factor address capacity used ra : BitVec 64)
    (owned : Owned s (.large p words) factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1)
    (frame : PureFrame s t) (pointer : t.regs.rsi.toBitVec = p)
    (payload : t.regs.r9.toBitVec = BitVec.ofNat 64 words.length)
    (factorReg : t.regs.rcx.toBitVec = factor)
    (multiply : ∀ u, 1 < (NatOperand.large p words).wordCount →
      MultiplyReady s u (.large p words) factor →
      Eventually (step e) (Post s (.large p words) factor address capacity used ra) (u, base+195)) :
    Eventually (step e) (Post s (.large p words) factor address capacity used ra) (t, base+122) := by
  have stored : (NatOperand.large p words).At (widthLoad t.dmem) := by
    rw [frame.memory]
    exact pushed_operand s (.large p words) factor address capacity used ra owned
  have positivePointer := stored.1
  have extent := stored.2.2.1
  have bound : words.length+3 < 2^64 := by omega
  have hm : ∀ i : Fin words.length,
      Mem.loadInt t.dmem (t.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [pointer]
    simpa only [width_address] using widthLoad_eq t.dmem _ _ _ (stored.2.2.2 i)
  have loadScalar (u : MachineData) (retained : PureFrame s u)
      (input : u.regs.rsi.toBitVec = p) (factorAt : u.regs.rcx.toBitVec = factor)
      (small : (NatOperand.large p words).wordCount ≤ 1) (nonempty : 0 < words.length) :
      Eventually (step e) (Post s (.large p words) factor address capacity used ra) (u, base+393) := by
    apply small_word_load_cps e base hc u (SszNative.NatMul.lowWord (.large p words))
    · have first := hm ⟨0, nonempty⟩
      rw [pointer] at first
      rw [input, retained.memory, ← frame.memory]
      simpa only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord, NatOperand.words,
        List.getElem?_eq_getElem nonempty, Option.getD_some, Nat.mul_zero, BitVec.add_zero] using first
    apply small_multiply_cps e base hc s _ (.large p words) factor address capacity used ra
      owned nonzero notone small
    · exact ⟨retained.memory, retained.sp, retained.output, retained.arena, retained.simd⟩
    · rfl
    · exact factorAt
  have scanned : Eventually (step e) (Post s (.large p words) factor address capacity used ra)
      (countState t (BitVec.ofNat 64 (words.length+3)) (BitVec.ofInt 64 (-1))
        t.regs.r15.toBitVec t.status, base+144) := by
    apply count_scan e base hc t words bound hm _ words.length (by omega)
    · intro saved flags zero
      have small : (NatOperand.large p words).wordCount ≤ 1 := by
        change Limbs.sigWords words ≤ 1
        change Limbs.sigWords words = 0 at zero
        omega
      apply zero_count_select_cps e base hc
      · intro empty flags'
        have emptyNat : words.length = 0 := by
          change t.regs.r9.toBitVec = 0#64 at empty
          rw [payload] at empty
          bv_omega
        have emptyWords : words = [] := List.eq_nil_of_length_eq_zero emptyNat
        apply empty_multiply_cps e base hc s _ (.large p words) factor address capacity used ra
          owned nonzero notone small
        · exact ⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩
        · simp only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord, NatOperand.words,
            emptyWords, List.getElem?_nil, Option.getD_none, UInt64.toBitVec_ofNat]
        · exact factorReg
        · rfl
      · intro nonempty flags'
        have lengthPositive : 0 < words.length := by
          by_contra none
          have lengthZero : words.length = 0 := by omega
          apply nonempty
          change t.regs.r9.toBitVec = 0#64
          rw [payload, lengthZero]
          rfl
        exact loadScalar _ ⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩
          pointer factorReg small lengthPositive
    · intro positive flags
      have countPositive : 0 < Limbs.sigWords words := by
        change Limbs.sigWords words ≠ 0 at positive
        omega
      have countBound := Limbs.sigWords_le_length words
      apply count_select_cps e base hc _ (Limbs.sigWords words) countPositive (by omega) rfl
      · intro one flags'
        have small : (NatOperand.large p words).wordCount ≤ 1 := by
          change Limbs.sigWords words ≤ 1
          omega
        exact loadScalar _ ⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩
          pointer factorReg small (by omega)
      · intro large flags'
        apply multiply _ large
        refine ⟨⟨frame.memory, frame.sp, frame.output, frame.arena, frame.simd⟩,
          pointer, payload, factorReg, rfl, rfl, ?_⟩
        change BitVec.ofInt 64 (-1) + BitVec.ofNat 64 (words.length-Limbs.sigWords words+1) =
          BitVec.ofNat 64 (words.length-Limbs.sigWords words)
        bv_omega
  apply count_entry_cps e base hc t
  simpa only [countState, payload, BitVec.ofNat_add, UInt64.ofBitVec_toBitVec,
    show BitVec.ofNat 64 3 = (3 : BitVec 64) by decide] using scanned

end SszX86.NatMulWord

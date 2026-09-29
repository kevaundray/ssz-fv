import SszX86.NatMulWordLargeLoopFacts
import SszX86.WordNormalize

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem pairs_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (source dst factor : BitVec 64) (words : List (BitVec 64))
    (capacity : Nat) (capacityBound : capacity < 2^64)
    (apart : NatAdd.Carry.Apart (.large source words) dst (8*capacity))
    (P : MachineState → Prop) :
    ∀ pairs, 0 < pairs → ∀ index, 0 < index → index+2*pairs ≤ capacity →
    ∀ (s : MachineData) (carry : Nat), carry < 2^64 →
    s.regs.rsi.toBitVec = source → s.regs.r9.toBitVec = BitVec.ofNat 64 words.length →
    s.regs.rcx.toBitVec = factor → s.regs.rbp.toBitVec = dst+8#64 →
    s.regs.r12.toBitVec = BitVec.ofNat 64 (index+2*pairs-1) →
    s.regs.rax.toBitVec = BitVec.ofNat 64 index →
    s.regs.r10.toBitVec = BitVec.ofNat 64 carry →
    (NatOperand.large source words).At (widthLoad s.dmem) →
    Large.Mapped s.dmem dst (8*capacity) →
    (∀ t, PairStable s t →
      t.dmem = Large.fillMem s.dmem dst index
        (LimbMul.inner (2*pairs) factor (words.drop index) [] carry).1 →
      t.regs.r8.toBitVec = BitVec.ofNat 64 (index+2*pairs-2) →
      t.regs.rax.toBitVec = BitVec.ofNat 64 (index+2*pairs) →
      t.regs.r10.toBitVec = BitVec.ofNat 64
        (LimbMul.inner (2*pairs) factor (words.drop index) [] carry).2 →
      Eventually (step e) P (t, base+702)) →
    Eventually (step e) P (s, base+466) := by
  intro pairs
  induction pairs with
  | zero => intro positive; omega
  | succ pairs ih =>
    intro positive index indexPositive inside s carry carryBound sourceReg lengthReg factorReg
      destinationReg pairedReg indexReg carryReg input outputMapped next
    let first := words[index]?.getD 0
    let second := words[index+1]?.getD 0
    let firstResult := LimbMul.step factor first 0 carry
    let secondResult := LimbMul.step factor second 0 firstResult.2
    have indexBound : index < 2^64 := by omega
    have nextBound : index+1 < 2^64 := by omega
    have lengthBound : words.length < 2^64 := by have := input.2.2.1; omega
    have indexNat : s.regs.rax.toNat = index := by
      change s.regs.rax.toBitVec.toNat = index
      rw [indexReg]
      exact Nat.mod_eq_of_lt indexBound
    have lengthNat : s.regs.r9.toNat = words.length := by
      change s.regs.r9.toBitVec.toNat = words.length
      rw [lengthReg]
      exact Nat.mod_eq_of_lt lengthBound
    have plusOne : s.regs.rax.toBitVec+1 = BitVec.ofNat 64 (index+1) := by
      simp (config := {instances := true}) only [indexReg, BitVec.ofNat_add, WordNormalize.bitvecNumeral]
    have plusOneNat : (s.regs.rax.toBitVec+1).toNat = index+1 := by
      rw [plusOne]
      exact Nat.mod_eq_of_lt nextBound
    have addresses := pair_addresses s dst index destinationReg indexReg
    have sourceNext : s.regs.rsi.toBitVec + s.regs.rax.toBitVec*8#64+8#64 =
        source + BitVec.ofNat 64 (index+1)*8#64 := by
      rw [sourceReg, indexReg, BitVec.ofNat_add]
      bv_omega
    have firstInput := source_word s.dmem source words index input
    have firstPreserved := NatAdd.Carry.fill_preserves s.dmem (.large source words) dst index
      (8*capacity) [(firstStep s first).1] input apart (by simp only [List.length_cons, List.length_nil]; omega)
    have secondInput := source_word
      (Mem.storeInt s.dmem (firstAddress s) 8 (firstStep s first).1.toInt)
      source words (index+1) (by simpa only [Large.fillMem, addresses.1] using firstPreserved)
    have firstCarryBound : firstResult.2 < 2^64 := LimbMul.step_carry_lt factor first 0 carry carryBound
    have secondCarryBound : secondResult.2 < 2^64 := LimbMul.step_carry_lt factor second 0 firstResult.2 firstCarryBound
    have carryNat : s.regs.r10.toNat = carry := by
      change s.regs.r10.toBitVec.toNat = carry
      rw [carryReg]
      exact Nat.mod_eq_of_lt carryBound
    have checkedFirst : firstStep s first = firstResult := by
      simp only [firstStep, factorReg, carryNat, firstResult]
    have checkedSecond : secondStep s first second = secondResult := by
      simp only [secondStep, factorReg, checkedFirst, secondResult]
    have recurrence := inner_two (2*pairs) index factor words carry
    have totalWidth : 2*(pairs+1) = 2*pairs+2 := by omega
    have exitIff : s.regs.rax.toBitVec+1 = s.regs.r12.toBitVec ↔ pairs = 0 := by
      rw [plusOne, pairedReg]
      bv_omega
    apply pair_cps e base hc s first second
    · simpa only [sourceReg, indexReg, indexNat, lengthNat] using firstInput.1
    · simpa only [indexNat, lengthNat] using firstInput.2
    · simpa only [plusOneNat, lengthNat, sourceNext] using secondInput.1
    · simpa only [plusOneNat, lengthNat] using secondInput.2
    · rw [addresses.1]
      exact Delimited.Reservation.mapped_subrange s.dmem dst (8*capacity) (8*index) 8 outputMapped (by omega)
    · rw [addresses.2]
      exact Delimited.Reservation.mapped_subrange s.dmem dst (8*capacity) (8*(index+1)) 8 outputMapped (by omega)
    · intro finished flags
      have zero := exitIff.mp finished
      subst pairs
      apply next (unrolledState s first second flags) (pair_stable _ _ _ _)
      · rw [totalWidth, recurrence]
        simpa only [LimbMul.inner, first, second, firstResult, secondResult, unrolledState]
          using pair_memory s dst factor index carry first second destinationReg indexReg factorReg carryReg carryBound
      · simpa only [unrolledState, secondProducedState, indexReg] using congrArg (BitVec.ofNat 64) (show index = index+2*(0+1)-2 by omega)
      · simp (config := {instances := true}) only
          [unrolledState, secondProducedState, UInt64.toBitVec_ofBitVec, indexReg,
            BitVec.ofNat_add, WordNormalize.bitvecNumeral]
      · rw [totalWidth, recurrence]
        simp only [LimbMul.inner, unrolledState, secondProducedState, checkedSecond,
          UInt64.toBitVec_ofNat', first, second, firstResult, secondResult]
    · intro unfinished flags
      have remainingPositive : 0 < pairs := by have := mt exitIff.mpr unfinished; omega
      let t := unrolledState s first second flags
      have stable : PairStable s t := pair_stable s first second flags
      have memory : t.dmem = Large.fillMem s.dmem dst index [firstResult.1, secondResult.1] :=
        pair_memory s dst factor index carry first second destinationReg indexReg factorReg carryReg carryBound
      have endpoint : index+2+2*pairs = index+2*(pairs+1) := by omega
      apply ih remainingPositive (index+2) (by omega) (by omega) t secondResult.2 secondCarryBound
      · simpa only [stable.rsi] using sourceReg
      · simpa only [stable.r9] using lengthReg
      · simpa only [stable.rcx] using factorReg
      · simpa only [stable.rbp] using destinationReg
      · rw [stable.r12, pairedReg]
        congr 1
        omega
      · simp (config := {instances := true}) only
          [t, unrolledState, secondProducedState, UInt64.toBitVec_ofBitVec,
            indexReg, BitVec.ofNat_add, WordNormalize.bitvecNumeral]
      · simp only [t, unrolledState, secondProducedState, UInt64.toBitVec_ofNat', checkedSecond]
      · rw [memory]
        exact NatAdd.Carry.fill_preserves s.dmem (.large source words) dst index (8*capacity)
          [firstResult.1, secondResult.1] input apart (by simp only [List.length_cons, List.length_nil]; omega)
      · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ outputMapped)
      · intro u restStable restMemory finalIndex finalCounter finalCarry
        apply next u (stable.trans restStable)
        · rw [totalWidth, recurrence]
          simp only [first, second, firstResult, secondResult, Large.fillMem] at memory ⊢
          simpa only [memory, Large.fillMem] using restMemory
        · simpa only [endpoint] using finalIndex
        · simpa only [endpoint] using finalCounter
        · rw [totalWidth, recurrence]
          exact finalCarry

end SszX86.NatMulWord

import SszX86.NatMulLoopRead

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

/-- Natural induction over the remaining original inner iterations. The result
is the exact sequence of stores, not an assumed initialized final buffer. -/
theorem inner_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (source dst : BitVec 64) (sourceCapacity leftCount rightCount row : Nat)
    (apart : Large.Disjoint source dst sourceCapacity (8*(leftCount+rightCount)))
    (span : dst.toNat + 8*(leftCount+rightCount) ≤ 2^64)
    (rowBound : row < leftCount) (P : MachineState → Prop) :
    ∀ remaining, 0 < remaining → ∀ column (words old : List (BitVec 64)),
    column + remaining = rightCount → words.length = remaining → remaining ≤ old.length →
    row + column + old.length ≤ leftCount + rightCount →
    8*(column+words.length) ≤ sourceCapacity →
    ∀ (s : MachineData) (factor : BitVec 64) (carry : Nat), carry < 2^64 →
    s.regs.rsi.toBitVec = source → s.regs.r10.toBitVec = dst + BitVec.ofNat 64 (8*row) →
    s.regs.rcx.toBitVec = factor → s.regs.r13.toBitVec = BitVec.ofNat 64 rightCount →
    s.regs.r14.toBitVec = BitVec.ofNat 64 (leftCount+rightCount) →
    s.regs.r15.toBitVec = BitVec.ofNat 64 row →
    s.regs.rbx.toBitVec = BitVec.ofNat 64 column →
    s.regs.r9.toBitVec = BitVec.ofNat 64 carry → s.regs.r8 = 0 →
    ReadAt s.dmem source column words → ReadAt s.dmem dst (row+column) old →
    (∀ t, InnerStable s t → t.regs.rbx.toBitVec = BitVec.ofNat 64 rightCount →
      t.regs.r9.toBitVec = BitVec.ofNat 64 (LimbMul.inner remaining factor words old carry).2 →
      t.regs.r8 = 0 →
      t.dmem = Large.fillMem s.dmem dst (row+column)
        (LimbMul.inner remaining factor words old carry).1 →
      Eventually (step e) P (t, base+627)) →
    Eventually (step e) P (s, base+576) := by
  intro remaining
  induction remaining with
  | zero => intro positive; omega
  | succ remaining ih =>
    intro positive column words old width wordsLength oldLength bufferLength sourceLength
      s factor carry carryBound rsi r10 rcx r13 r14 r15 rbx r9 r8 sourceRead oldRead next
    cases words with
    | nil => simp only [List.length_nil] at wordsLength; omega
    | cons word words =>
      cases old with
      | nil => simp only [List.length_nil] at oldLength; omega
      | cons oldWord old =>
        let one := LimbMul.step factor word oldWord carry
        have physical : leftCount+rightCount < 2^64 := physical_counts dst _ _ span
        have columnBound : column < rightCount := by omega
        have address : s.regs.r10.toBitVec + s.regs.rbx.toBitVec * 8#64 =
            dst + BitVec.ofNat 64 (8*(row+column)) := by
          rw [r10, rbx]
          simp [BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_add, BitVec.add_assoc, Nat.mul_comm]
        have sourceAddress : s.regs.rsi.toBitVec + s.regs.rbx.toBitVec * 8#64 =
            source + BitVec.ofNat 64 (8*column) := by
          rw [rsi, rbx]
          simp [BitVec.ofNat_mul, Nat.mul_comm]
        apply inner_step_cps e base hc s word oldWord carry carryBound r9 r8
        · rw [r15, rbx, r14]
          exact inner_guard _ _ _ _ physical rowBound columnBound
        · rw [sourceAddress]
          exact sourceRead.head
        · rw [address]
          exact oldRead.head
        intro t stable tIndex tCarry tZero tMemory
        have memory : t.dmem = Mem.storeInt s.dmem (dst + BitVec.ofNat 64 (8*(row+column)))
            8 one.1.toInt := by simpa [rcx, address, one] using tMemory
        have index : t.regs.rbx.toBitVec = BitVec.ofNat 64 (column+1) := by
          simpa [rbx, BitVec.ofNat_add] using tIndex
        have carried : t.regs.r9.toBitVec = BitVec.ofNat 64 one.2 := by
          simpa [rcx, one] using tCarry
        by_cases last : remaining = 0
        · subst remaining
          have atEnd : s.regs.rbx.toBitVec + 1 = s.regs.r13.toBitVec := by
            rw [rbx, r13]
            bv_omega
          simp only [atEnd, ite_true]
          apply next t stable
          · simpa [width] using index
          · simpa [LimbMul.inner, one] using carried
          · exact tZero
          · simpa [LimbMul.inner, Large.fillMem, one] using memory
        · have again : s.regs.rbx.toBitVec + 1 ≠ s.regs.r13.toBitVec := by
            rw [rbx, r13]
            bv_omega
          simp only [again, ite_false]
          apply ih (by omega) (column+1) words old (by omega)
            (by simp only [List.length_cons] at wordsLength; omega)
            (by simp only [List.length_cons] at oldLength; omega)
            (by simp only [List.length_cons] at bufferLength; omega)
            (by simp only [List.length_cons] at sourceLength; omega)
            t factor one.2 (LimbMul.step_carry_lt _ _ _ _ carryBound)
          · simpa only [stable.rsi] using rsi
          · simpa only [stable.r10] using r10
          · simpa only [stable.rcx] using rcx
          · simpa only [stable.r13] using r13
          · simpa only [stable.r14] using r14
          · simpa only [stable.r15] using r15
          · exact index
          · exact carried
          · exact tZero
          · rw [memory]
            exact ReadAt.store_disjoint sourceRead.tail apart
              (by simp only [List.length_cons] at sourceLength; omega)
              (by omega) one.1
          · rw [memory]
            have shifted : row+(column+1) = row+column+1 := by omega
            rw [shifted]
            exact ReadAt.store_before oldRead.tail
              (by simp only [List.length_cons] at bufferLength; omega) one.1
          intro final finalStable finalIndex finalCarry finalZero finalMemory
          apply next final (stable.trans finalStable) finalIndex
          · simpa [LimbMul.inner, one] using finalCarry
          · exact finalZero
          · simpa [LimbMul.inner, Large.fillMem, one, memory,
              show row+(column+1) = row+column+1 by omega] using finalMemory

end SszX86.NatMul.Product

import SszX86.NatMulLoopRow

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

/-- Every actual outer iteration is executed. The final words are the checked
nativeRows recurrence, while the byte frame excludes precisely this live suffix. -/
theorem outer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (leftPointer source dst : BitVec 64) (leftPhysical rightPhysical leftCount : Nat)
    (right : List (BitVec 64))
    (leftApart : Large.Disjoint leftPointer dst (8*leftPhysical) (8*(leftCount+right.length)))
    (rightApart : Large.Disjoint source dst (8*rightPhysical) (8*(leftCount+right.length)))
    (span : dst.toNat+8*(leftCount+right.length) ≤ 2^64)
    (leftBound : leftPhysical < 2^64) (leftFits : leftCount ≤ leftPhysical)
    (rightFits : right.length ≤ rightPhysical) (rightPositive : 0 < right.length)
    (nonzero : leftPointer ≠ 0) (P : MachineState → Prop) :
    ∀ remaining, 0 < remaining → ∀ row (left buffer : List (BitVec 64)),
    row+remaining = leftCount → left.length = remaining →
    row+buffer.length = leftCount+right.length → ∀ s : MachineData,
    s.regs.rsp.toBitVec.toNat+24 ≤ 2^64 →
    Body.Apart s.regs.rsp.toBitVec.toNat 24 dst.toNat (8*(leftCount+right.length)) →
    s.regs.rsi.toBitVec = source →
    s.regs.r10.toBitVec = dst + BitVec.ofNat 64 (8*row) →
    s.regs.r12.toBitVec = BitVec.ofNat 64 leftCount →
    s.regs.r13.toBitVec = BitVec.ofNat 64 right.length →
    s.regs.r14.toBitVec = BitVec.ofNat 64 (leftCount+right.length) →
    s.regs.r15.toBitVec = BitVec.ofNat 64 row →
    Locals s.dmem s.regs.rsp.toBitVec leftPointer (BitVec.ofNat 64 leftPhysical) dst →
    ReadAt s.dmem leftPointer row left → ReadAt s.dmem source 0 right →
    ReadAt s.dmem dst row buffer → Large.Mapped s.dmem dst (8*(leftCount+right.length)) →
    (∀ t, OuterStable s t →
      t.regs.r10.toBitVec = dst + BitVec.ofNat 64 (8*leftCount) →
      t.regs.r15.toBitVec = BitVec.ofNat 64 leftCount →
      ReadAt t.dmem dst row (LimbMul.nativeRows left right buffer) →
      RowFrame s.dmem t.dmem dst row buffer.length →
      Large.Mapped t.dmem dst (8*(leftCount+right.length)) →
      Eventually (step e) P (t, base+664)) →
    Eventually (step e) P (s, base+512) := by
  intro remaining
  induction remaining with
  | zero => intro positive; omega
  | succ remaining ih =>
    intro positive row left buffer rowsEnd leftLength bufferLength s stackSpan stackApart
      rsi r10 r12 r13 r14 r15 locals leftRead rightRead bufferRead hmapped next
    cases left with
    | nil => simp only [List.length_nil] at leftLength; omega
    | cons factor left =>
      have rowBound : row < leftCount := by omega
      apply row_cps e base hc s leftPointer source dst leftPhysical rightPhysical leftCount
        row right buffer factor rightApart span stackSpan stackApart leftBound leftFits
        rightFits rightPositive rowBound bufferLength nonzero rsi r10 r12 r13 r14 r15
        locals leftRead.head rightRead bufferRead hmapped P
      intro t stable tPointer tIndex tMemory
      let updated := LimbMul.nativeRow factor right buffer
      have updateLength : updated.length = buffer.length :=
        nativeRow_length factor right buffer (by omega)
      have rowFrame : RowFrame s.dmem t.dmem dst row buffer.length := by
        rw [tMemory]
        exact rowFrame_fill _ _ _ _ _ (by rw [LimbMul.row_length]; omega)
      have bufferFrame := rowFrame.to_buffer span (by omega : row+buffer.length ≤ leftCount+right.length)
      have updatedRead : ReadAt t.dmem dst row updated := by
        rw [tMemory]
        exact ReadAt.nativeRow _ _ _ _ _ _ bufferRead (by omega) (by omega)
      have tMapped : Large.Mapped t.dmem dst (8*(leftCount+right.length)) := by
        rw [tMemory]
        exact fill_mapped _ _ _ _ _ hmapped
      cases updatedEq : updated with
      | nil => simp only [updatedEq, List.length_nil] at updateLength; omega
      | cons first rest =>
        have updatedWords : LimbMul.nativeRow factor right buffer = first::rest := updatedEq
        have updatedRead' : ReadAt t.dmem dst row (first::rest) := by
          simpa only [updatedEq] using updatedRead
        have restLength : row+1+rest.length = leftCount+right.length := by
          simp only [updatedEq, List.length_cons] at updateLength
          omega
        by_cases last : remaining = 0
        · subst remaining
          have done : row+1 = leftCount := by omega
          simp only [done, ite_true]
          have leftEmpty : left = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at leftLength
            omega
          apply next t stable
          · simpa only [done] using tPointer
          · simpa only [done] using tIndex
          · simpa [LimbMul.nativeRows, leftEmpty, updatedWords] using updatedRead'
          · exact rowFrame
          · exact tMapped
        · have again : row+1 ≠ leftCount := by omega
          simp only [again, ite_false]
          apply ih (by omega) (row+1) left rest (by omega)
            (by simp only [List.length_cons] at leftLength; omega) restLength t
          · simpa only [stable.rsp] using stackSpan
          · simpa only [stable.rsp] using stackApart
          · simpa only [stable.rsi] using rsi
          · exact tPointer
          · simpa only [stable.r12] using r12
          · simpa only [stable.r13] using r13
          · simpa only [stable.r14] using r14
          · exact tIndex
          · simpa only [stable.rsp] using locals.preserve bufferFrame stackSpan stackApart
          · exact (rowFrame.read_disjoint leftRead leftApart (by omega)
              (by simp only [List.length_cons] at leftLength ⊢; omega)).tail
          · exact rowFrame.read_disjoint rightRead rightApart (by omega) (by omega)
          · exact updatedRead'.tail
          · exact tMapped
          intro final finalStable finalPointer finalIndex finalRead finalFrame finalMapped
          apply next final (stable.trans finalStable) finalPointer finalIndex
          · have head := updatedRead'.head
            rw [← finalFrame.head (by omega)] at head
            have combined := ReadAt.cons head finalRead
            simpa [LimbMul.nativeRows, updatedWords] using combined
          · exact rowFrame.trans (finalFrame.widen (by omega) (by omega))
          · exact finalMapped

end SszX86.NatMul.Product

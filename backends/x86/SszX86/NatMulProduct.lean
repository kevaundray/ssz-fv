import SszX86.NatMulLoopOuter

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

theorem ReadAt.take {m : DataMem} {pointer : BitVec 64} {index : Nat}
    {words : List (BitVec 64)} (read : ReadAt m pointer index words) (count : Nat) :
    ReadAt m pointer index (words.take count) := by
  intro j
  have bound : j.val < words.length := by have := j.isLt; simp only [List.length_take] at this; omega
  simpa using read ⟨j.val, bound⟩

theorem ReadAt.to_wordsAt {m : DataMem} {pointer : BitVec 64} {words : List (BitVec 64)}
    (read : ReadAt m pointer 0 words) : NatMemory.wordsAt (widthLoad m) pointer.toNat words := by
  intro j
  unfold widthLoad
  rw [width_address]
  have loaded := read j
  simp only [Nat.zero_add] at loaded
  simp [loaded]

/-- PC512 through PC664 on the original allocating branch. The only destination
value premise is its CURRENT zero-filled contents, supplied by the real memset.
The output and its precise byte frame are consequences of actual finite loops. -/
theorem product_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (leftPointer rightPointer dst : BitVec 64)
    (leftWords rightWords : List (BitVec 64))
    (leftAt : (NatOperand.large leftPointer leftWords).At (widthLoad s.dmem))
    (rightAt : (NatOperand.large rightPointer rightWords).At (widthLoad s.dmem))
    (leftPositive : 0 < Limbs.sigWords leftWords) (rightPositive : 0 < Limbs.sigWords rightWords)
    (span : dst.toNat+8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords) ≤ 2^64)
    (leftApart : Large.Disjoint leftPointer dst (8*leftWords.length)
      (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)))
    (rightApart : Large.Disjoint rightPointer dst (8*rightWords.length)
      (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)))
    (stackSpan : s.regs.rsp.toBitVec.toNat+24 ≤ 2^64)
    (stackApart : Body.Apart s.regs.rsp.toBitVec.toNat 24 dst.toNat
      (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)))
    (rsi : s.regs.rsi.toBitVec = rightPointer) (r10 : s.regs.r10.toBitVec = dst)
    (r12 : s.regs.r12.toBitVec = BitVec.ofNat 64 (Limbs.sigWords leftWords))
    (r13 : s.regs.r13.toBitVec = BitVec.ofNat 64 (Limbs.sigWords rightWords))
    (r14 : s.regs.r14.toBitVec = BitVec.ofNat 64 (Limbs.sigWords leftWords+Limbs.sigWords rightWords))
    (r15 : s.regs.r15.toBitVec = 0#64)
    (locals : Locals s.dmem s.regs.rsp.toBitVec leftPointer (BitVec.ofNat 64 leftWords.length) dst)
    (zero : NatMemory.wordsAt (widthLoad s.dmem) dst.toNat
      (List.replicate (Limbs.sigWords leftWords+Limbs.sigWords rightWords) 0))
    (hmapped : Large.Mapped s.dmem dst (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)))
    (P : MachineState → Prop)
    (next : ∀ t, OuterStable s t →
      t.regs.r10.toBitVec = dst+BitVec.ofNat 64 (8*Limbs.sigWords leftWords) →
      t.regs.r15.toBitVec = BitVec.ofNat 64 (Limbs.sigWords leftWords) →
      NatMemory.wordsAt (widthLoad t.dmem) dst.toNat
        (SszNative.NatMul.writtenWords (.large leftPointer leftWords) (.large rightPointer rightWords)) →
      BufferFrame s.dmem t.dmem dst.toNat
        (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)) →
      Large.Mapped t.dmem dst (8*(Limbs.sigWords leftWords+Limbs.sigWords rightWords)) →
      Eventually (step e) P (t, base+664)) :
    Eventually (step e) P (s, base+512) := by
  have leftFits := Limbs.sigWords_le_length leftWords
  have rightFits := Limbs.sigWords_le_length rightWords
  have leftLength : (leftWords.take (Limbs.sigWords leftWords)).length = Limbs.sigWords leftWords := by
    simp only [List.length_take, Nat.min_eq_left leftFits]
  have rightLength : (rightWords.take (Limbs.sigWords rightWords)).length = Limbs.sigWords rightWords := by
    simp only [List.length_take, Nat.min_eq_left rightFits]
  have leftBound : leftWords.length < 2^64 := by have := leftAt.2.2.1; omega
  have nonzero : leftPointer ≠ 0#64 := by intro eq; have := leftAt.1; simp [eq] at this
  apply outer_cps e base hc leftPointer rightPointer dst leftWords.length rightWords.length
    (Limbs.sigWords leftWords) (rightWords.take (Limbs.sigWords rightWords))
    (by simpa only [rightLength] using leftApart)
    (by simpa only [rightLength] using rightApart)
    (by simpa only [rightLength] using span) leftBound leftFits
    (by simpa only [rightLength] using rightFits)
    (by simpa only [rightLength] using rightPositive) nonzero P
    (Limbs.sigWords leftWords) leftPositive 0 (leftWords.take (Limbs.sigWords leftWords))
    (List.replicate (Limbs.sigWords leftWords+Limbs.sigWords rightWords) 0)
    (by omega) leftLength (by simp [rightLength]) s stackSpan
    (by simpa only [rightLength] using stackApart) rsi
    (by simpa using r10) r12 (by simpa only [rightLength] using r13)
    (by simpa only [rightLength] using r14) r15 locals
    ((ReadAt.of_wordsAt leftAt.2.2.2).take _) ((ReadAt.of_wordsAt rightAt.2.2.2).take _)
    (ReadAt.of_wordsAt zero) (by simpa only [rightLength] using hmapped)
  intro t stable tPointer tIndex written frame finalMapped
  apply next t stable tPointer tIndex
  · rw [SszNative.NatMul.writtenWords_native_loop]
    exact written.to_wordsAt
  · exact frame.to_buffer span (by simp)
  · simpa only [rightLength] using finalMapped

end SszX86.NatMul.Product

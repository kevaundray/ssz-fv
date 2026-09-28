import SszX86.EmitBodyOwned
import SszX86.EmitUintModel

namespace SszX86.Emit
open SszNative SszNative.Serialize UintCodec

/-- Both complete original Nat representations survive the six stack writes;
no normalization or successful scan state is assumed. -/
theorem AtBody.uint_owned {s t : MachineData} {base : Int64}
    {logicalWidth number : NatOperand} {buffer ra : BitVec 64} {written : Nat}
    (h : AtBody s t)
    (owned : Owned s base (.uint logicalWidth) (.uint number) buffer ra written)
    (tag : BodyTag (.uint logicalWidth) (.uint number) t) :
    Uint.Owned t logicalWidth number written := by
  have widthHeader : ∀ a, InSpan a (s.regs.rsi.toBitVec + 8) 16 →
      Borrowed s (.uint logicalWidth) (.uint number) buffer a := by
    intro a inside
    left
    exact span_shift _ 8 16 24 (by decide) inside
  have numberHeader : ∀ a, InSpan a (s.regs.rdx.toBitVec + 8) 16 →
      Borrowed s (.uint logicalWidth) (.uint number) buffer a := by
    intro a inside
    right; left
    exact span_shift _ 8 16 24 (by decide) inside
  refine {
    tag := tag.2 (by dsimp only [descTag]; decide)
    widthAt := ?_
    numberAt := ?_
    valid := owned.valid.success
    capacity := ?_
    width_bound := ?_
    number_bound := ?_
    output_bound := ?_
    result_bound := ?_
    output := h.output_mapped owned
    result := h.result_mapped owned
    apart := ?_
    readonly := ?_ }
  · rw [h.memory, h.descriptorPointer]
    exact owned.saved_nat _ logicalWidth widthHeader
      (fun _ inside => Or.inr (Or.inr (Or.inl inside))) owned.descriptor.2
  · rw [h.memory, h.valuePointer]
    exact owned.saved_nat _ number numberHeader
      (fun _ inside => Or.inr (Or.inr (Or.inr inside))) owned.valueStored.2
  · rw [h.capacity]
    exact owned.valid.fits
  · rw [h.descriptorPointer]
    exact owned.descriptorBound
  · rw [h.valuePointer]
    exact owned.valueBound
  · rw [h.output]
    have physical := owned.outputBound
    have fits := owned.valid.fits
    omega
  · rw [h.result]
    have physical := owned.resultBound
    omega
  · intro a inOutput inResult
    obtain ⟨i, hi, output⟩ := inOutput
    obtain ⟨j, hj, result⟩ := inResult
    exact h.output_result owned i hi j hj (output.symm.trans result)
  · intro a borrowed writable
    have original : Borrowed s (.uint logicalWidth) (.uint number) buffer a := by
      rcases borrowed with fromWidth | fromNumber
      · rcases fromWidth with header | limbs
        · apply widthHeader a
          simpa only [h.descriptorPointer] using header
        · exact Or.inr (Or.inr (Or.inl limbs))
      · rcases fromNumber with header | limbs
        · apply numberHeader a
          simpa only [h.valuePointer] using header
        · exact Or.inr (Or.inr (Or.inr limbs))
    apply h.readonly owned a original
    rcases writable with output | result
    · exact Or.inl output
    · exact Or.inr (Or.inl result)

end SszX86.Emit

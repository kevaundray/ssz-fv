import SszX86.CodecSerializePublish
import SszX86.CodecMeasureCore

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec
open SszX86.Serialize.Publish

/-- The copied image occupies exactly the native 72-byte result object. -/
theorem copy_image72 (m : DataMem) (out : BitVec 64) (image : Image)
    (bound : out.toNat + 72 ≤ 2^64) : ImageAt (copyMem m out image) out image := by
  constructor <;> simp (disch := first | assumption | omega | decide) only
    [copyMem, BoolCodec.load_store_offset_disjoint, load_store_word]

theorem copied_error (s : MachineData) (image : Image) (flags : StatusFlags)
    (reason : SszNative.Codec.Error)
    (source : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (bound : s.regs.rbx.toNat + 72 ≤ 2^64)
    (stored : Codec.ErrorAt (widthLoad s.dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat reason)
    (safe : ∀ a, Codec.ErrorBorrows reason a →
      ¬ (Emit.InSpan a s.regs.rbx.toBitVec 72 ∨
        Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 16)) :
    Codec.ErrorAt (widthLoad (copied s image flags).dmem) s.regs.rbx.toNat reason := by
  exact Codec.ErrorAt.transport s.dmem (copied s image flags).dmem _ _ image reason _
    source (copy_image72 _ _ image bound) (copied_frame s image flags) safe stored

/-- The original wrapper reads all five Plan words, including retained child
pointer/count and leading size, rather than silently substituting a leaf Plan. -/
theorem image_plan (m : DataMem) (p : BitVec 64) (image : Image)
    (plan : SszNative.CodecMeasure.Plan) (source : ImageAt m p image)
    (result : CodecMeasure.ResultAt (widthLoad m) p.toNat (.ok plan)) :
    image.tag = 0 ∧ image.w0.toNat = plan.childrenPointer ∧
      image.w1.toNat = plan.children.length ∧ image.w2 = plan.size.pointer ∧
      image.w3 = plan.size.payload ∧ image.w4.toNat = plan.leading ∧
      plan.size.At (widthLoad m) := by
  have seen := source.observed
  rcases result with ⟨⟨h0,h1,h2,h3,h4⟩, borrowed, ht⟩
  have eq0 := Option.some.inj (seen.w0.symm.trans h0)
  have eq1 := Option.some.inj (seen.w1.symm.trans h1)
  have eq2 := Option.some.inj (seen.w2.symm.trans h2)
  have eq3 := Option.some.inj (seen.w3.symm.trans h3)
  have eq4 := Option.some.inj (seen.w4.symm.trans h4)
  have eqt := Option.some.inj (seen.tag.symm.trans ht)
  refine ⟨BitVec.eq_of_toNat_eq ?_, eq0, eq1,
    BitVec.eq_of_toNat_eq eq2, BitVec.eq_of_toNat_eq eq3, eq4, borrowed⟩
  simpa only [BitVec.toNat_zero] using eqt

/-- Actual stack repacking preserves the complete scalar Plan and supplies the
original Nat representation to the native host-size loop. Recursive child
storage is transported separately across the same exact write frame. -/
theorem prepared_result (s : MachineData) (image : Image) (flags : StatusFlags)
    (plan : SszNative.CodecMeasure.Plan)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (source : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (result : CodecMeasure.ResultAt (widthLoad s.dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat (.ok plan))
    (safe : ∀ a, Emit.NatBorrowed plan.size a →
      ¬ Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 56) :
    CodecMeasure.ResultAt (widthLoad (prepared s image flags).dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat (.ok plan) ∧
      (prepared s image flags).regs.rax.toBitVec = plan.size.pointer ∧
      (prepared s image flags).regs.r9.toBitVec = plan.size.payload := by
  obtain ⟨tag,h0,h1,h2,h3,h4,borrowed⟩ := image_plan _ _ image plan source result
  have new := (prepared_state_image s image flags bound source).observed
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩,
    prepared_operand s image flags plan.size borrowed safe, ?_⟩, ?_, ?_⟩
  · exact new.w0.trans (congrArg some h0)
  · exact new.w1.trans (congrArg some h1)
  · simpa only [h2] using new.w2
  · simpa only [h3] using new.w3
  · exact new.w4.trans (congrArg some h4)
  · simpa only [tag, BitVec.toNat_zero] using new.tag
  · simpa only [prepared, tested, loaded, UInt64.toBitVec_ofBitVec] using h2
  · simpa only [prepared, tested, loaded, UInt64.toBitVec_ofBitVec] using h3

end SszX86.CodecSerialize.Publish

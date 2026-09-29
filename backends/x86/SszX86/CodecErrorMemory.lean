import SszX86.CodecError
import SszX86.SerializePublishSemantic

namespace SszX86.Codec
open SszNative
open SszNative.Codec (Error)
open Serialize.Publish

/-- Copying a native Error copies every active scalar without constraining its
four trailing padding bytes. The borrowed Nat limbs remain elsewhere. -/
theorem ErrorAt.transport (before after : DataMem) (src dst : BitVec 64)
    (image : Image) (reason : Error) (writable : BitVec 64 → Prop)
    (source : ImageAt before src image) (destination : ImageAt after dst image)
    (frame : Emit.MemoryFrame before after writable)
    (safe : ∀ a, ErrorBorrows reason a → ¬ writable a)
    (stored : ErrorAt (widthLoad before) src.toNat reason) :
    ErrorAt (widthLoad after) dst.toNat reason := by
  have old := source.observed
  have new := destination.observed
  rcases stored with ⟨h0, h1, ⟨h2, h3, he⟩, ⟨h4, h5, ha⟩, h6, h7, ht⟩
  simp only [Nat.add_assoc] at h3 h5
  refine ⟨new.w0.trans (old.w0.symm.trans h0),
    new.w1.trans (old.w1.symm.trans h1),
    ⟨new.w2.trans (old.w2.symm.trans h2), ?_, ?_⟩,
    ⟨new.w4.trans (old.w4.symm.trans h4), ?_, ?_⟩,
    new.w6.trans (old.w6.symm.trans h6),
    new.w7.trans (old.w7.symm.trans h7), new.tag.trans (old.tag.symm.trans ht)⟩
  · simpa only [Nat.add_assoc] using new.w3.trans (old.w3.symm.trans h3)
  · exact Measure.operand_frame before after writable frame (errorFirst reason)
      (fun a h => safe a (Or.inl h)) he
  · simpa only [Nat.add_assoc] using new.w5.trans (old.w5.symm.trans h5)
  · exact Measure.operand_frame before after writable frame (errorSecond reason)
      (fun a h => safe a (Or.inr h)) ha

theorem ErrorAt.image_nonzero {m : DataMem} {p : BitVec 64} {image : Image}
    {reason : Error} (physical : ImageAt m p image)
    (stored : ErrorAt (widthLoad m) p.toNat reason) : image.tag ≠ 0 := by
  have tag := Option.some.inj (physical.observed.tag.symm.trans stored.tag)
  intro zero
  have code : errorCode reason = 0 := by simpa only [zero, BitVec.toNat_zero] using tag.symm
  exact errorCode_ne_zero reason code

end SszX86.Codec

import SszX86.CodecMeasureFixedCore
import SszX86.SerializePublishSemantic

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- None constrains only its discriminant and status. The inactive Nat payload
and final padding stay arbitrary concrete bytes of the original mapped image. -/
theorem image_none (m : DataMem) (p : BitVec 64) (v : Serialize.Publish.Image)
    (image : Serialize.Publish.ImageAt m p v)
    (observed : ResultAt (widthLoad m) p.toNat (.ok none)) :
    v.tag = 0 ∧ v.w0 = 0 := by
  have seen := image.observed
  have option := Option.some.inj (seen.w0.symm.trans observed.1)
  have tag := Option.some.inj (seen.tag.symm.trans observed.2)
  exact ⟨BitVec.eq_of_toNat_eq (by simpa using tag),
    BitVec.eq_of_toNat_eq (by simpa using option)⟩

theorem image_some (m : DataMem) (p : BitVec 64) (v : Serialize.Publish.Image)
    (width : NatOperand) (image : Serialize.Publish.ImageAt m p v)
    (observed : ResultAt (widthLoad m) p.toNat (.ok (some width))) :
    v.tag = 0 ∧ v.w0 = 1 ∧ v.w1 = width.pointer ∧ v.w2 = width.payload ∧
      width.At (widthLoad m) := by
  have seen := image.observed
  rcases observed with ⟨option, ⟨pointer, payload, limbs⟩, status⟩
  simp only [Nat.add_assoc] at payload
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w1.symm.trans pointer)),
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w2.symm.trans payload)), limbs⟩
  · simpa using Option.some.inj (seen.tag.symm.trans status)
  · simpa using Option.some.inj (seen.w0.symm.trans option)

theorem image_error (m : DataMem) (p : BitVec 64) (v : Serialize.Publish.Image)
    (reason : SszNative.Serialize.Error) (image : Serialize.Publish.ImageAt m p v)
    (observed : ResultAt (widthLoad m) p.toNat (.error reason)) : v.tag ≠ 0 :=
  Serialize.Publish.image_error_tag m p v reason image observed

/-- The exact arithmetic success image used at PC201/586. -/
theorem image_arithmetic (m : DataMem) (p : BitVec 64) (v : Serialize.Publish.Image)
    (width : NatOperand) (image : Serialize.Publish.ImageAt m p v)
    (observed : NatArithmetic.AddResultAt (widthLoad m) p.toNat (.ok width)) :
    v.tag = 0 ∧ v.w0 = width.pointer ∧ v.w1 = width.payload ∧ width.At (widthLoad m) := by
  have seen := image.observed
  rcases observed with ⟨⟨pointer, payload, limbs⟩, status⟩
  refine ⟨BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w0.symm.trans pointer)),
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w1.symm.trans payload)), limbs⟩
  simpa using Option.some.inj (seen.tag.symm.trans status)

/-- Quotient and remainder are both recovered from the concrete helper output. -/
theorem image_division (m : DataMem) (p : BitVec 64) (v : Serialize.Publish.Image)
    (quotient : NatOperand) (remainder : BitVec 64) (image : Serialize.Publish.ImageAt m p v)
    (observed : NatArithmetic.DivisionResultAt (widthLoad m) p.toNat (.ok (quotient, remainder))) :
    v.tag = 0 ∧ v.w0 = quotient.pointer ∧ v.w1 = quotient.payload ∧
      v.w2 = remainder ∧ quotient.At (widthLoad m) := by
  have seen := image.observed
  rcases observed with ⟨⟨pointer, payload, limbs⟩, remainderLoad, status⟩
  refine ⟨BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w0.symm.trans pointer)),
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w1.symm.trans payload)),
    BitVec.eq_of_toNat_eq (Option.some.inj (seen.w2.symm.trans remainderLoad)), limbs⟩
  simpa using Option.some.inj (seen.tag.symm.trans status)

end SszX86.CodecMeasureFixed

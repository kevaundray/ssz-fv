import SszX86.CodecMeasureFixedOutputCopyFacts

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec Serialize.Publish

/-- Only active arithmetic-error fields are fixed. Padding stays unconstrained. -/
def ArithmeticErrorImage (reason : NatArithmetic.Failure) (v : Image) : Prop :=
  v.w0 = 1 ∧ v.w1 = 0 ∧ v.w2 = 0 ∧ v.w3 = 0 ∧
  v.w4 = 0 ∧ v.w5 = 0 ∧ v.w6 = 0 ∧ v.w7 = 0 ∧
  v.tag.toNat = (match reason with | .scratchExhausted => 32768 | .badRepresentation => 32770)

theorem arithmetic_image_observed (m : DataMem) (out : BitVec 64)
    (v : Image) (reason : NatArithmetic.Failure) (image : ImageAt m out v)
    (active : ArithmeticErrorImage reason v) :
    ResultAt (widthLoad m) out.toNat (.error (.arithmetic reason)) := by
  have observe (off n : Nat) (value : Int)
      (loaded : Mem.loadInt m (out + BitVec.ofNat 64 off) n = some value) :
      widthLoad m (out.toNat + off) n = some value.toNat := by
    unfold widthLoad
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, loaded]
    rfl
  rcases active with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht⟩
  have l0 := observe 0 8 _ image.w0
  have l1 := observe 8 8 _ image.w1
  have l2 := observe 16 8 _ image.w2
  have l3 := observe 24 8 _ image.w3
  have l4 := observe 32 8 _ image.w4
  have l5 := observe 40 8 _ image.w5
  have l6 := observe 48 8 _ image.w6
  have l7 := observe 56 8 _ image.w7
  have lt := observe 64 4 _ image.tag
  simpa only [ResultAt, Measure.ErrorAt, NatArithmetic.errorAt,
    h0, h1, h2, h3, h4, h5, h6, h7, ht,
    Int.toNat_natCast, BitVec.toNat_ofNat, Nat.zero_add, Nat.add_zero]
    using And.intro l0 (And.intro l1 (And.intro l2 (And.intro l3
      (And.intro l4 (And.intro l5 (And.intro l6 (And.intro l7 lt)))))))

end SszX86.CodecMeasureFixed.Output

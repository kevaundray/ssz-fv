import SszX86.MeasureBitsArithmetic
import SszNatNarrow
import SszWidth

namespace SszX86.Measure.Bits
open SszNative

/-- The vector compares both count words, with no truncation to a machine usize. -/
theorem vector_pair_words (words : List (BitVec 64)) (count : BitVec 128)
    (fits : Limbs.sigWords words ≤ 2) :
    (words[0]?.getD 0#64 = count.setWidth 64 ∧
      words[1]?.getD 0#64 = (count >>> 64).setWidth 64) ↔
    Limbs.value words = count.toNat := by
  have widthValue : Limbs.value words =
      (words[0]?.getD 0#64).toNat + 2^64 * (words[1]?.getD 0#64).toNat :=
    Limbs.width_two_value words fits
  rw [widthValue, ← count_pair count]
  have lo := (words[0]?.getD 0#64).isLt
  have hi := (words[1]?.getD 0#64).isLt
  have clo := (count.setWidth 64).isLt
  have chi := ((count >>> 64).setWidth 64).isLt
  simp only [← BitVec.toNat_inj, Uint.pairValue]
  omega

theorem vector_many_ne (pointer : BitVec 64) (words : List (BitVec 64))
    (count : BitVec 128) (large : 2 < Limbs.sigWords words) :
    Limbs.value words ≠ count.toNat := by
  intro same
  have fits := (NatOperand.wordCount_le_iff_value_lt (.large pointer words) 2).2
    (show (.large pointer words : NatOperand).value < 2^(64*2) by
      simpa only [NatOperand.value, NatOperand.words, same, Nat.reduceMul] using count.isLt)
  change Limbs.sigWords words ≤ 2 at fits
  omega

theorem small_count_words (limb : BitVec 64) (count : BitVec 128) :
    (limb = count.setWidth 64 ∧ 0#64 = (count >>> 64).setWidth 64) ↔
    limb.toNat = count.toNat := by
  have h := vector_pair_words [limb] count
    (by have bound := Limbs.sigWords_le_length [limb]; simp only [List.length_cons, List.length_nil] at bound; omega)
  simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil, Option.getD_some, Option.getD_none, Limbs.value,
    Nat.mul_zero, Nat.add_zero] using h

end SszX86.Measure.Bits

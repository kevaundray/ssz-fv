import SszIndicesPathsRefinement
import SszIndicesPowerSemanticPaths
import SszIndicesArithmeticSemanticWords
import SszNatShiftSemantics
import SszIndicesPhysical

set_option autoImplicit false

namespace SszNative.Indices

/-- The packed fast path reads only the low limb, but keeps exactly the low
packing bits of the full, possibly noncanonical, natural operand. -/
theorem packed_start_value (position width : NatOperand) (shift : Nat)
    (packed : packingShift width = some shift) :
    ((word position 0 &&& lowMask shift) <<< (5 - shift)).toNat =
      position.value * width.value % 32 := by
  obtain ⟨shiftBound, widthEq⟩ := packingShift_spec width shift packed
  have maskEq : (word position 0 &&& lowMask shift).toNat = position.value % 2^shift := by
    rw [BitVec.toNat_and, lowMask_toNat shift (by omega), word_toNat]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have widthPositive : 0 < width.value := by rw [widthEq]; exact Nat.two_pow_pos _
  have widthProduct := packed_width_identity width shift packed
  have startBound : position.value % 2^shift * width.value < 32 := by
    rw [← widthProduct]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) widthPositive
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, maskEq, ← widthEq,
    Nat.mod_eq_of_lt (by omega : position.value % 2^shift * width.value < 2^64)]
  rw [← widthProduct, Nat.mul_mod_mul_right]

/-- The stop-word addition cannot wrap: even invalid declarations enter the
packed branch only at widths 1, 2, 4, 8, 16, or 32. -/
theorem packed_stop_value (position width : NatOperand) (shift : Nat)
    (packed : packingShift width = some shift) :
    (((word position 0 &&& lowMask shift) <<< (5 - shift)) +
      ((1 : BitVec 64) <<< (5 - shift))).toNat =
      position.value * width.value % 32 + width.value := by
  obtain ⟨shiftBound, widthEq⟩ := packingShift_spec width shift packed
  have widthProduct := packed_width_identity width shift packed
  have widthBound : width.value ≤ 32 := by
    rw [widthEq]
    change 2 ^ (5 - shift) ≤ 2 ^ 5
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (Nat.sub_le 5 shift)
  have endBound : position.value * width.value % 32 + width.value ≤ 32 := by
    rw [← widthProduct, Nat.mul_mod_mul_right]
    simpa only [Nat.succ_mul] using
      Nat.mul_le_mul_right width.value
        (Nat.succ_le_of_lt (Nat.mod_lt position.value (Nat.two_pow_pos shift)))
  have shifted : ((1 : BitVec 64) <<< (5 - shift)).toNat = width.value := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (1 * 2 ^ (5 - shift)) % 2 ^ 64 = width.value
    rw [Nat.one_mul, ← widthEq, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, packed_start_value position width shift packed, shifted,
    Nat.mod_eq_of_lt (by omega)]

theorem unpackedPosition_refines (position width : NatOperand)
    (base capacity used : Nat) :
    PathRefines ChunkPosition.erase (unpackedPosition position width base capacity used).result
      (.ok ⟨position.value * width.value / 32,
        position.value * width.value % 32,
        position.value * width.value % 32 + width.value⟩) := by
  unfold unpackedPosition
  apply PathRefines.bind _ _ NatOperand.value ChunkPosition.erase
    (.ok (position.value * width.value))
    (fun product => .ok ⟨product / 32, product % 32, product % 32 + width.value⟩)
  · exact PathRefines.arithmetic _ _ _
      (NatMul.run_value position width base capacity used)
  · intro product returned
    apply PathRefines.bind _ _ (fun pair => (pair.1.value, pair.2.toNat)) ChunkPosition.erase
      (.ok (product.value / 32, product.value % 32))
      (fun divided => .ok ⟨divided.1, divided.2, divided.2 + width.value⟩)
    · apply PathRefines.arithmetic
      intro divided dividedEq
      obtain ⟨quotientEq, remainderEq, _⟩ :=
        NatDivision.run_success product 32 base capacity _ divided dividedEq
      exact Prod.ext quotientEq remainderEq
    · intro divided dividedEq
      apply PathRefines.bind _ _ NatOperand.value ChunkPosition.erase
        (.ok ((NatOperand.small divided.2).value + width.value))
        (fun stop => .ok ⟨divided.1.value, divided.2.toNat, stop⟩)
      · exact PathRefines.arithmetic _ _ _ (NatAdd.run_value (.small divided.2) width
          base capacity _)
      · intro stop stopEq
        exact PathRefines.ok _ _

 theorem sequencePosition_refines (shape : Codec.Desc) (position width : NatOperand)
    (base capacity used : Nat) :
    PathRefines ChunkPosition.erase (sequencePosition shape position width base capacity used).result
      (.ok (match shape with
        | .primitive (.bitVector _) | .primitive (.bitList _)
        | .primitive (.progressiveBitList _) => ⟨position.value / 256, 0, 0⟩
        | _ => ⟨position.value * width.value / 32, position.value * width.value % 32,
            position.value * width.value % 32 + width.value⟩)) := by
  have bitsCase : ∀ used,
      PathRefines ChunkPosition.erase
        (bind (arithmetic used (NatShift.shr position 8 base capacity used))
          (fun chunk used => unchanged used (.ok ⟨chunk, .small 0, .small 0⟩))).result
        (.ok ⟨position.value / 256, 0, 0⟩) := by
    intro used
    apply PathRefines.bind _ _ NatOperand.value ChunkPosition.erase
      (.ok (position.value / 256)) (fun chunk => .ok ⟨chunk, 0, 0⟩)
    · apply PathRefines.arithmetic
      intro chunk success
      simpa only [Nat.shiftRight_eq_div_pow] using
        NatShift.shr_value position 8 base capacity used chunk success
    · intro chunk success
      exact PathRefines.ok _ _
  have bytesCase : ∀ used,
      PathRefines ChunkPosition.erase
        (match packingShift width with
        | some shift =>
            let start := (word position 0 &&& lowMask shift) <<< (5 - shift)
            bind (arithmetic used (NatShift.shr position shift base capacity used))
              (fun chunk used => unchanged used
                (.ok (⟨chunk, .small start, .small (start + (1 <<< (5 - shift)))⟩ : ChunkPosition)))
        | none => unpackedPosition position width base capacity used).result
        (.ok ⟨position.value * width.value / 32, position.value * width.value % 32,
          position.value * width.value % 32 + width.value⟩) := by
    intro used
    cases packed : packingShift width with
    | none => exact unpackedPosition_refines position width base capacity used
    | some shift =>
        apply PathRefines.bind _ _ NatOperand.value ChunkPosition.erase
          (.ok (position.value * width.value / 32))
          (fun chunk => .ok ⟨chunk, position.value * width.value % 32,
            position.value * width.value % 32 + width.value⟩)
        · apply PathRefines.arithmetic
          intro chunk success
          rw [NatShift.shr_value position shift base capacity used chunk success,
            Nat.shiftRight_eq_div_pow]
          exact packed_div_identity position.value width shift packed
        · intro chunk success
          apply PathRefines.of_eq
          simp only [unchanged, Except.map, eraseResult, ChunkPosition.erase, small_value]
          have incrementEq :
              BitVec.ofNat 64 ((1 : Nat) <<< (5 - shift)) =
                ((1 : BitVec 64) <<< (5 - shift)) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft] <;> rfl
          rw [BitVec.natCast_eq_ofNat, incrementEq,
            packed_start_value position width shift packed,
            packed_stop_value position width shift packed]
  cases shape with
  | primitive shape => cases shape <;> first | exact bitsCase used | exact bytesCase used
  | _ => exact bytesCase used

end SszNative.Indices

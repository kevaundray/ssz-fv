import SszArm.IndicesNatShrClz

set_option autoImplicit false

namespace SszArm.Indices.NatShr.Clz

/-- The input's 64-bit representation proves termination; no loop fuel or
future result premise is imposed on the caller. -/
theorem word (s : ArmState) (pc : BitVec 64) (value : BitVec 64)
    (code : CodeAt s pc) (error : read_err s = .None)
    (input : r (.GPR 9#5) s = value) (counter : r (.GPR 10#5) s = 64#64)
    (entry : read_pc s = if value = 0#64 then pc + 12#64 else pc) :
    ∃ t, run (3 * SszNative.Serialize.bitLength value.toNat) s = t ∧
      Measure.Uint.ClzFrame s t ∧ read_pc t = pc + 12#64 ∧
      r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 (64 - SszNative.Serialize.bitLength value.toNat) := by
  obtain ⟨bound, zero, before⟩ := Measure.Uint.bitLength_shift_facts value
  have widthZero : SszNative.Serialize.bitLength value.toNat = 0 ↔ value = 0#64 := by
    constructor
    · intro empty
      simpa only [empty, BitVec.ushiftRight_zero] using zero
    · intro empty
      simp [empty, SszNative.Serialize.bitLength]
  have loopEntry : read_pc s = if SszNative.Serialize.bitLength value.toNat = 0 then
      pc + 12#64 else pc := by
    simpa only [widthZero] using entry
  obtain ⟨t, executed, frame, returnedPC, returnedInput, returnedCounter⟩ :=
    loop pc (SszNative.Serialize.bitLength value.toNat) s code error loopEntry
      (by simpa only [input] using before) (by simpa only [input] using zero)
  refine ⟨t, executed, frame, returnedPC, returnedInput, ?_⟩
  rw [returnedCounter, counter]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Direct binding to the complete Nat::shr function image. -/
theorem shr_word (s : ArmState) (base : BitVec 64) (value : BitVec 64)
    (code : Linked.NatShr.CodeAt s base) (error : read_err s = .None)
    (input : r (.GPR 9#5) s = value) (counter : r (.GPR 10#5) s = 64#64)
    (entry : read_pc s = if value = 0#64 then base + 136#64 else base + 124#64) :
    ∃ t, run (3 * SszNative.Serialize.bitLength value.toNat) s = t ∧
      Measure.Uint.ClzFrame s t ∧ read_pc t = base + 136#64 ∧
      r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 (64 - SszNative.Serialize.bitLength value.toNat) := by
  simpa only [BitVec.add_assoc] using
    word s (base + 124#64) value (shr_code s base code) error input counter
      (by simpa only [BitVec.add_assoc] using entry)

/-- Direct binding to the complete ceil_shift function image. -/
theorem ceil_word (s : ArmState) (base : BitVec 64) (value : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (input : r (.GPR 9#5) s = value) (counter : r (.GPR 10#5) s = 64#64)
    (entry : read_pc s = if value = 0#64 then base + 216#64 else base + 204#64) :
    ∃ t, run (3 * SszNative.Serialize.bitLength value.toNat) s = t ∧
      Measure.Uint.ClzFrame s t ∧ read_pc t = base + 216#64 ∧
      r (.GPR 9#5) t = 0#64 ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 (64 - SszNative.Serialize.bitLength value.toNat) := by
  simpa only [BitVec.add_assoc] using
    word s (base + 204#64) value (ceil_code s base code) error input counter
      (by simpa only [BitVec.add_assoc] using entry)

end SszArm.Indices.NatShr.Clz

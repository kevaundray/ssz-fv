import SszArm.IndicesPrefixEqualClz

namespace SszArm.Indices.PrefixEqual.Clz

/-- Every physically observed 64-bit limb discharges the loop's termination
facts. This is independent of the logical size of the enclosing Nat. -/
theorem word (side : Side) (s : ArmState) (base : BitVec 64) (value : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (input : r (.GPR side.input) s = value)
    (counter : r (.GPR side.counter) s = 64#64)
    (pc : read_pc s = if value = 0#64 then
      base + BitVec.ofNat 64 (side.offset + 12) else base + BitVec.ofNat 64 side.offset) :
    ∃ t, run (3 * SszNative.Serialize.bitLength value.toNat) s = t ∧ Frame side s t ∧
      read_pc t = base + BitVec.ofNat 64 (side.offset + 12) ∧
      r (.GPR side.input) t = 0#64 ∧
      r (.GPR side.counter) t =
        BitVec.ofNat 64 (64 - SszNative.Serialize.bitLength value.toNat) := by
  obtain ⟨bound, zero, before⟩ := Measure.Uint.bitLength_shift_facts value
  have widthZero : SszNative.Serialize.bitLength value.toNat = 0 ↔ value = 0#64 := by
    constructor
    · intro empty
      simpa only [empty, BitVec.ushiftRight_zero] using zero
    · intro empty
      simp [empty, SszNative.Serialize.bitLength]
  have entry : read_pc s = if SszNative.Serialize.bitLength value.toNat = 0 then
      base + BitVec.ofNat 64 (side.offset + 12) else base + BitVec.ofNat 64 side.offset := by
    simpa only [widthZero] using pc
  obtain ⟨t, executed, frame, returnedPC, returnedInput, returnedCounter⟩ :=
    loop side base (SszNative.Serialize.bitLength value.toNat) s code error entry
      (by simpa only [input] using before) (by simpa only [input] using zero)
  refine ⟨t, executed, frame, returnedPC, returnedInput, ?_⟩
  rw [returnedCounter, counter]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end SszArm.Indices.PrefixEqual.Clz

import SszArm.BitVectorValueStore

namespace SszArm.BitVector.ValueTail

open UintCodec (widthLoad)

private theorem read_tag_prefix (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 4 address s = (read_mem_bytes 8 address s).setWidth 32 := by
  simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index within
  simp only [BitVec.getLsbD_setWidth,
    Memory.getLsbD_read_bytes (n := 4) (by decide),
    Memory.getLsbD_read_bytes (n := 8) (by decide)]
  simp [within, show index < 64 by omega]

/-- Read the actual low tag word, rather than assuming the native branch. -/
theorem u128_observed (s : ArmState) (count : BitVec 128)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 144) (some count)) :
    read_mem_bytes 4 (r (.GPR 31#5) s + 144#64) s = 1#32 ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) s = countLow count ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 168#64) s = countHigh count := by
  obtain ⟨tag, _, low, high⟩ := observed
  simp only [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
    Option.some.injEq] at tag low high
  have tagWord : read_mem_bytes 8 (r (.GPR 31#5) s + 144#64) s = 1#64 :=
    BitVec.eq_of_toNat_eq tag
  refine ⟨?_, ?_, ?_⟩
  · rw [read_tag_prefix, tagWord]
    rfl
  · apply BitVec.eq_of_toNat_eq
    simpa using low
  · apply BitVec.eq_of_toNat_eq
    simpa using high

end SszArm.BitVector.ValueTail

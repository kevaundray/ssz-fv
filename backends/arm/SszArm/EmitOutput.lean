import SszArm.EmitPost

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)

theorem load_one (s : ArmState) (address : Nat) :
    widthLoad s address 1 = some (s.mem (BitVec.ofNat 64 address)).toNat := by
  simp only [widthLoad, BoolCodec.read_one]
  rfl

/-- Partial initialization is respected across the entire supplied output.
The prefix and spare suffix may both be uninitialized: only previously present
spare bytes require observations. The written prefix is initialized by emission;
`Post.tail` separately preserves every spare physical byte, initialized or not. -/
theorem Post.output_initialization {s t : ArmState} {desc : Desc} {value : Value} {size : Nat}
    (post : Post s t desc value size)
    (expected : SszNative.Serialize.expectedSize desc value = .ok size)
    (before : Nat → Option UInt8)
    (spare : ∀ index byte, size ≤ index → index < (Args.ofEntry s).capacity.toNat →
      before index = some byte →
      widthLoad s ((Args.ofEntry s).output.toNat + index) 1 = some byte.toNat)
    (index : Nat) (byte : UInt8) (within : index < (Args.ofEntry s).capacity.toNat)
    (initialized : SszNative.Serialize.applyWrites before (SszNative.Serialize.emit desc value) index =
      some byte) :
    widthLoad t ((Args.ofEntry s).output.toNat + index) 1 = some byte.toNat := by
  have exactSize := (SszNative.Serialize.expected_encoding desc value).2 size expected
  by_cases inside : index < (SszNative.Serialize.emit desc value).size
  · simp only [SszNative.Serialize.applyWrites_prefix before _ index inside,
      Array.getElem?_eq_getElem inside] at initialized
    have observed := post.bytes index inside
    simpa only [Array.getElem?_eq_getElem inside, Option.getD_some, Option.some.inj initialized] using observed
  · have outside : size ≤ index := by rw [exactSize] at inside; omega
    have previous : before index = some byte := by
      simpa only [SszNative.Serialize.applyWrites, if_neg inside] using initialized
    have observed := spare index byte outside within previous
    have unchanged := post.tail index outside within
    have address : BitVec.ofNat 64 ((Args.ofEntry s).output.toNat + index) =
        (Args.ofEntry s).output + BitVec.ofNat 64 index := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [load_one, address] at observed ⊢
    rw [unchanged]
    exact observed

end SszArm.Emit

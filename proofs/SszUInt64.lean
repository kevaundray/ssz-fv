import Ssz.Proofs.Codec.Table

/-! Public SSZ codec equations for the eight-byte memory kernels. -/

namespace SszNative

/-- Every 64-bit machine word fits the upstream uint64 serialization domain. -/
theorem serialize_uint64 (value : BitVec 64) :
    Ssz.serialize (.uint 8) (.uint value.toNat) =
      .ok (Ssz.uintBytes 8 value.toNat) := by
  have fits : value.toNat < 2 ^ (8 * 8) := value.isLt
  simp [Ssz.serialize, fits]

/-- The upstream decoder consumes the entire eight-byte encoding of the word. -/
theorem deserialize_uint64 (value : BitVec 64) :
    Ssz.deserialize (.uint 8) (Ssz.uintBytes 8 value.toNat) =
      .ok (.uint value.toNat) := by
  simp [Ssz.deserialize, Ssz.uintBytes_size,
    Ssz.readUint_uintBytes 8 value.toNat value.isLt]
  rfl

end SszNative

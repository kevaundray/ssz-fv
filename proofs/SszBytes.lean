import Ssz.Codec.Deserialize

namespace SszNative

/-- A byte value that fits its descriptor is its own encoding. The upstream
validity predicate selects exactly byte vectors and byte lists; capacities are
unbounded naturals. This lemma assumes validation, rather than proving a native
validation routine. -/
theorem bytes_codec (desc : Ssz.Desc) (data : Ssz.Bytes)
    (fits : Ssz.Value.fits desc (.bytes data) = true) :
    Ssz.serialize desc (.bytes data) = .ok data ∧
    Ssz.deserialize desc data = .ok (.bytes data) := by
  cases desc <;> simp_all [Ssz.Value.fits]
  case byteVector length =>
    constructor
    · simp [Ssz.serialize, fits]
    · simp [Ssz.deserialize, fits] <;> rfl
  case byteList limit =>
    constructor
    · simp [Ssz.serialize, fits]
    · simp [Ssz.deserialize, Nat.not_lt.mpr fits] <;> rfl

end SszNative

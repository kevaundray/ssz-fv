import Kraken.SeparationMem
import SszUInt64

namespace SszX86

/-- The upstream natural-number serializer and Kraken agree at every byte width.
No bounded-natural surrogate is used for the upstream specification. -/
theorem uintBytes_eq_toBytes (width value : Nat) :
    (Ssz.uintBytes width value).toList = Int.toBytes width (Int.ofNat value) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    simp only [Ssz.uintBytes, Array.toList_append]
    change UInt8.ofNat (value % 256) :: (Ssz.uintBytes width (value / 256)).toList =
      UInt8.ofNat ((Int.ofNat value % 256).toNat) ::
        Int.toBytes width (Int.ofNat value / 256)
    rw [ih]
    rfl

/-- Signed register interpretation does not alter the eight stored bytes, even
when bit 63 is set. The statement covers every 64-bit register value. -/
theorem registerBytes_eq_uintBytes (value : BitVec 64) :
    Int.toBytes 8 value.toInt = (Ssz.uintBytes 8 value.toNat).toList := by
  have hmod : value.toInt.take 64 = Int.ofNat value.toNat := by
    have hbound := value.isLt
    change value.toInt % 18446744073709551616 = (value.toNat : Int)
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  calc
    Int.toBytes 8 value.toInt = Int.toBytes 8 (value.toInt.take 64) :=
      (Int.toBytes_emod 8 value.toInt).symm
    _ = Int.toBytes 8 (Int.ofNat value.toNat) := by rw [hmod]
    _ = (Ssz.uintBytes 8 value.toNat).toList := (uintBytes_eq_toBytes 8 value.toNat).symm

/-- The bytes used in the public contracts are the pinned upstream SSZ bytes. -/
def wordBytes (value : BitVec 64) : List UInt8 :=
  (Ssz.uintBytes 8 value.toNat).toList

@[simp] theorem wordBytes_length (value : BitVec 64) : (wordBytes value).length = 8 := by
  rw [wordBytes, ← registerBytes_eq_uintBytes]
  exact Int.toBytes_length 8 value.toInt

@[simp] theorem ofBytes_wordBytes (value : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes value)) = value := by
  rw [wordBytes, ← registerBytes_eq_uintBytes]
  exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl value

/-- The public serializer produces the bytes in the machine memory contract. -/
theorem serialize_wordBytes (value : BitVec 64) :
    Ssz.serialize (.uint 8) (.uint value.toNat) = .ok (wordBytes value).toArray := by
  simpa [wordBytes] using SszNative.serialize_uint64 value

/-- The public decoder interprets the machine memory contract as the same value. -/
theorem deserialize_wordBytes (value : BitVec 64) :
    Ssz.deserialize (.uint 8) (wordBytes value).toArray = .ok (.uint value.toNat) := by
  simpa [wordBytes] using SszNative.deserialize_uint64 value

end SszX86

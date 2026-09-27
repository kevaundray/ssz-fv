import SszLimbs

set_option autoImplicit false

namespace SszNative.WordDecode

/- Algorithm model of the OR/shift loops in native/src/nat.rs:from_le_bytes.
The same loop packs the small representation and every large-representation
limb. Pointer access, arena allocation, and ISA execution are separate
obligations. Out-of-range model reads are zero; native callers must additionally
establish that their selected byte range is accessible. -/
def packPrefix (data : Ssz.Bytes) (start : Nat) : Nat → BitVec 64
  | 0 => 0
  | count + 1 => packPrefix data start count |||
      (BitVec.ofNat 64 (data[start + count]?.getD 0).toNat <<< (8 * count))

private theorem pow_byte_succ (n : Nat) :
    2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
  rw [Nat.mul_add, Nat.pow_add]
  simp [Nat.mul_comm]

/-- An arbitrary byte window fits in exactly its unsigned byte width. -/
theorem readUint_lt (data : Ssz.Bytes) (start width : Nat) :
    Ssz.readUint data start width < 2 ^ (8 * width) := by
  induction width generalizing start with
  | zero => simp [Ssz.readUint]
  | succ width ih =>
    have hb : (data[start]?.getD 0).toNat < 256 :=
      (data[start]?.getD 0).toBitVec.isLt
    have hr := ih (start + 1)
    rw [Ssz.readUint, pow_byte_succ]
    omega

/-- Appending the next byte adds its high-position contribution. -/
theorem readUint_snoc (data : Ssz.Bytes) (start width : Nat) :
    Ssz.readUint data start (width + 1) = Ssz.readUint data start width +
      2 ^ (8 * width) * (data[start + width]?.getD 0).toNat := by
  induction width generalizing start with
  | zero => simp [Ssz.readUint]
  | succ width ih =>
    rw [Ssz.readUint, ih, Ssz.readUint, pow_byte_succ]
    simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- No carries or truncation occur while packing at most eight bytes. -/
theorem packPrefix_toNat (data : Ssz.Bytes) (start count : Nat) (fits : count ≤ 8) :
    (packPrefix data start count).toNat = Ssz.readUint data start count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have ih' := ih (by omega)
    have low := readUint_lt data start count
    let byte := data[start + count]?.getD 0
    have hb : byte.toNat < 256 := byte.toBitVec.isLt
    have hb64 : byte.toNat < 2 ^ 64 := by omega
    have product := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos (8 * count))
    have power : 2 ^ (8 * (count + 1)) ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_byte_succ] at power
    have shifted : byte.toNat * 2 ^ (8 * count) < 2 ^ 64 := by omega
    rw [packPrefix, BitVec.toNat_or, ih', BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt shifted, SszNative.WordDecode.readUint_snoc]
    change Ssz.readUint data start count ||| (byte.toNat * 2 ^ (8 * count)) = _
    rw [Nat.or_comm, Nat.mul_comm byte.toNat,
      ← Nat.two_pow_add_eq_or_of_lt low byte.toNat]
    exact Nat.add_comm _ _

/-- Splitting a byte window separates its low and high contributions. -/
theorem readUint_split (data : Ssz.Bytes) (start low high : Nat) :
    Ssz.readUint data start (low + high) = Ssz.readUint data start low +
      2 ^ (8 * low) * Ssz.readUint data (start + low) high := by
  induction low generalizing start with
  | zero => simp [Ssz.readUint]
  | succ low ih =>
    rw [Nat.succ_add, Ssz.readUint, ih, Ssz.readUint, pow_byte_succ]
    simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- The native eight-byte grouping, including a final partial word. -/
def decodeWords (data : Ssz.Bytes) (start count : Nat) : List (BitVec 64) :=
  if count = 0 then [] else
    let chunk := min count 8
    packPrefix data start chunk :: decodeWords data (start + chunk) (count - chunk)
termination_by count
decreasing_by omega

theorem decodeWords_value (data : Ssz.Bytes) (start count : Nat) :
    SszNative.Limbs.value (decodeWords data start count) =
      Ssz.readUint data start count := by
  induction count using Nat.strongRecOn generalizing start with
  | ind count ih =>
    rw [decodeWords]
    by_cases zero : count = 0
    · subst count
      rfl
    · simp only [zero, ↓reduceIte]
      by_cases small : count ≤ 8
      · simp only [Nat.min_eq_left small, Nat.sub_self, decodeWords,
          ↓reduceIte, SszNative.Limbs.value, Nat.mul_zero, Nat.add_zero]
        exact packPrefix_toNat data start count small
      · have large : 8 ≤ count := by omega
        simp only [Nat.min_eq_right large, SszNative.Limbs.value]
        rw [packPrefix_toNat data start 8 (by decide),
          ih (count - 8) (by omega) (start + 8)]
        have split := readUint_split data start 8 (count - 8)
        simpa only [Nat.add_sub_of_le large] using split.symm

/-- The limb count used by the native arena reservation. -/
theorem decodeWords_length (data : Ssz.Bytes) (start count : Nat) :
    (decodeWords data start count).length = (count + 7) / 8 := by
  induction count using Nat.strongRecOn generalizing start with
  | ind count ih =>
    rw [decodeWords]
    by_cases hz : count = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte, List.length_cons]
      rw [ih (count - min count 8) (by omega) (start + min count 8)]
      omega

/-- Countdown over redundant high zero bytes, before choosing the representation. -/
def significantBytes (data : Ssz.Bytes) : Nat → Nat
  | 0 => 0
  | count + 1 =>
    if data[count]?.getD 0 = 0 then significantBytes data count else count + 1

theorem significantBytes_le (data : Ssz.Bytes) (count : Nat) :
    significantBytes data count ≤ count := by
  induction count with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
    simp only [significantBytes]
    split <;> omega

theorem readUint_significantBytes (data : Ssz.Bytes) (count : Nat) :
    Ssz.readUint data 0 (significantBytes data count) = Ssz.readUint data 0 count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [significantBytes]
    split
    · rename_i lastZero
      rw [ih, readUint_snoc]
      simp [lastZero]
    · rfl

/-- Logical limb representation of the native decoder's result. Empty words
represent Small(0); a single word represents Small; longer lists represent Large. -/
def decode (data : Ssz.Bytes) : List (BitVec 64) :=
  decodeWords data 0 (significantBytes data data.size)

theorem decode_value (data : Ssz.Bytes) :
    SszNative.Limbs.value (decode data) = Ssz.readUint data 0 data.size := by
  rw [decode, decodeWords_value, readUint_significantBytes]

theorem deserialize_uint (data : Ssz.Bytes) (width : Nat) (size : data.size = width) :
    Ssz.deserialize (.uint width) data =
      .ok (.uint (SszNative.Limbs.value (decode data))) := by
  rw [decode_value]
  simp [Ssz.deserialize, size] <;> rfl

/-- Full integer decoding outcome, including the exact-scope rejection.
Native allocation success is a separate machine-level precondition. -/
def outcome (width : Nat) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value :=
  if data.size = width then .ok (.uint (SszNative.Limbs.value (decode data)))
  else .error (.scope width data.size)

theorem outcome_eq_deserialize (width : Nat) (data : Ssz.Bytes) :
    outcome width data = Ssz.deserialize (.uint width) data := by
  by_cases h : data.size = width
  · simpa only [outcome, h, ↓reduceIte] using (deserialize_uint data width h).symm
  · simp [outcome, Ssz.deserialize, h] <;> rfl

end SszNative.WordDecode

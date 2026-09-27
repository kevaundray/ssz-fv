import Std
import Ssz.Proofs.Codec.Table

set_option autoImplicit false

namespace SszNative.Limbs

/-- The little-endian base-2^64 value of a limb list. -/
def value : List (BitVec 64) -> Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * value ws

/-- The `i`-th byte of a limb list, read little-endian. -/
def byteAt (words : List (BitVec 64)) (i : Nat) : UInt8 :=
  UInt8.ofNat ((words[i / 8]?.getD 0).toNat / 2 ^ (8 * (i % 8)))

/-- Fixed-width bytes extracted from a limb list. -/
def bytes (words : List (BitVec 64)) (width : Nat) : Array UInt8 :=
  Array.ofFn (fun i : Fin width => byteAt words i.1)

private theorem value_append (xs ys : List (BitVec 64)) :
    value (xs ++ ys) = value xs + 2 ^ (64 * xs.length) * value ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
      simp only [List.cons_append, value, List.length, ih]
      have hpow : 2 ^ 64 * 2 ^ (64 * xs.length) = 2 ^ (64 * (xs.length + 1)) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, hpow]

/-- Appending zero limbs on the high end preserves the value. -/
theorem value_append_zero (words : List (BitVec 64)) (n : Nat) :
    value (words ++ List.replicate n (0 : BitVec 64)) = value words := by
  have hz : value (List.replicate n (0 : BitVec 64)) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp_all [List.replicate_succ, value]
  rw [value_append, hz, Nat.mul_zero, Nat.add_zero]

/-- The value of any limb list fits in its declared radix. -/
theorem value_lt (words : List (BitVec 64)) :
    value words < 2 ^ (64 * words.length) := by
  induction words with
  | nil => simp [value]
  | cons w ws ih =>
      have hw : w.toNat < 2 ^ 64 := w.isLt
      have hsucc : 1 + value ws ≤ 2 ^ (64 * ws.length) := by omega
      calc
        value (w :: ws) = w.toNat + 2 ^ 64 * value ws := rfl
        _ < 2 ^ 64 + 2 ^ 64 * value ws := Nat.add_lt_add_right hw _
        _ = 2 ^ 64 * (1 + value ws) := by simp [Nat.mul_add]
        _ ≤ 2 ^ 64 * 2 ^ (64 * ws.length) := Nat.mul_le_mul_left _ hsucc
        _ = 2 ^ (64 * (ws.length + 1)) := by
            rw [show 64 * (ws.length + 1) = 64 * ws.length + 64 by omega,
              Nat.pow_add, Nat.mul_comm]

private theorem byte_of_add_high (a b i : Nat) (hi : i < 8) :
    ((a + 2 ^ 64 * b) / 2 ^ (8 * i)) % 256 = (a / 2 ^ (8 * i)) % 256 := by
  have hpow : 2 ^ 64 = 2 ^ (8 * i) * 2 ^ (64 - 8 * i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmul : 2 ^ 64 * b = (2 ^ (64 - 8 * i) * b) * 2 ^ (8 * i) := by
    rw [hpow]
    ac_rfl
  rw [hmul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
  have hdiv : (2 ^ (64 - 8 * i) * b) % 256 = 0 := by
    have hsplit' : 64 - 8 * i = 8 + (56 - 8 * i) := by omega
    have hpow256 : 256 ∣ 2 ^ (64 - 8 * i) := by
      refine ⟨2 ^ (56 - 8 * i), ?_⟩
      rw [hsplit', Nat.pow_add]
    obtain ⟨k, hk⟩ := hpow256
    apply Nat.mod_eq_zero_of_dvd
    exact ⟨k * b, by rw [hk, Nat.mul_assoc]⟩
  simp only [Nat.add_mod, hdiv, Nat.add_zero, Nat.mod_mod]

private theorem value_shift8 (w : BitVec 64) (ws : List (BitVec 64)) (i : Nat) :
    value (w :: ws) / 2 ^ (8 * (i + 8)) = value ws / 2 ^ (8 * i) := by
  have hpow : 2 ^ (8 * (i + 8)) = 2 ^ 64 * 2 ^ (8 * i) := by
    have hs : 8 * (i + 8) = 64 + 8 * i := by omega
    rw [hs, Nat.pow_add]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  have hdiv : value (w :: ws) / 2 ^ 64 = value ws := by
    change (w.toNat + 2 ^ 64 * value ws) / 2 ^ 64 = value ws
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt w.isLt, Nat.zero_add]
  rw [hdiv]

/-- Byte extraction from limbs agrees with the byte of the represented value. -/
theorem byteAt_eq_value (words : List (BitVec 64)) (i : Nat) :
    byteAt words i = UInt8.ofNat ((value words / 2 ^ (8 * i)) % 256) := by
  induction words generalizing i with
  | nil => simp [byteAt, value]
  | cons w ws ih =>
      by_cases hi : i < 8
      · have hbyte : byteAt (w :: ws) i = UInt8.ofNat (w.toNat / 2 ^ (8 * i)) := by
          simp [byteAt, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
        rw [hbyte, value, byte_of_add_high w.toNat (value ws) i hi]
        exact UInt8.ofNat_mod_size.symm
      · have hi8 : 8 ≤ i := Nat.le_of_not_lt hi
        let j := i - 8
        have hj : i = j + 8 := by
          subst j
          omega
        have hrec : byteAt ws j = UInt8.ofNat ((value ws / 2 ^ (8 * j)) % 256) := ih j
        rw [hj]
        simpa [byteAt, Nat.add_div_right, Nat.add_mod_right,
          value_shift8 w ws j] using hrec

/-- The byte at a valid SSZ integer position, including truncated encodings. -/
theorem uintBytes_byte (width value i : Nat) (hi : i < width) :
    (Ssz.uintBytes width value)[i]'(by simpa only [Ssz.uintBytes_size] using hi) =
      UInt8.ofNat ((value / 2 ^ (8 * i)) % 256) := by
  induction width generalizing value i with
  | zero => cases hi
  | succ width ih =>
      cases i with
      | zero =>
          simp [Ssz.uintBytes]
      | succ i =>
          have hi' : i < width := Nat.succ_lt_succ_iff.mp hi
          have hrec := ih (value / 256) i hi'
          have hpow : 256 * 2 ^ (8 * i) = 2 ^ (8 * (i + 1)) := by
            rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add]
            congr 1
            omega
          simpa [Ssz.uintBytes, Array.getElem_append, Nat.div_div_eq_div_mul, hpow] using hrec

/-- The limb bytes match upstream SSZ integer bytes at every width. -/
theorem bytes_eq_uintBytes (words : List (BitVec 64)) (width : Nat) :
    bytes words width = Ssz.uintBytes width (value words) := by
  apply Array.ext
  · simp [bytes, Ssz.uintBytes_size]
  · intro i hi hi₂
    have hi' : i < width := by simpa only [bytes, Array.size_ofFn] using hi
    simp only [bytes, Array.getElem_ofFn]
    rw [byteAt_eq_value, uintBytes_byte width (value words) i hi']

/-- Appending zero limbs on the high end preserves the byte output at every width. -/
theorem bytes_append_zero (words : List (BitVec 64)) (n width : Nat) :
    bytes (words ++ List.replicate n (0 : BitVec 64)) width = bytes words width := by
  rw [bytes_eq_uintBytes, bytes_eq_uintBytes, value_append_zero]

/-- SSZ serialization agrees with limb extraction. -/
theorem serialize_uint (words : List (BitVec 64)) (width : Nat)
    (bound : value words < 2 ^ (8 * width)) :
    Ssz.serialize (.uint width) (.uint (value words)) = .ok (bytes words width) := by
  simp [Ssz.serialize, bound, bytes_eq_uintBytes]

/-- SSZ deserialization recovers the represented value. -/
theorem deserialize_uint (words : List (BitVec 64)) (width : Nat)
    (bound : value words < 2 ^ (8 * width)) :
    Ssz.deserialize (.uint width) (bytes words width) = .ok (.uint (value words)) := by
  rw [bytes_eq_uintBytes]
  simp [Ssz.deserialize, Ssz.uintBytes_size, Ssz.readUint_uintBytes, bound] <;> rfl

/-- An unsigned 64-bit shift can be read as byte extraction. -/
theorem shift_toNat_byte (word : BitVec 64) (i : Nat) :
    UInt8.ofNat ((word >>> (8 * (i % 8))).toNat) =
      UInt8.ofNat (word.toNat / 2 ^ (8 * (i % 8))) := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end SszNative.Limbs

import SszSerializeCore
import SszWidth

set_option autoImplicit false

namespace SszNative.Serialize

@[simp] theorem count_value (size : Nat) (physical : size < 2 ^ 64) :
    (count size).value = size := by
  simp only [count, NatOperand.value, NatOperand.words, Limbs.value,
    Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]

theorem requiredBytes_fits (number width : Nat) :
    requiredBytes number ≤ width ↔ number < 2 ^ (8 * width) := by
  by_cases zero : number = 0
  · subst number
    simp [requiredBytes, bitLength, Nat.two_pow_pos]
  · have bits : bitLength number = number.log2 + 1 := by simp [bitLength, zero]
    have rounded : requiredBytes number ≤ width ↔ number.log2 < 8 * width := by
      unfold requiredBytes
      rw [bits]
      split <;> omega
    exact rounded.trans (Nat.log2_lt zero)

theorem uintFits_iff (width number : NatOperand) :
    uintFits width number ↔ number.value < 2 ^ (8 * width.value) :=
  requiredBytes_fits number.value width.value

/-- Ideal primitive measurement, with semantic checks but without host resources.
This is an independent mathematical result against which the ordered native
measurement is compared, not an implementation shortcut. -/
def expectedSize (desc : Desc) (value : Value) : Except Ssz.Err Nat :=
  match desc, value with
  | .bool, .bool _ => .ok 1
  | .uint width, .uint number =>
    if uintFits width number then .ok width.value else .error .typeMismatch
  | .byteVector length, .bytes bytes =>
    if length.value = bytes.size then .ok bytes.size else .error (.scope length.value bytes.size)
  | .byteList limit, .bytes bytes =>
    if bytes.size ≤ limit.value then .ok bytes.size else .error (.overLimit limit.value bytes.size)
  | .bitVector length, .bits bits =>
    if length.value = bits.count.toNat then .ok bits.bytes.size
    else .error (.scope length.value bits.count.toNat)
  | .bitList limit, .bits bits =>
    if bits.count.toNat ≤ limit.value then .ok (bits.count.toNat / 8 + 1)
    else .error (.overLimit limit.value bits.count.toNat)
  | .progressiveBitList limit, .bits bits =>
    match limit with
    | none => .ok (bits.count.toNat / 8 + 1)
    | some cap =>
      if bits.count.toNat ≤ cap.value then .ok (bits.count.toNat / 8 + 1)
      else .error (.overLimit cap.value bits.count.toNat)
  | _, _ => .error .typeMismatch

theorem operand_bytes (number : NatOperand) (width : Nat) :
    Limbs.bytes number.words width = Ssz.uintBytes width number.value :=
  Limbs.bytes_eq_uintBytes number.words width

theorem canonical_size (bits : Packed) :
    (PackedBits.canonicalBytes bits.bytes bits.count.toNat).size = bits.bytes.size := by
  rw [← PackedBits.packBits_unpackBits_canonicalBytes bits.bytes bits.count.toNat bits.sized]
  simp only [Ssz.packBits, Array.size_ofFn, ← bits.sized]

theorem delimited_size (bits : Packed) :
    (PackedBits.delimitedBytes bits.bytes bits.count.toNat).size = bits.count.toNat / 8 + 1 := by
  rw [← PackedBits.packBitsDelimited_unpackBits bits.bytes bits.count.toNat bits.sized]
  simp only [Ssz.packBitsDelimited, Ssz.packBits, Array.size_ofFn, Packing.unpackBits_size]
  omega

/-- Dirty packed padding is masked, complete source bytes are copied, and the
list delimiter is emitted even for zero bits. No source canonicality assumption
is used. The width in success is exactly the emitted byte count. -/
theorem expected_encoding (desc : Desc) (value : Value) :
    Ssz.serialize desc.erase value.erase =
      (expectedSize desc value).map (fun _ => emit desc value) ∧
    ∀ size, expectedSize desc value = .ok size → (emit desc value).size = size := by
  cases desc with
  | bool =>
    cases value <;>
      simp [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize, Except.map]
  | uint width =>
    cases value with
    | uint number =>
      by_cases fits : uintFits width number <;>
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          ← uintFits_iff, fits, ↓reduceIte, Except.map, operand_bytes,
          Ssz.uintBytes_size] <;> simp
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]
  | byteVector length =>
    cases value with
    | bytes bytes =>
      by_cases same : length.value = bytes.size
      · simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          same, ↓reduceIte, Except.map] <;> simp
      · have reverse : bytes.size ≠ length.value := Ne.symm same
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          same, ↓reduceIte, Except.map] <;> simp
        exact reverse
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]
  | byteList limit =>
    cases value with
    | bytes bytes =>
      by_cases fits : bytes.size ≤ limit.value <;>
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          fits, ↓reduceIte, Except.map] <;> simp
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]
  | bitVector length =>
    cases value with
    | bits bits =>
      have packed := PackedBits.packBits_unpackBits_canonicalBytes bits.bytes bits.count.toNat bits.sized
      by_cases same : length.value = bits.count.toNat
      · simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          Packing.unpackBits_size, same, ↓reduceIte, Except.map, packed,
          canonical_size bits] <;> simp
      · have reverse : bits.count.toNat ≠ length.value := Ne.symm same
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          Packing.unpackBits_size, same, ↓reduceIte, Except.map] <;> simp
        exact reverse
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]
  | bitList limit =>
    cases value with
    | bits bits =>
      have packed := PackedBits.packBitsDelimited_unpackBits bits.bytes bits.count.toNat bits.sized
      by_cases fits : bits.count.toNat ≤ limit.value <;>
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          Packing.unpackBits_size, fits, ↓reduceIte, Except.map, packed,
          delimited_size bits] <;> simp
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]
  | progressiveBitList limit =>
    cases value with
    | bits bits =>
      have packed := PackedBits.packBitsDelimited_unpackBits bits.bytes bits.count.toNat bits.sized
      cases limit with
      | none =>
        simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
          Option.map, Ssz.boundCheck, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.map, packed, delimited_size bits] <;> simp
      | some cap =>
        by_cases fits : bits.count.toNat ≤ cap.value <;>
          simp only [Desc.erase, Value.erase, expectedSize, emit, Ssz.serialize,
            Option.map, Ssz.boundCheck, Packing.unpackBits_size, fits, ↓reduceIte,
            Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map, packed,
            delimited_size bits] <;> simp
    | _ =>
      simp [Desc.erase, Value.erase, expectedSize, Ssz.serialize, Except.map]

/-- This does not assume an encoding succeeds: semantic rejection is preserved. -/
theorem expectedSize_eq_pinned (desc : Desc) (value : Value) :
    expectedSize desc value = (Ssz.serialize desc.erase value.erase).map Array.size := by
  obtain ⟨encoding, width⟩ := expected_encoding desc value
  rw [encoding]
  cases checked : expectedSize desc value with
  | error reason => rfl
  | ok size => simp only [Except.map, width size checked]

/-- A helper can fail only at its actual two-word reservation; its represented
value on success is the full 128-bit input, not merely the low word. -/
theorem fromWide_cases (arena : Delimited.ArenaState) (wide : BitVec 128) :
    (∃ actual, (fromWide arena wide).result = .ok actual ∧ actual.value = wide.toNat) ∨
      (fromWide arena wide).result = .error (.arithmetic .scratchExhausted) := by
  cases result : (NatArithmetic.fromWide arena.base arena.capacity arena.used wide).result with
  | ok actual =>
    left
    exact ⟨actual, by simp only [fromWide, result, Except.mapError],
      NatArithmetic.fromWide_value arena.base arena.capacity arena.used wide actual result⟩
  | error reason =>
    cases reason with
    | scratchExhausted => right; simp only [fromWide, result, Except.mapError]
    | badRepresentation =>
      unfold NatArithmetic.fromWide at result
      split at result
      · cases result
      · split at result <;> cases result

/-- Resource-transparent correctness: scratch failure is an explicit alternative,
not a hypothesis asserting enough space or successful parsing. -/
def Measures (result : Except Error NatOperand) (expected : Except Ssz.Err Nat) : Prop :=
  eraseResult (result.map NatOperand.value) = .ok expected ∨
    result = .error (.arithmetic .scratchExhausted)

private theorem fromWide_measures (arena : Delimited.ArenaState) (wide : BitVec 128) :
    Measures (fromWide arena wide).result (.ok wide.toNat) := by
  rcases fromWide_cases arena wide with ⟨actual, success, value⟩ | exhausted
  · left
    simp only [success, Except.map, eraseResult, value]
  · exact Or.inr exhausted

private theorem list_measures (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) :
    Measures (measureList limit bits arena).result
      (match limit with
       | none => .ok (bits.count.toNat / 8 + 1)
       | some cap => if bits.count.toNat ≤ cap.value then .ok (bits.count.toNat / 8 + 1)
           else .error (.overLimit cap.value bits.count.toNat)) := by
  have widthBound : bits.count.toNat / 8 + 1 < 2 ^ 128 := by
    have := bits.count.isLt
    omega
  have widthValue : (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)).toNat =
      bits.count.toNat / 8 + 1 := Nat.mod_eq_of_lt widthBound
  rcases fromWide_cases arena bits.count with ⟨actual, success, value⟩ | exhausted
  · have next := fromWide_measures { arena with used := (fromWide arena bits.count).used }
      (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))
    rw [widthValue] at next
    cases limit with
    | none => simpa only [measureList, bind, success, bounded, unchanged] using next
    | some cap =>
      by_cases fits : bits.count.toNat ≤ cap.value
      · simpa only [measureList, bind, success, bounded, value, fits, ↓reduceIte, unchanged] using next
      · left
        simp only [measureList, bind, success, bounded, value, fits, ↓reduceIte,
          unchanged, Except.map, eraseResult]
  · right
    simp only [measureList, bind, exhausted]

/-- Every primitive and every wrong Value kind is covered. Noncanonical original
NatOperands are unrestricted, and no scratch-availability guard is assumed. -/
theorem measure_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) :
    Measures (measure desc value arena).result (expectedSize desc value) := by
  cases desc <;> cases value <;>
    simp only [measure, expectedSize, Value.Physical] at physical ⊢
  all_goals try { exact Or.inl rfl }
  · split <;> exact Or.inl rfl
  · rename_i length bytes
    split <;> left <;>
      simp only [unchanged, Except.map, eraseResult, count_value bytes.size physical]
  · rename_i limit bytes
    by_cases fits : bytes.size ≤ limit.value <;> left <;>
      simp only [bounded, count_value bytes.size physical, fits, ↓reduceIte, bind,
        unchanged, Except.map, eraseResult]
  · rename_i length bits
    split
    · left
      simp only [unchanged, Except.map, eraseResult, count_value bits.bytes.size physical]
    · rcases fromWide_cases arena bits.count with ⟨actual, success, value⟩ | exhausted
      · left
        simp only [bind, success, unchanged, Except.map, eraseResult, value]
      · right
        simp only [bind, exhausted]
  · exact list_measures _ _ _
  · exact list_measures _ _ _

open SszNative.Limbs
/-- The rounding used by the native ADD/SHRD pair, including the zero case. -/
theorem requiredBytes_round (number : Nat) :
    requiredBytes number = (bitLength number + 7) / 8 := by
  unfold requiredBytes
  split <;> omega

/-- A low radix digit cannot change the leading bit of a positive higher digit. -/
theorem log2_radix (low high bits : Nat) (lowBound : low < 2 ^ bits)
    (positive : 0 < high) :
    (low + 2 ^ bits * high).log2 = bits + high.log2 := by
  have highNonzero : high ≠ 0 := by omega
  have lo := Nat.log2_self_le highNonzero
  have hi := Nat.lt_log2_self (n := high)
  have radixPositive := Nat.two_pow_pos bits
  have numberPositive : 0 < low + 2 ^ bits * high := by
    have := Nat.mul_pos radixPositive positive
    omega
  apply (Nat.log2_eq_iff (by omega : low + 2 ^ bits * high ≠ 0)).mpr
  constructor
  · rw [Nat.pow_add]
    exact Nat.le_trans (Nat.mul_le_mul_left _ lo) (Nat.le_add_left _ _)
  · have upper : low + 2 ^ bits * high < 2 ^ bits * (high + 1) := by
      rw [Nat.mul_succ]
      omega
    have bounded := Nat.mul_le_mul_left (2 ^ bits) (show high + 1 ≤ 2 ^ (high.log2 + 1) by omega)
    have exponent : bits + high.log2 + 1 = bits + (high.log2 + 1) := by omega
    rw [exponent, Nat.pow_add]
    exact Nat.lt_of_lt_of_le upper bounded

/-- The value of a prefix followed by one original physical limb. -/
theorem prefix_value_succ : ∀ (words : List (BitVec 64)) (n : Nat),
    Limbs.value (words.take (n + 1)) = Limbs.value (words.take n) +
      2 ^ (64 * n) * (words[n]?.getD 0).toNat
  | [], n => by simp [Limbs.value]
  | word :: words, 0 => by simp [Limbs.value]
  | word :: words, n + 1 => by
    have ih := prefix_value_succ words n
    have power : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [power]
    simp [Limbs.value, ih, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- The literal countdown removes only high zeros, not active low limbs. -/
theorem significant_prefix_value (words : List (BitVec 64)) (n : Nat) :
    Limbs.value (words.take (significantCount words n)) = Limbs.value (words.take n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases zero : words[n]?.getD 0 = 0
    · simp only [significantCount, zero, ↓reduceIte]
      rw [ih, prefix_value_succ, zero]
      simp
    · simp only [significantCount, zero, ↓reduceIte]

/-- The selected highest physical limb is nonzero even in a padded representation. -/
theorem significant_top_nonzero (words : List (BitVec 64)) (n : Nat)
    (positive : 0 < significantCount words n) :
    words[significantCount words n - 1]?.getD 0 ≠ 0 := by
  induction n with
  | zero => simp [significantCount] at positive
  | succ n ih =>
    by_cases zero : words[n]?.getD 0 = 0
    · simp only [significantCount, zero, ↓reduceIte] at positive ⊢
      exact ih positive
    · simp only [significantCount, zero, ↓reduceIte, Nat.add_sub_cancel]
      exact zero

/-- This is the pure semantic bridge for both ISA scans. It neither assumes a
successful width check nor bounds the mathematical value by a host word. -/
theorem bitLength_significant (words : List (BitVec 64))
    (positive : 0 < sigWords words) :
    bitLength (Limbs.value words) = 64 * (sigWords words - 1) +
      (words[sigWords words - 1]?.getD 0).toNat.log2 + 1 := by
  let count := sigWords words
  let top := words[count - 1]?.getD 0
  have topNonzero : top ≠ 0 := significant_top_nonzero words words.length positive
  have topPositive : 0 < top.toNat := by
    have : top.toNat ≠ 0 := by
      intro zero
      apply topNonzero
      apply BitVec.eq_of_toNat_eq
      simpa using zero
    omega
  have selectedPrefix : Limbs.value words = Limbs.value (words.take count) := by
    have selected := significant_prefix_value words words.length
    dsimp only [count, sigWords]
    simpa only [List.take_length] using selected.symm
  have predecessor : count - 1 + 1 = count := by dsimp [count]; omega
  have decomposition : Limbs.value words = Limbs.value (words.take (count - 1)) +
      2 ^ (64 * (count - 1)) * top.toNat := by
    calc
      Limbs.value words = Limbs.value (words.take count) := selectedPrefix
      _ = Limbs.value (words.take (count - 1 + 1)) := by rw [predecessor]
      _ = _ := prefix_value_succ words (count - 1)
  have lowBound : Limbs.value (words.take (count - 1)) < 2 ^ (64 * (count - 1)) := by
    apply Nat.lt_of_lt_of_le (value_lt _)
    apply Nat.pow_le_pow_right (by decide)
    simp only [List.length_take]
    omega
  have logarithm := log2_radix _ top.toNat (64 * (count - 1)) lowBound topPositive
  have valuePositive : 0 < Limbs.value words := by
    rw [decomposition]
    have := Nat.mul_pos (Nat.two_pow_pos (64 * (count - 1))) topPositive
    omega
  unfold bitLength
  have nonzero : Limbs.value words ≠ 0 := by omega
  simp only [nonzero, ↓reduceIte]
  rw [decomposition, logarithm]

/-- Rounded native size formula, preserving the selected limb's full 64 bits. -/
theorem requiredBytes_significant (words : List (BitVec 64))
    (positive : 0 < sigWords words) :
    requiredBytes (Limbs.value words) =
      (64 * (sigWords words - 1) + (words[sigWords words - 1]?.getD 0).toNat.log2 + 8) / 8 := by
  rw [requiredBytes_round, bitLength_significant words positive]

theorem requiredBytes_zero_significant (words : List (BitVec 64))
    (zero : sigWords words = 0) : requiredBytes (Limbs.value words) = 0 := by
  have valueZero : Limbs.value words = 0 := by
    have selected := significant_prefix_value words words.length
    change Limbs.value (words.take (sigWords words)) = _ at selected
    simpa [zero, Limbs.value] using selected.symm
  simp [valueZero, requiredBytes, bitLength]

/-- A physical list bounds the computed size, not the input's logical magnitude. -/
theorem requiredBytes_length (words : List (BitVec 64)) :
    requiredBytes (Limbs.value words) ≤ 8 * words.length := by
  apply (requiredBytes_fits _ _).mpr
  have bound := value_lt words
  simpa only [show 8 * (8 * words.length) = 64 * words.length by omega] using bound

/-- The actual sixteen-byte arithmetic cannot overflow, even before using the
stronger mapped-allocation bound on physical limb storage. -/
theorem requiredBytes_u128 (words : List (BitVec 64))
    (physical : words.length < 2 ^ 64) :
    requiredBytes (Limbs.value words) < 2 ^ 128 := by
  have := requiredBytes_length words
  omega

/-- Three significant width limbs dominate every native 128-bit byte requirement. -/
theorem wide_width_bound (words : List (BitVec 64)) (wide : 2 < sigWords words) :
    2 ^ 128 ≤ Limbs.value words := by
  have nonempty : trim words ≠ [] := by
    intro empty
    have count := trim_length words
    rw [empty] at count
    simp only [List.length_nil] at count
    omega
  have lower := canonical_ge_pow _ (trim_canonical words) nonempty
  have power : 2 ^ 128 ≤ 2 ^ (64 * ((trim words).length - 1)) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [trim_length]
    omega
  rw [trim_value] at lower
  exact Nat.le_trans power lower

/-- Exact stopping certificate for the real repeated SHR64 lowering. -/
theorem bsr_certificate (word : BitVec 64) (nonzero : word ≠ 0) :
    word >>> (word.toNat.log2 + 1) = 0 ∧
      ∀ i, i ≤ word.toNat.log2 → word >>> i ≠ 0 := by
  have positive : word.toNat ≠ 0 := by
    intro zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using zero
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_log2_self (n := word.toNat))
  · intro i within zero
    have lower := (Nat.le_log2 positive).mp within
    have quotient : 0 < word.toNat / 2 ^ i := Nat.div_pos lower (Nat.two_pow_pos i)
    have valueZero := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at valueZero
    change word.toNat / 2 ^ i = 0 at valueZero
    omega

theorem bsr_bound (word : BitVec 64) (nonzero : word ≠ 0) : word.toNat.log2 < 64 := by
  have positive : word.toNat ≠ 0 := by
    intro zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using zero
  exact (Nat.log2_lt positive).mpr word.isLt

end SszNative.Serialize

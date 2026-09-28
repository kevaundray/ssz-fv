import SszSerializeCore

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

end SszNative.Serialize

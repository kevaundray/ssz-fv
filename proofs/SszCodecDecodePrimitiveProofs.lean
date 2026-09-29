import SszCodecDecodeRefinementCore
import SszBool

set_option autoImplicit false

namespace SszNative.CodecDecode

attribute [local simp] Except.map Except.mapError


/-- The small branch packs only the significant prefix and performs no reservation. -/
theorem unsigned_small (input : Input) (arena : Delimited.ArenaState)
    (small : WordDecode.significantBytes input.bytes input.bytes.size ≤ 8) :
    unsigned input arena =
      ⟨.ok (.uint (.small (WordDecode.packPrefix input.bytes 0
        (WordDecode.significantBytes input.bytes input.bytes.size)))), arena.used,
        [.uint input arena (WordDecode.significantBytes input.bytes input.bytes.size) none []]⟩ := by
  simp only [unsigned, small, ↓reduceIte]

/-- The reservation is exactly the ceiling of the trimmed byte count, not the
schema width or the untrimmed input length. The recorded initialized words have
exactly that length. -/
theorem unsigned_large (input : Input) (arena : Delimited.ArenaState)
    (large : ¬ WordDecode.significantBytes input.bytes input.bytes.size ≤ 8)
    (allocation : Arena.Reservation)
    (reserved : Arena.reserve arena.base arena.capacity arena.used
      ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) = some allocation) :
    unsigned input arena =
      ⟨.ok (.uint (.large (BitVec.ofNat 64 allocation.pointer)
        (WordDecode.decodeWords input.bytes 0
          (WordDecode.significantBytes input.bytes input.bytes.size)))), allocation.used,
        [.uint input arena (WordDecode.significantBytes input.bytes input.bytes.size)
          (some allocation) (WordDecode.decodeWords input.bytes 0
            (WordDecode.significantBytes input.bytes input.bytes.size))]⟩ ∧
    (WordDecode.decodeWords input.bytes 0
      (WordDecode.significantBytes input.bytes input.bytes.size)).length =
      (WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8 := by
  exact ⟨by simp only [unsigned, large, ↓reduceIte, reserved], WordDecode.decodeWords_length _ _ _⟩

theorem unsigned_exhausted (input : Input) (arena : Delimited.ArenaState)
    (large : ¬ WordDecode.significantBytes input.bytes input.bytes.size ≤ 8)
    (reserved : Arena.reserve arena.base arena.capacity arena.used
      ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) = none) :
    unsigned input arena = ⟨.error scratch, arena.used,
      [.uint input arena (WordDecode.significantBytes input.bytes input.bytes.size) none []]⟩ := by
  simp only [unsigned, large, ↓reduceIte, reserved]

theorem unsigned_refines (input : Input) (arena : Delimited.ArenaState) :
    (unsigned input arena).erase = .ok (.ok (.uint (Ssz.readUint input.bytes 0 input.bytes.size))) ∨
    (unsigned input arena).erase = .error (.arithmetic .scratchExhausted) := by
  by_cases small : WordDecode.significantBytes input.bytes input.bytes.size ≤ 8
  · have value : (NatOperand.small (WordDecode.packPrefix input.bytes 0
        (WordDecode.significantBytes input.bytes input.bytes.size))).value =
        Ssz.readUint input.bytes 0 input.bytes.size := by
      simp only [NatOperand.value, NatOperand.words, Limbs.value, Nat.mul_zero, Nat.add_zero]
      rw [WordDecode.packPrefix_toNat _ _ _ small, WordDecode.readUint_significantBytes]
    left
    simp [unsigned, small, Outcome.erase, Codec.eraseResult, Node.value, value]
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used
        ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) with
    | none =>
      right
      simp [unsigned, small, reserved, Outcome.erase, scratch, Codec.eraseResult, Serialize.eraseResult]
    | some allocation =>
      have value : (NatOperand.large (BitVec.ofNat 64 allocation.pointer)
          (WordDecode.decodeWords input.bytes 0
            (WordDecode.significantBytes input.bytes input.bytes.size))).value =
          Ssz.readUint input.bytes 0 input.bytes.size := by
        change Limbs.value (WordDecode.decodeWords _ _ _) = _
        rw [WordDecode.decodeWords_value, WordDecode.readUint_significantBytes]
      left
      simp [unsigned, small, reserved, Outcome.erase, Codec.eraseResult, Node.value, value]

/-- Every successful unsigned result has the full untrimmed input's value. -/
theorem unsigned_value (input : Input) (arena : Delimited.ArenaState) (node : Node)
    (success : (unsigned input arena).result = .ok node) :
    node.value.erase = .uint (Ssz.readUint input.bytes 0 input.bytes.size) := by
  rcases unsigned_refines input arena with semantic | exhausted
  · simpa only [Outcome.erase, success, Except.map, Codec.eraseResult,
      Except.ok.injEq] using semantic
  · simp [Outcome.erase, success, Codec.eraseResult] at exhausted

/-- Success of the accepted Bits constructor already proves the exact packed
byte count; no successful future operation is assumed. -/
private theorem construct_packed (length : NatOperand) (data : Ssz.Bytes) (count : BitVec 128)
    (success : BitVector.construct length data = .ok count) :
    data.size = (count.toNat + 7) / 8 := by
  cases narrowed : NatNarrow.toU128 length with
  | none => simp [BitVector.construct, narrowed] at success
  | some actual =>
    by_cases sized : data.size = (actual.toNat + 7) / 8
    · simp only [BitVector.construct, narrowed, sized, ↓reduceIte, Except.ok.injEq] at success
      subst count
      exact sized
    · simp [BitVector.construct, narrowed, sized] at success

private theorem finish_packed (length expected : NatOperand) (remainder : BitVec 64)
    (data : Ssz.Bytes) (count : BitVec 128)
    (success : BitVector.finish length expected remainder data = .ok count) :
    data.size = (count.toNat + 7) / 8 := by
  unfold BitVector.finish at success
  split at success
  · split at success
    · split at success
      · cases success
      · exact construct_packed _ _ _ success
    · exact construct_packed _ _ _ success
  · cases success

/-- The wrapper's repeated packed guard is unreachable on every successful
provider result, even without a logical bound on the descriptor. -/
theorem bitVector_packed_guard (length : NatOperand) (input : Input)
    (arena : Delimited.ArenaState) (count : BitVec 128)
    (success : (BitVector.run length input.bytes arena).result = .ok count) :
    input.bytes.size = (count.toNat + 7) / 8 := by
  cases divided : (NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    simp only [BitVector.run, divided] at success
    cases success
  | ok pair =>
    rcases pair with ⟨quotient, remainder⟩
    by_cases zero : remainder = 0
    · have finished : BitVector.finish length quotient remainder input.bytes = .ok count := by
        simpa only [BitVector.run, divided, zero, ↓reduceIte] using success
      exact finish_packed _ _ _ _ _ finished
    · cases rounded : (NatAdd.run quotient (.small 1) arena.base arena.capacity
          (NatDivision.run length 8 arena.base arena.capacity arena.used).used).result with
      | error reason =>
        simp only [BitVector.run, divided, zero, ↓reduceIte, rounded] at success
        cases success
      | ok expected =>
        have finished : BitVector.finish length expected remainder input.bytes = .ok count := by
          simpa only [BitVector.run, divided, zero, ↓reduceIte, rounded] using success
        exact finish_packed _ _ _ _ _ finished

private theorem construct_not_scope (length expected : NatOperand) (data : Ssz.Bytes)
    (actual : Nat) :
    BitVector.construct length data ≠ .error (.scope expected actual) := by
  cases narrowed : NatNarrow.toU128 length with
  | none => simp [BitVector.construct, narrowed]
  | some count =>
    by_cases sized : data.size = (count.toNat + 7) / 8 <;>
      simp [BitVector.construct, narrowed, sized]

private theorem finish_scope_actual (length expected reported : NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes) (actual : Nat)
    (rejected : BitVector.finish length expected remainder data =
      .error (.scope reported actual)) : actual = data.size := by
  unfold BitVector.finish at rejected
  split at rejected
  · split at rejected
    · split at rejected
      · cases rejected
      · exact False.elim (construct_not_scope _ _ _ _ rejected)
    · exact False.elim (construct_not_scope _ _ _ _ rejected)
  · cases rejected
    rfl

/-- Scope errors carry the physical input length, making its Small conversion
exact at the recursive error boundary. -/
theorem bitVector_scope_actual (length reported : NatOperand) (input : Input)
    (arena : Delimited.ArenaState) (actual : Nat)
    (rejected : (BitVector.run length input.bytes arena).result =
      .error (.scope reported actual)) : actual = input.bytes.size := by
  cases divided : (NatDivision.run length 8 arena.base arena.capacity arena.used).result with
  | error reason =>
    simp only [BitVector.run, divided] at rejected
    cases rejected
  | ok pair =>
    rcases pair with ⟨quotient, remainder⟩
    by_cases zero : remainder = 0
    · apply finish_scope_actual length quotient reported remainder input.bytes actual
      simpa only [BitVector.run, divided, zero, ↓reduceIte] using rejected
    · cases rounded : (NatAdd.run quotient (.small 1) arena.base arena.capacity
          (NatDivision.run length 8 arena.base arena.capacity arena.used).used).result with
      | error reason =>
        simp only [BitVector.run, divided, zero, ↓reduceIte, rounded] at rejected
        cases rejected
      | ok expected =>
        apply finish_scope_actual length expected reported remainder input.bytes actual
        simpa only [BitVector.run, divided, zero, ↓reduceIte, rounded] using rejected

theorem bitVector_erase (length : NatOperand) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    (bitVector length input arena).erase =
      ((BitVector.run length input.bytes arena).erase input.bytes).mapError Serialize.Host.arithmetic := by
  have actual := count_value input.bytes.size physical
  cases result : (BitVector.run length input.bytes arena).result with
  | ok count =>
    have sized := bitVector_packed_guard length input arena count result
    simp [bitVector, bind, result, packed, sized, unchanged, Outcome.erase,
      BitVector.Outcome.erase, BitVector.eraseResult, Codec.eraseResult, Node.value]
  | error reason =>
    cases reason with
    | scope expected size =>
      have sizeEq := bitVector_scope_actual length expected input arena size result
      simp [bitVector, bind, result, bitVectorError, Outcome.erase, BitVector.Outcome.erase,
        BitVector.eraseResult, Codec.eraseResult, Serialize.eraseResult, sizeEq, actual]
    | arithmetic _ | paddingBits =>
      simp [bitVector, bind, result, bitVectorError, Outcome.erase, BitVector.Outcome.erase,
        BitVector.eraseResult, Codec.eraseResult, Serialize.eraseResult]

theorem bitVector_refines (length : NatOperand) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    (bitVector length input arena).erase = .ok (Ssz.deserialize (.bitVector length.value) input.bytes) ∨
    (bitVector length input arena).erase = .error (.arithmetic .scratchExhausted) := by
  rw [bitVector_erase _ _ _ physical]
  rcases BitVector.run_refines length input.bytes arena physical with semantic | exhausted
  · left; rw [semantic]; rfl
  · right; rw [exhausted]; rfl

/-- The allocated two-word operand and the Small operand both denote the exact
prepared count; their original representations remain at the bound boundary. -/
theorem preparedNumber_value (arena : Delimited.ArenaState) (count : Delimited.CountWords)
    (ready : Delimited.Prepared) (prepared : Delimited.prepare arena count = some ready) :
    (preparedNumber ready).value = ready.count.value := by
  by_cases zero : count.high = 0#64
  · simp [Delimited.prepare, zero] at prepared
    cases prepared
    simp [preparedNumber, NatOperand.value, NatOperand.words, Limbs.value,
      Delimited.CountWords.value, zero]
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none => simp [Delimited.prepare, zero, reserved] at prepared
    | some allocation =>
      simp [Delimited.prepare, zero, reserved] at prepared
      cases prepared
      simp [preparedNumber, NatOperand.value, NatOperand.words, Limbs.value,
        Delimited.CountWords.value]

theorem preparedNumber_data_value (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) (ready : Delimited.Prepared)
    (prepared : Delimited.prepare arena
      (Delimited.countWords input.bytes.size (Ssz.highestBit input.bytes[input.bytes.size - 1]!)) = some ready) :
    (preparedNumber ready).value = BitView.delimitedCount input.bytes ∧
    ready.count.value = BitView.delimitedCount input.bytes := by
  have count := Delimited.prepare_count arena _ ready prepared
  have value : ready.count.value = BitView.delimitedCount input.bytes := by
    rw [count]
    exact Delimited.countWords_data_value _ physical
  exact ⟨(preparedNumber_value _ _ _ prepared).trans value, value⟩

/-- The retained delimiter byte is present exactly when it contains logical
bits, and the u128 count conversion cannot truncate. -/
theorem delimited_packed_guard (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) (nonempty : 0 < input.bytes.size)
    (ready : Delimited.Prepared)
    (prepared : Delimited.prepare arena
      (Delimited.countWords input.bytes.size (Ssz.highestBit input.bytes[input.bytes.size - 1]!)) = some ready) :
    (BitVec.ofNat 128 ready.count.value).toNat = BitView.delimitedCount input.bytes ∧
    (input.bytes.extract 0 (Delimited.retainedBytes input.bytes.size
      (Ssz.highestBit input.bytes[input.bytes.size - 1]!))).size =
      ((BitVec.ofNat 128 ready.count.value).toNat + 7) / 8 := by
  have value := (preparedNumber_data_value input arena physical ready prepared).2
  have bound := BitView.delimited_count_bound input.bytes physical
  have represented : (BitVec.ofNat 128 ready.count.value).toNat = BitView.delimitedCount input.bytes := by
    rw [BitVec.toNat_ofNat, value, Nat.mod_eq_of_lt (by omega)]
  have keep : Delimited.retainedBytes input.bytes.size
      (Ssz.highestBit input.bytes[input.bytes.size - 1]!) ≤ input.bytes.size := by
    unfold Delimited.retainedBytes
    split <;> omega
  refine ⟨represented, ?_⟩
  rw [represented]
  simp only [Array.size_extract, Nat.sub_zero, Nat.min_eq_left keep]
  exact (BitView.delimited_byte_count input.bytes nonempty).symm

/-- A rejected bound retains the native cap and the already prepared actual
operand, not reconstructed Small metadata. -/
theorem prepared_bound_error (cap : NatOperand) (ready : Delimited.Prepared)
    (over : cap.value < (preparedNumber ready).value) :
    (bounded (some cap) (preparedNumber ready) ready.used).result =
      .error (.primitive (.limit cap (preparedNumber ready))) ∧
    (bounded (some cap) (preparedNumber ready) ready.used).used = ready.used := by
  simp [bounded, Serialize.bounded, Serialize.unchanged, Nat.not_le.mpr over]

theorem delimited_refines (limit : Option NatOperand) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    (delimited limit input arena).erase =
      .ok (BitView.delimitedOutcome (limit.map NatOperand.value) input.bytes) ∨
    (delimited limit input arena).erase = .error (.arithmetic .scratchExhausted) := by
  by_cases empty : input.bytes.size = 0
  · left
    simp [delimited, empty, unchanged, Outcome.erase, Codec.eraseResult, BitView.delimitedOutcome]
  · have nonempty : 0 < input.bytes.size := by omega
    by_cases zero : input.bytes[input.bytes.size - 1]! = 0
    · left
      cases scanned : input.bytes.all (· == 0) <;>
        simp only [delimited, empty, zero, ↓reduceIte, Delimited.scanZeros, scanned,
          Bool.false_eq_true, unchanged, Outcome.erase, Except.map,
          Codec.eraseResult, BitView.delimitedOutcome]
    · cases prepared : Delimited.prepare arena (Delimited.countWords input.bytes.size
          (Ssz.highestBit input.bytes[input.bytes.size - 1]!)) with
      | none =>
        right
        simp [delimited, empty, zero, prepared, unchanged, Outcome.erase,
          scratch, Codec.eraseResult, Serialize.eraseResult]
      | some ready =>
        have value := preparedNumber_data_value input arena physical ready prepared
        have guard := delimited_packed_guard input arena physical nonempty ready prepared
        have keep : Delimited.retainedBytes input.bytes.size
            (Ssz.highestBit input.bytes[input.bytes.size - 1]!) =
            (BitView.delimitedCount input.bytes + 7) / 8 :=
          (BitView.delimited_byte_count input.bytes nonempty).symm
        have bits : Ssz.unpackBits (input.bytes.extract 0
            (Delimited.retainedBytes input.bytes.size (Ssz.highestBit input.bytes[input.bytes.size - 1]!)))
            (BitVec.ofNat 128 ready.count.value).toNat =
            Ssz.unpackBits input.bytes (BitView.delimitedCount input.bytes) := by
          rw [guard.1, keep]
          exact BitView.delimited_unpack_retained input.bytes nonempty
        simp only [BitVec.toNat_ofNat, Nat.reducePow] at bits
        left
        cases limit with
        | none =>
          simp [delimited, empty, zero, prepared, bounded, Serialize.bounded,
            Serialize.unchanged, bind, packed, guard.2, unchanged, Outcome.erase,
            Codec.eraseResult, Node.value, bits, BitView.delimitedOutcome]
        | some cap =>
          by_cases fits : BitView.delimitedCount input.bytes ≤ cap.value <;>
            simp [delimited, empty, zero, prepared, bounded, Serialize.bounded,
              Serialize.unchanged, value.1, fits, bind, packed, guard.2, unchanged,
              Outcome.erase, Codec.eraseResult, Serialize.eraseResult, Node.value,
              bits, BitView.delimitedOutcome]

/-- All seven raw primitive declarations refine pinned deserialization. The only
exception is a scratch failure actually returned by the native algorithm; the
sole input premise bounds the physical slice, never logical operands. -/
theorem primitive_erase_refines (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    (primitive shape input arena).erase = .ok (Ssz.deserialize shape.erase input.bytes) ∨
    (primitive shape input arena).erase = .error (.arithmetic .scratchExhausted) := by
  have actual := count_value input.bytes.size physical
  cases shape with
  | bool =>
    left
    change (primitive .bool input arena).erase = .ok (Ssz.deserialize .bool input.bytes)
    rw [← BoolCodec.outcome_eq_deserialize]
    have byteBound : input.bytes[0]!.toNat < 2 ^ 64 := by
      have byte : input.bytes[0]!.toNat < 256 := input.bytes[0]!.toBitVec.isLt
      omega
    have oneValue : (NatOperand.small 1).value = 1 := rfl
    have byteValue : (NatOperand.small (BitVec.ofNat 64 input.bytes[0]!.toNat)).value =
        input.bytes[0]!.toNat := by
      simp only [NatOperand.value, NatOperand.words, Limbs.value, Nat.mul_zero,
        Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt byteBound]
    by_cases sized : input.bytes.size = 1
    · simp only [primitive, exact, oneValue, sized, ↓reduceIte, bind, unchanged,
        BoolCodec.outcome]
      by_cases zero : input.bytes[0]! = 0
      · simp only [zero, ↓reduceIte, Outcome.erase, Except.map, Codec.eraseResult]
        rfl
      · simp only [zero, ↓reduceIte]
        by_cases one : input.bytes[0]! = 1
        · simp only [one, ↓reduceIte, Outcome.erase, Except.map, Codec.eraseResult]
          rfl
        · simp only [one, ↓reduceIte, Outcome.erase, Except.map, Codec.eraseResult, byteValue]
    · simp only [primitive, exact, sized, Ne.symm sized, ↓reduceIte,
        bind, unchanged, Outcome.erase, Except.map, Codec.eraseResult,
        Serialize.eraseResult, BoolCodec.outcome, actual, oneValue]
  | uint width =>
    by_cases scope : width.value = input.bytes.size
    · have unsigned := unsigned_refines input { arena with used := arena.used }
      simpa [primitive, exact, scope, bind, unchanged, Outcome.erase,
        Serialize.Desc.erase, Ssz.deserialize, Pure.pure, Except.pure,
        Bind.bind, Except.bind] using unsigned
    · left
      simp [primitive, exact, scope, bind, unchanged, Outcome.erase,
        Codec.eraseResult, Serialize.eraseResult, Serialize.Desc.erase,
        Ssz.deserialize, actual, Ne.symm scope] <;> rfl
  | byteVector length =>
    left
    by_cases scope : length.value = input.bytes.size
    · simp [primitive, exact, scope, bind, unchanged, Outcome.erase,
        Codec.eraseResult, Serialize.Desc.erase, Ssz.deserialize, Node.value] <;> rfl
    · simp [primitive, exact, scope, bind, unchanged, Outcome.erase,
        Codec.eraseResult, Serialize.eraseResult, Serialize.Desc.erase,
        Ssz.deserialize, actual, Ne.symm scope] <;> rfl
  | byteList limit =>
    left
    by_cases fits : input.bytes.size ≤ limit.value
    · simp [primitive, bounded, Serialize.bounded, Serialize.unchanged, actual, fits,
        bind, unchanged, Outcome.erase, Codec.eraseResult,
        Serialize.Desc.erase, Ssz.deserialize, Node.value,
        Nat.not_lt.mpr fits] <;> rfl
    · simp [primitive, bounded, Serialize.bounded, Serialize.unchanged, actual, fits,
        bind, Outcome.erase, Codec.eraseResult, Serialize.eraseResult,
        Serialize.Desc.erase, Ssz.deserialize, Nat.lt_of_not_ge fits] <;> rfl
  | bitVector length => exact bitVector_refines length input arena physical
  | bitList limit =>
    simpa only [primitive, Serialize.Desc.erase, Option.map_some,
      BitView.list_outcome_eq_deserialize] using delimited_refines (some limit) input arena physical
  | progressiveBitList limit =>
    simpa only [primitive, Serialize.Desc.erase, BitView.progressive_outcome_eq_deserialize]
      using delimited_refines limit input arena physical


/-- Erasure cannot manufacture scratch exhaustion from a semantic or another
host error. This upgrades the public refinement to the actual native result. -/
theorem erase_scratch_iff (outcome : Outcome Node) :
    outcome.erase = .error (.arithmetic .scratchExhausted) ↔
      outcome.result = .error scratch := by
  cases result : outcome.result with
  | ok node => simp [Outcome.erase, result, Codec.eraseResult]
  | error reason =>
    cases reason with
    | primitive reason =>
      cases reason with
      | arithmetic failure =>
        cases failure <;>
          simp [Outcome.erase, result, Codec.eraseResult, Serialize.eraseResult, scratch]
      | wrongType | scope _ _ | limit _ _ | outputTooSmall =>
        simp [Outcome.erase, result, Codec.eraseResult, Serialize.eraseResult, scratch]
    | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
    | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
    | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
    | emptyEncoding | noDelimiter | trailingZeros | noSelector =>
      simp [Outcome.erase, result, Codec.eraseResult, scratch]


/-- Primitive refinement in the shared recursive composition interface. -/
theorem primitive_refines (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Refines nodeErase (primitive shape input arena) (Ssz.deserialize shape.erase input.bytes) := by
  rcases primitive_erase_refines shape input arena physical with semantic | exhausted
  · exact Or.inl semantic
  · exact Or.inr ((erase_scratch_iff _).mp exhausted)

end SszNative.CodecDecode

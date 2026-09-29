import SszHashLayoutPacked
import SszSerializeMeasure

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

@[simp] private theorem except_ok_bind {ε α β : Type} (value : α)
    (next : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= next) = next value := rfl

@[simp] private theorem except_error_bind {ε α β : Type} (reason : ε)
    (next : α → Except ε β) :
    ((Except.error reason : Except ε α) >>= next) = .error reason := rfl

@[simp] private theorem except_ok_map {ε α β : Type} (f : α → β) (value : α) :
    f <$> (Except.ok value : Except ε α) = .ok (f value) := rfl

@[simp] private theorem except_error_map {ε α β : Type} (f : α → β) (reason : ε) :
    f <$> (Except.error reason : Except ε α) = .error reason := rfl

@[simp] private theorem except_pure {ε α : Type} (value : α) :
    (pure value : Except ε α) = .ok value := rfl

private theorem packedBytesExt (left right : Ssz.Bytes) (sized : left.size = right.size)
    (same : ∀ index, index < left.size → left[index]! = right[index]!) : left = right := by
  apply Array.ext sized
  intro index inside otherInside
  simpa only [getElem!_pos, inside, otherInside] using same index inside

private theorem ofFn32_get (f : Fin 32 → UInt8) (index : Nat) (inside : index < 32) :
    (Array.ofFn f)[index]! = f ⟨index, inside⟩ := by
  simp only [getElem!_pos, Array.size_ofFn, inside, Array.getElem_ofFn]

/-- Exactly the native bit-length comparison, including zero-width zero. -/
theorem uintFits_bitLength (width number : NatOperand) :
    Serialize.uintFits width number ↔ Serialize.bitLength number.value ≤ width.value * 8 := by
  unfold Serialize.uintFits Serialize.requiredBytes
  split <;> omega

@[simp] theorem scalar_uint_oversized (width number : NatOperand) (large : 32 < width.value) :
    scalar (.primitive (.uint width)) (.uint number) =
      .error (arithmeticError .badRepresentation) := by
  simp [scalar, Nat.not_le.mpr large]

@[simp] theorem basicWidth_uint_oversized (width : NatOperand) (large : 32 < width.value) :
    basicWidth (.primitive (.uint width)) = .error (arithmeticError .badRepresentation) := by
  simp [basicWidth, Nat.not_le.mpr large]

theorem scalar_uint_rejected (width number : NatOperand) (safe : width.value ≤ 32)
    (wide : width.value * 8 < Serialize.bitLength number.value) :
    scalar (.primitive (.uint width)) (.uint number) = .error wrongType := by
  have notFits : ¬ Serialize.uintFits width number := by
    rw [uintFits_bitLength]
    omega
  simp [scalar, safe, notFits]

theorem scalar_uint_accepted (width number : NatOperand) (safe : width.value ≤ 32)
    (fits : Serialize.uintFits width number) :
    scalar (.primitive (.uint width)) (.uint number) = .ok (number, width.value) := by
  simp [scalar, safe, fits]

@[simp] theorem checkScalars_cons (desc : Desc) (value : Value) (rest : List Value) :
    checkScalars desc (value :: rest) =
      (scalar desc value >>= fun _ => checkScalars desc rest) := rfl

/-- A failed earlier scalar always wins over later validation. -/
theorem checkScalars_first_error (desc : Desc) (value : Value) (rest : List Value)
    (reason : Error) (failed : scalar desc value = .error reason) :
    checkScalars desc (value :: rest) = .error reason := by
  simp [checkScalars, failed]

theorem checkScalars_ok_iff (desc : Desc) (values : List Value) :
    checkScalars desc values = .ok () ↔
      ∀ value ∈ values, ∃ number width, scalar desc value = .ok (number, width) := by
  induction values with
  | nil => simp [checkScalars]
  | cons value rest ih =>
      cases found : scalar desc value with
      | error reason => simp [checkScalars, found]
      | ok pair =>
          rcases pair with ⟨number, width⟩
          simp [checkScalars, found, ih]

/-- Successful scalar validation fixes its basic width without changing operands. -/
theorem scalar_basicWidth (desc : Desc) (value : Value) (number : NatOperand) (width : Nat)
    (checked : scalar desc value = .ok (number, width)) : basicWidth desc = .ok (some width) := by
  cases desc with
  | primitive shape =>
      cases shape <;> cases value <;>
        simp_all [scalar, basicWidth] <;> split at checked <;> simp_all <;>
        split at checked <;> simp_all
  | _ => simp [scalar] at checked

/-- Only bool/uint tags survive the validation loop. -/
theorem scalar_basic_tag (desc : Desc) (value : Value) (number : NatOperand) (width : Nat)
    (checked : scalar desc value = .ok (number, width)) :
    (∃ bit, value = .bool bit) ∨ (∃ operand, value = .uint operand) := by
  cases value <;> simp_all [scalar] <;> cases desc <;> simp_all [scalar] <;>
    rename_i shape <;> cases shape <;> simp_all [scalar]

@[simp] theorem packed_basic_zero_width (values : List Value) (position : Nat) :
    Packed.bytesAt (.basic values 0) position = .ok 0 := by
  simp [Packed.bytesAt]

@[simp] theorem packed_count_bytes (data : Ssz.Bytes) :
    Packed.count (.bytes data) = Ssz.chunksForBytes data.size := by
  simp [Packed.count, Packed.byteCount, Ssz.chunksForBytes, Ssz.bytesPerChunk]

@[simp] theorem packed_count_scalar (number : NatOperand) (width : Nat) :
    Packed.count (.scalar number width) = Ssz.chunksForBytes width := by
  simp [Packed.count, Packed.byteCount, Ssz.chunksForBytes, Ssz.bytesPerChunk]

@[simp] theorem packed_count_basic (values : List Value) (width : Nat) :
    Packed.count (.basic values width) = Ssz.chunksForBytes (values.length * width) := by
  simp [Packed.count, Packed.byteCount, Ssz.chunksForBytes, Ssz.bytesPerChunk]

@[simp] theorem packed_count_bits (data : Serialize.Packed) :
    Packed.count (.bits data) = Ssz.chunksForBits data.count.toNat := by
  simp only [Packed.count, Packed.byteCount, data.sized,
    Ssz.chunksForBits, Ssz.bytesPerChunk]
  omega

/-- Pointwise byte semantics; expanded bytes are a proof specification only. -/
def RepresentsBytes (packed : Packed) (data : Ssz.Bytes) : Prop :=
  packed.byteCount = data.size ∧
    ∀ position, packed.bytesAt position = .ok (if inside : position < data.size then data[position] else 0)

 theorem fillPacked_size (packed : Packed) (start count : Nat) (chunk : Ssz.Bytes)
    (success : fillPacked packed start count = .ok chunk) : chunk.size = 32 := by
  induction count generalizing chunk with
  | zero => simp [fillPacked] at success; cases success; simp
  | succ count ih =>
      cases earlier : fillPacked packed start count with
      | error reason => simp [fillPacked, earlier] at success
      | ok buffer =>
          cases next : packed.bytesAt (start + count) with
          | error reason => simp [fillPacked, earlier, next] at success
          | ok byte =>
              simp [fillPacked, earlier, next] at success
              cases success
              simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using
                ih buffer earlier

 theorem packedChunk_size (packed : Packed) (index : Nat) (chunk : Ssz.Bytes)
    (success : packedChunk packed index = .ok chunk) : chunk.size = 32 :=
  fillPacked_size packed (index * 32) 32 chunk success

/-- The loop invariant retains the copied prefix and untouched zero suffix. -/
theorem fillPacked_spec (packed : Packed) (start count : Nat) (small : count ≤ 32)
    (byte : Nat → UInt8) (reads : ∀ offset, offset < count →
      packed.bytesAt (start + offset) = .ok (byte offset)) :
    fillPacked packed start count =
      .ok (Array.ofFn fun offset : Fin 32 => if offset.val < count then byte offset.val else 0) := by
  induction count with
  | zero =>
      rw [fillPacked]
      apply congrArg Except.ok
      apply packedBytesExt
      · simp only [Array.size_replicate, Array.size_ofFn]
      · intro offset inside
        have bound : offset < 32 := by simpa only [Array.size_replicate] using inside
        rw [ofFn32_get _ offset bound]
        simp only [getElem!_pos, Array.size_replicate, bound, Array.getElem_replicate,
          Nat.not_lt_zero, ↓reduceIte]
  | succ count ih =>
      rw [fillPacked, ih (by omega) (by intro offset inside; exact reads offset (by omega)),
        reads count (by omega)]
      change Except.ok ((Array.ofFn fun offset : Fin 32 =>
        if offset.val < count then byte offset.val else 0).set! count (byte count)) = _
      apply congrArg Except.ok
      apply packedBytesExt
      · simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_ofFn]
      · intro offset inside
        have bound : offset < 32 := by
          simpa only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
            Array.size_ofFn] using inside
        rw [MerkleWords.setByte_get _ _ _ _ (by simpa only [Array.size_ofFn] using bound),
          ofFn32_get _ offset bound, ofFn32_get _ offset bound]
        by_cases last : count = offset
        · subst offset
          simp only [↓reduceIte, show count < count + 1 by omega]
        · by_cases copied : offset < count
          · simp only [last, copied, show offset < count + 1 by omega, ↓reduceIte]
          · simp only [last, copied, show ¬ offset < count + 1 by omega, ↓reduceIte]

/-- No successful prior check can later produce WrongType during basic packing. -/
theorem basic_bytesAt_success (desc : Desc) (values : List Value) (width position : Nat)
    (checked : checkScalars desc values = .ok ()) :
    ∃ byte, Packed.bytesAt (.basic values width) position = .ok byte := by
  simp only [Packed.bytesAt]
  split
  · rename_i inside
    have member := List.getElem_mem (l := values) (n := position / width)
      (basic_index_bound values width position inside)
    obtain ⟨number, actualWidth, valid⟩ := (checkScalars_ok_iff desc values).mp checked _ member
    rcases scalar_basic_tag desc _ number actualWidth valid with ⟨bit, tag⟩ | ⟨operand, tag⟩
    · rw [tag]; exact ⟨_, rfl⟩
    · rw [tag]; exact ⟨_, rfl⟩
  · exact ⟨0, rfl⟩

theorem fillPacked_success (packed : Packed) (start count : Nat)
    (reads : ∀ position, ∃ byte, packed.bytesAt position = .ok byte) :
    ∃ chunk, fillPacked packed start count = .ok chunk := by
  induction count with
  | zero => exact ⟨_, rfl⟩
  | succ count ih =>
      obtain ⟨chunk, previous⟩ := ih
      obtain ⟨byte, next⟩ := reads (start + count)
      exact ⟨chunk.set! count byte, by simp [fillPacked, previous, next]⟩

theorem basic_packedChunk_success (desc : Desc) (values : List Value) (width index : Nat)
    (checked : checkScalars desc values = .ok ()) :
    ∃ chunk, packedChunk (.basic values width) index = .ok chunk ∧ chunk.size = 32 := by
  obtain ⟨chunk, success⟩ := fillPacked_success (.basic values width) (index * 32) 32
    (fun position => basic_bytesAt_success desc values width position checked)
  exact ⟨chunk, success, packedChunk_size _ _ _ success⟩

/-- Indexed bytes of the pinned padding-and-slicing operation. -/
theorem packBytes_chunk (data : Ssz.Bytes) (index : Nat)
    (inside : index < (Ssz.packBytes data).size) :
    (Ssz.packBytes data)[index] = Array.ofFn (fun offset : Fin 32 =>
      if h : index * 32 + offset.val < data.size then data[index * 32 + offset.val] else 0) := by
  simp only [Ssz.packBytes, Array.getElem_ofFn, Ssz.bytesPerChunk]
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract, Array.size_replicate, Array.size_ofFn]
    omega
  · intro offset left right
    have small : offset < 32 := by simpa using right
    by_cases copied : index * 32 + offset < data.size
    · have piece : offset < min (index * 32 + 32) data.size - index * 32 := by omega
      simp only [Array.getElem_append, Array.size_extract, piece,
        ↓reduceDIte, Array.getElem_extract, Array.getElem_ofFn, copied]
    · have piece : ¬ offset < min (index * 32 + 32) data.size - index * 32 := by omega
      simp [Array.getElem_append, Array.size_extract, piece, copied]

 theorem packed_count_refines (packed : Packed) (data : Ssz.Bytes)
    (rep : RepresentsBytes packed data) : packed.count = (Ssz.packBytes data).size := by
  simp [Packed.count, rep.1, Ssz.packBytes, Ssz.bytesPerChunk]

 theorem packedChunk_refines (packed : Packed) (data : Ssz.Bytes)
    (rep : RepresentsBytes packed data) (index : Nat) (inside : index < packed.count) :
    packedChunk packed index = .ok ((Ssz.packBytes data)[index]'(by
      rw [← packed_count_refines packed data rep]; exact inside)) := by
  rw [packBytes_chunk]
  unfold packedChunk
  have filled := fillPacked_spec packed (index * 32) 32 (by omega)
    (fun offset => if h : index * 32 + offset < data.size then data[index * 32 + offset] else 0)
    (fun offset _ => rep.2 _)
  simpa using filled

 theorem bytes_represents (data : Ssz.Bytes) : RepresentsBytes (.bytes data) data := by
  exact ⟨rfl, fun _ => rfl⟩

 theorem scalar_represents (number : NatOperand) (width : Nat) :
    RepresentsBytes (.scalar number width) (Ssz.uintBytes width number.value) := by
  constructor
  · simp [Packed.byteCount, Ssz.uintBytes_size]
  · intro position
    by_cases inside : position < width
    · simp only [Packed.bytesAt, inside, Ssz.uintBytes_size, ↓reduceDIte, ↓reduceIte]
      congr 1
      rw [Limbs.byteAt_eq_value, Limbs.uintBytes_byte width number.value position inside]
      rfl
    · simp [Packed.bytesAt, Ssz.uintBytes_size, inside]

 theorem bits_represents (data : Serialize.Packed) :
    RepresentsBytes (.bits data) (PackedBits.canonicalBytes data.bytes data.count.toNat) := by
  have size : (PackedBits.canonicalBytes data.bytes data.count.toNat).size = data.bytes.size := by
    rw [← PackedBits.packBits_unpackBits_canonicalBytes _ _ data.sized]
    simpa [Ssz.packBits] using data.sized.symm
  constructor
  · exact size.symm
  · intro position
    by_cases inside : position < data.bytes.size
    · have floor : data.count.toNat / 8 ≤ data.bytes.size := by rw [data.sized]; omega
      have bulk : (data.bytes.extract 0 (data.count.toNat / 8)).size = data.count.toNat / 8 := by
        simp [Array.size_extract, Nat.min_eq_left floor]
      by_cases aligned : data.count.toNat % 8 = 0
      · have before : position < data.count.toNat / 8 := by rw [data.sized] at inside; omega
        simp only [Packed.bytesAt, inside, ↓reduceDIte, aligned,
          ↓reduceIte, PackedBits.canonicalBytes, Array.append_empty,
          Array.size_extract, Nat.sub_zero, Nat.min_eq_left floor, before,
          Array.getElem_extract, Nat.zero_add]
        simp
      · by_cases before : position < data.count.toNat / 8
        · have room : position < data.count.toNat / 8 + 1 := by omega
          simp [Packed.bytesAt, inside, PackedBits.canonicalBytes, aligned, bulk,
            Array.getElem_push, room, before, show position ≠ data.count.toNat / 8 by omega]
        · have last : position = data.count.toNat / 8 := by rw [data.sized] at inside; omega
          subst position
          simp [Packed.bytesAt, inside, PackedBits.canonicalBytes, aligned,
            Array.getElem_push, bulk, getElem!_pos]
    · simp [Packed.bytesAt, size, inside]

 theorem packedChunk_bytes (data : Ssz.Bytes) (index : Nat)
    (inside : index < Packed.count (.bytes data)) :
    packedChunk (.bytes data) index = .ok ((Ssz.packBytes data)[index]'(by
      rw [← packed_count_refines _ _ (bytes_represents data)]; exact inside)) :=
  packedChunk_refines _ _ (bytes_represents data) index inside

 theorem packedBits_eq (data : Serialize.Packed) :
    Ssz.packedBits (Ssz.unpackBits data.bytes data.count.toNat) =
      Ssz.packBytes (PackedBits.canonicalBytes data.bytes data.count.toNat) := by
  simp only [Ssz.packedBits, Packing.unpackBits_size,
    PackedBits.packBits_unpackBits_canonicalBytes _ _ data.sized]

/-- A scalar's original operand encodes exactly the bytes accepted upstream. -/
theorem scalar_serializes (desc : Desc) (value : Value) (number : NatOperand) (width : Nat)
    (checked : scalar desc value = .ok (number, width)) :
    Ssz.serialize desc.erase value.erase = .ok (Ssz.uintBytes width number.value) := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool =>
          cases value <;> simp only [scalar] at checked
          case bool bit =>
            cases checked
            cases bit <;> simp [Codec.Desc.erase, Serialize.Desc.erase, Codec.Value.erase,
              Ssz.serialize, Serialize.count, NatOperand.value, NatOperand.words, Limbs.value,
              Ssz.uintBytes]
          all_goals cases checked
      | uint declared =>
          cases value <;> simp only [scalar] at checked
          case uint operand =>
            split at checked
            · split at checked
              · cases checked
                rename_i safe fits
                simp [Codec.Desc.erase, Serialize.Desc.erase, Codec.Value.erase,
                  Ssz.serialize, (Serialize.uintFits_iff declared number).mp fits]
              · cases checked
            · cases checked
          all_goals cases checked
      | _ => cases value <;> simp [scalar] at checked
  | _ => simp [scalar] at checked

/-- Safe raw widths refine rejections as well as successes; no schema-normalized
integer-width assumption is needed. -/
theorem scalar_refines (desc : Desc) (value : Value) (width : Nat)
    (basic : basicWidth desc = .ok (some width)) :
    eraseResult ((scalar desc value).map fun pair => Ssz.uintBytes pair.2 pair.1.value) =
      .ok (Ssz.serialize desc.erase value.erase) := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool =>
          cases value <;> simp [scalar, eraseResult, wrongType, Codec.eraseResult,
            Serialize.eraseResult, Codec.Desc.erase, Serialize.Desc.erase,
            Codec.Value.erase, Ssz.serialize, Except.map]
          rename_i bit
          cases bit <;> simp [Serialize.count, NatOperand.value, NatOperand.words,
            Limbs.value, Ssz.uintBytes]
      | uint declared =>
          have safe : declared.value ≤ 32 := by
            by_cases yes : declared.value ≤ 32
            · exact yes
            · simp [basicWidth, yes] at basic
          cases value <;> simp [scalar, safe, eraseResult, wrongType, Codec.eraseResult,
            Serialize.eraseResult, Codec.Desc.erase, Serialize.Desc.erase,
            Codec.Value.erase, Ssz.serialize, Except.map, ← Serialize.uintFits_iff]
          rename_i number
          by_cases fits : Serialize.uintFits declared number <;>
            simp only [fits, ↓reduceIte] <;> rfl
      | _ => simp [basicWidth] at basic
  | _ => simp [basicWidth] at basic

/-- Mathematical byte of a basic value, used only by the concatenation proof. -/
def scalarByte (value : Value) (position : Nat) : Except Error UInt8 :=
  match value with
  | .bool bit => .ok (if bit then 1 else 0)
  | .uint number => .ok (Limbs.byteAt number.words position)
  | _ => .error wrongType

def ScalarPart (value : Value) (width : Nat) (part : Ssz.Bytes) : Prop :=
  part.size = width ∧ ∀ position (inside : position < part.size),
    scalarByte value position = .ok part[position]

theorem scalar_part (desc : Desc) (value : Value) (number : NatOperand) (width : Nat)
    (checked : scalar desc value = .ok (number, width)) :
    ScalarPart value width (Ssz.uintBytes width number.value) := by
  constructor
  · exact Ssz.uintBytes_size _ _
  · intro position inside
    have within : position < width := by simpa only [Ssz.uintBytes_size] using inside
    cases desc with
    | primitive shape =>
        cases shape with
        | bool =>
            cases value <;> simp only [scalar] at checked
            case bool bit =>
              cases checked
              have zero : position = 0 := by omega
              subst position
              cases bit <;> simp [scalarByte, Serialize.count, NatOperand.value,
                NatOperand.words, Limbs.value, Ssz.uintBytes]
            all_goals cases checked
        | uint declared =>
            cases value <;> simp only [scalar] at checked
            case uint operand =>
              split at checked
              · split at checked
                · cases checked
                  simp only [scalarByte]
                  congr 1
                  rw [Limbs.byteAt_eq_value,
                    Limbs.uintBytes_byte declared.value number.value position within]
                  rfl
                · cases checked
              · cases checked
            all_goals cases checked
        | _ => cases value <;> simp [scalar] at checked
    | _ => simp [scalar] at checked

theorem basic_cons_represents (value : Value) (values : List Value) (width : Nat)
    (part rest : Ssz.Bytes) (first : ScalarPart value width part)
    (later : RepresentsBytes (.basic values width) rest) :
    RepresentsBytes (.basic (value :: values) width) (part ++ rest) := by
  have total : (part ++ rest).size = (value :: values).length * width := by
    simp only [Array.size_append, first.1, ← later.1, Packed.byteCount,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega
  constructor
  · exact total.symm
  · intro position
    by_cases inside : position < (values.length + 1) * width
    · have positive : 0 < width := by
        by_cases zero : width = 0
        · simp [zero] at inside
        · omega
      by_cases before : position < width
      · have quotient : position / width = 0 := Nat.div_eq_of_lt before
        have remainder : position % width = position := Nat.mod_eq_of_lt before
        have within : position < part.size := by rw [first.1]; exact before
        simp [Packed.bytesAt, inside, total, quotient, remainder,
          first.1, before]
        exact first.2 position within
      · have shifted : position - width < values.length * width := by
          simp only [Nat.add_mul, Nat.one_mul] at inside
          omega
        have sum : position = (position - width) + width := by omega
        have quotient : position / width = (position - width) / width + 1 :=
          (congrArg (fun n => n / width) sum).trans (Nat.add_div_right _ positive)
        have remainder : position % width = (position - width) % width :=
          (congrArg (fun n => n % width) sum).trans (Nat.add_mod_right _ _)
        have next := later.2 (position - width)
        have restSize : rest.size = values.length * width := later.1.symm
        simp only [Packed.bytesAt, shifted, ↓reduceDIte, restSize] at next
        simpa [Packed.bytesAt, inside, total, quotient, remainder,
          Array.getElem_append, first.1, before] using next
    · simp [Packed.bytesAt, inside, total]

/-- Concatenation is a specification, never part of chunk execution. -/
def concatParts : List Ssz.Bytes → Ssz.Bytes
  | [] => #[]
  | part :: rest => part ++ concatParts rest

theorem concatParts_fold (parts : List Ssz.Bytes) (initial : Ssz.Bytes) :
    parts.foldl (fun total part => total ++ part) initial = initial ++ concatParts parts := by
  induction parts generalizing initial with
  | nil => simp [concatParts]
  | cons part rest ih => simp [concatParts, ih, Array.append_assoc]

/-- Ordered validation constructs a mathematical witness of upstream serializeEach,
with the exact physical packed length and every indexed native byte. -/
theorem checkScalars_serializes (desc : Desc) (values : List Value) (width : Nat)
    (basic : basicWidth desc = .ok (some width))
    (checked : checkScalars desc values = .ok ()) :
    ∃ parts, Ssz.serializeEach desc.erase (Codec.Value.eraseList values) = .ok parts ∧
      RepresentsBytes (.basic values width) (concatParts parts) := by
  induction values with
  | nil =>
      refine ⟨[], by simp only [Codec.Value.eraseList, Ssz.serializeEach], ?_⟩
      constructor
      · simp [Packed.byteCount, concatParts]
      · intro position; simp [Packed.bytesAt, concatParts]
  | cons value rest ih =>
      obtain ⟨number, actualWidth, valid⟩ :=
        (checkScalars_ok_iff desc (value :: rest)).mp checked value (by simp)
      have same := scalar_basicWidth desc value number actualWidth valid
      rw [basic] at same
      have widths : actualWidth = width := by simpa using same.symm
      subst actualWidth
      have tailChecked : checkScalars desc rest = .ok () := by
        simpa [checkScalars, valid] using checked
      obtain ⟨parts, serialized, represented⟩ := ih tailChecked
      refine ⟨Ssz.uintBytes width number.value :: parts, ?_, ?_⟩
      · simp [Codec.Value.eraseList, Ssz.serializeEach,
          scalar_serializes desc value number width valid, serialized]
      · exact basic_cons_represents value rest width _ _ (scalar_part _ _ _ _ valid) represented

/-- Basic sequences pack precisely serializeEach's bytes, even when a scalar
straddles a chunk boundary; the descriptor width can be zero or any raw width ≤32. -/
theorem basic_packElements_refines (desc : Desc) (values : List Value) (width : Nat)
    (basic : basicWidth desc = .ok (some width))
    (checked : checkScalars desc values = .ok ()) :
    ∃ parts, Ssz.serializeEach desc.erase (Codec.Value.eraseList values) = .ok parts ∧
      Packed.count (.basic values width) = (Ssz.packElements parts).size ∧
      ∀ index, index < Packed.count (.basic values width) →
        packedChunk (.basic values width) index =
          .ok ((Ssz.packElements parts)[index]?.getD Ssz.zeroChunk) := by
  obtain ⟨parts, serialized, represented⟩ :=
    checkScalars_serializes desc values width basic checked
  have counted : Packed.count (.basic values width) = (Ssz.packElements parts).size := by
    simpa [Ssz.packElements, concatParts_fold] using
      packed_count_refines (.basic values width) (concatParts parts) represented
  refine ⟨parts, serialized, counted, ?_⟩
  intro index inside
  have found : index < (Ssz.packElements parts).size := by omega
  rw [Array.getElem?_eq_getElem found, Option.getD_some]
  simpa [Ssz.packElements, concatParts_fold] using
    packedChunk_refines (.basic values width) (concatParts parts) represented index inside

theorem packed_count_bytes_physical (data : Ssz.Bytes) (physical : data.size < 2 ^ 64) :
    Packed.count (.bytes data) < 2 ^ 64 := by
  simp only [Packed.count, Packed.byteCount]
  omega

theorem packed_count_bits_physical (data : Serialize.Packed)
    (physical : data.bytes.size < 2 ^ 64) : Packed.count (.bits data) < 2 ^ 64 := by
  simp only [Packed.count, Packed.byteCount]
  omega

theorem packed_count_scalar_physical (number : NatOperand) (width : Nat)
    (safe : width ≤ 32) : Packed.count (.scalar number width) < 2 ^ 64 := by
  simp only [Packed.count, Packed.byteCount]
  omega

theorem packed_count_basic_physical (values : List Value) (width : Nat)
    (physical : values.length < 2 ^ 64) (safe : width ≤ 32) :
    Packed.count (.basic values width) < 2 ^ 64 := by
  have product := Nat.mul_le_mul_left values.length safe
  simp only [Packed.count, Packed.byteCount]
  omega

theorem basicWidth_bound (desc : Desc) (width : Nat)
    (basic : basicWidth desc = .ok (some width)) : width ≤ 32 := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool => simp only [basicWidth, Except.ok.injEq, Option.some.injEq] at basic; omega
      | uint declared =>
          simp only [basicWidth] at basic
          split at basic <;> simp_all
      | _ => simp [basicWidth] at basic
  | _ => simp [basicWidth] at basic

theorem scalar_error_reason (desc : Desc) (value : Value) (width : Nat) (reason : Error)
    (basic : basicWidth desc = .ok (some width))
    (failed : scalar desc value = .error reason) : reason = wrongType := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool => cases value <;> simp_all [scalar]
      | uint declared =>
          have safe : declared.value ≤ 32 := by
            by_cases yes : declared.value ≤ 32
            · exact yes
            · simp [basicWidth, yes] at basic
          cases value <;> simp_all [scalar]
          split at failed <;> simp_all
      | _ => simp [basicWidth] at basic
  | _ => simp [basicWidth] at basic

/-- Both ordered semantic rejection and acceptance agree with serializeEach.
The only additional native rejection is the separate unsafe raw-width branch. -/
theorem checkScalars_refines (desc : Desc) (values : List Value) (width : Nat)
    (basic : basicWidth desc = .ok (some width)) :
    eraseResult (checkScalars desc values) =
      .ok ((Ssz.serializeEach desc.erase (Codec.Value.eraseList values)).map fun _ => ()) := by
  induction values with
  | nil => simp only [checkScalars, Codec.Value.eraseList, Ssz.serializeEach, Except.map, eraseResult]
  | cons value rest ih =>
      cases checked : scalar desc value with
      | ok pair =>
          rcases pair with ⟨number, actualWidth⟩
          have serialized := scalar_serializes desc value number actualWidth checked
          simp only [checkScalars, checked, except_ok_bind]
          rw [ih]
          simp only [Codec.Value.eraseList, Ssz.serializeEach, serialized, except_ok_bind]
          cases Ssz.serializeEach desc.erase (Codec.Value.eraseList rest) <;> rfl
      | error reason =>
          have reasonIs := scalar_error_reason desc value width reason basic checked
          subst reason
          have semantic := scalar_refines desc value width basic
          rw [checked] at semantic
          have rejected : Ssz.serialize desc.erase value.erase = .error .typeMismatch := by
            simpa [Except.map, eraseResult, wrongType, Codec.eraseResult,
              Serialize.eraseResult] using semantic.symm
          simp [checkScalars, checked, Codec.Value.eraseList, Ssz.serializeEach,
            rejected, eraseResult, wrongType, Codec.eraseResult, Serialize.eraseResult, Except.map]

end SszNative.HashLayout

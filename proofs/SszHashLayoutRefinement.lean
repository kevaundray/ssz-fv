import SszHashLayoutRefinementCore

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

private theorem guarded_true {α : Type} {condition : Prop} [Decidable condition]
    (holds : condition) (yes no : α) : (if condition then yes else no) = yes := by
  simp only [holds, ↓reduceIte]

private theorem guarded_false {α : Type} {condition : Prop} [Decidable condition]
    (fails : ¬condition) (yes no : α) : (if condition then yes else no) = no := by
  simp only [fails, ↓reduceIte]

theorem basicWidth_safe (desc : Desc) (safe : SafeWidths desc) :
    ∃ width, basicWidth desc = .ok width := by
  cases desc with
  | primitive shape => cases shape <;> simp_all [SafeWidths, basicWidth]
  | _ => exact ⟨none, rfl⟩

theorem basicWidth_some (desc : Desc) (width : Nat)
    (basic : basicWidth desc = .ok (some width)) :
    desc.erase.isBasic = true ∧ desc.erase.itemLength = width := by
  cases desc with
  | primitive shape =>
      cases shape <;> simp_all [basicWidth, Desc.erase, Serialize.Desc.erase,
        Ssz.Desc.isBasic, Ssz.Desc.itemLength]
      split at basic <;> simp_all
  | _ => simp [basicWidth] at basic

theorem basicWidth_none (desc : Desc) (notBasic : basicWidth desc = .ok none) :
    desc.erase.isBasic = false := by
  cases desc with
  | primitive shape =>
      cases shape <;> simp_all [basicWidth, Desc.erase, Serialize.Desc.erase, Ssz.Desc.isBasic]
      split at notBasic <;> simp_all
  | _ => rfl

theorem sequence_refines (element : Desc) (values : List Value) (positions : Option NatOperand)
    (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState) (safe : SafeWidths element) :
    Refines LayoutRefines (sequence element values positions mixin arena)
      (Ssz.sequenceLayout element.erase (Value.eraseList values)
        (positions.map NatOperand.value) mixin) := by
  obtain ⟨width, basic⟩ := basicWidth_safe element safe
  rw [sequence, basic]
  simp only [lift, bind_ok]
  cases width with
  | none =>
      have composite := basicWidth_none element basic
      simp only [Ssz.sequenceLayout, composite, Bool.false_eq_true, ↓reduceIte]
      exact .ok _ _ (nesting_refines (.sequence element values) _
        (Nested.sequence_count element values) (Nested.sequence_at element values) positions mixin)
  | some width =>
      obtain ⟨isBasic, itemLength⟩ := basicWidth_some element width basic
      cases checked : checkScalars element values with
      | error reason =>
          have validation := checkScalars_refines element values width basic
          rw [checked] at validation
          cases serialized : Ssz.serializeEach element.erase (Value.eraseList values) with
          | error fault =>
              simp only [serialized, Except.map] at validation
              simp only [Ssz.sequenceLayout, isBasic, ↓reduceIte, serialized]
              dsimp only [lift, bind, unchanged, Bind.bind, Except.bind]
              exact .error reason fault validation
          | ok parts =>
              simp only [serialized, Except.map] at validation
              cases reason with
              | codec reason =>
                  cases reason with
                  | primitive reason => cases reason <;> cases validation
                  | _ => cases validation
              | merkle reason => cases reason <;> cases validation
              | _ => cases validation
      | ok checkedUnit =>
          cases checkedUnit
          obtain ⟨parts, serialized, represented⟩ :=
            checkScalars_serializes element values width basic checked
          have chunks : Ssz.packElements parts = Ssz.packBytes (concatParts parts) := by
            simp [Ssz.packElements, concatParts_fold]
          simp only [bind_ok, Ssz.sequenceLayout, isBasic, ↓reduceIte, serialized]
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          cases positions with
          | none =>
              apply ResultRefines.ok
              simpa only [chunks, Option.map] using packing_refines (.basic values width)
                (concatParts parts) represented none mixin
          | some position =>
              have widthBound : width < 2 ^ 64 := by
                have bound := basicWidth_bound element width basic
                omega
              cases multiplied : (mul position (Serialize.count width) arena).result with
              | error reason =>
                  have exhausted := mul_onlyExhaustion position (Serialize.count width) arena reason multiplied
                  subst reason
                  simp only [Refines, bind, multiplied]
                  exact .exhausted _
              | ok bytes =>
                  have bytesValue := mul_value position (Serialize.count width) arena bytes multiplied
                  rw [Serialize.count_value width widthBound] at bytesValue
                  let cursor := { arena with used := (mul position (Serialize.count width) arena).used }
                  cases divided : (ceilDiv bytes 32 cursor).result with
                  | error reason =>
                      have exhausted := ceilDiv_onlyExhaustion bytes 32 cursor (by decide) reason divided
                      subst reason
                      dsimp only [cursor] at divided
                      simp only [Refines, bind, multiplied, divided]
                      exact .exhausted _
                  | ok capacity =>
                      have capacityValue := ceilDiv_value bytes 32 cursor (by decide) capacity divided
                      have exactCapacity : capacity.value = Ssz.chunksForBytes (position.value * width) := by
                        change capacity.value = (position.value * width + 32 - 1) / 32
                        change capacity.value = (bytes.value + 32 - 1) / 32 at capacityValue
                        rw [bytesValue] at capacityValue
                        exact capacityValue
                      dsimp only [cursor] at divided
                      simp only [Refines, bind, multiplied, divided]
                      apply ResultRefines.ok
                      have relation := packing_refines (.basic values width) (concatParts parts)
                        represented (some capacity) mixin
                      simpa only [chunks, Option.map, exactCapacity, itemLength] using relation

private theorem scalar_layout_refines (desc : Desc) (value : Value) (width : Nat)
    (basic : basicWidth desc = .ok (some width)) (arena : Delimited.ArenaState) :
    Refines LayoutRefines
      (bind (lift arena.used (scalar desc value)) fun pair used =>
        unchanged used (.ok ⟨.packed (.scalar pair.1 pair.2),
          some (Serialize.count ((pair.2 + 31) / 32)), none⟩))
      (Ssz.fixedLeaf desc.erase value.erase) := by
  cases checked : scalar desc value with
  | error reason =>
      have validation := scalar_refines desc value width basic
      rw [checked] at validation
      have reasonEq := scalar_error_reason desc value width reason basic checked
      subst reason
      have rejected : Ssz.serialize desc.erase value.erase = .error .typeMismatch := by
        simpa only [Except.map, eraseResult, wrongType, Codec.eraseResult,
          Serialize.eraseResult, Except.ok.injEq] using validation.symm
      dsimp only [lift, bind, unchanged, Ssz.fixedLeaf]
      rw [rejected]
      dsimp only [Bind.bind, Except.bind]
      exact .error wrongType .typeMismatch rfl
  | ok pair =>
      rcases pair with ⟨number, actualWidth⟩
      have actualBasic := scalar_basicWidth desc value number actualWidth checked
      have bound := basicWidth_bound desc actualWidth actualBasic
      have countBound : (actualWidth + 31) / 32 < 2 ^ 64 := by omega
      have serialized := scalar_serializes desc value number actualWidth checked
      dsimp only [lift, bind, unchanged, Ssz.fixedLeaf]
      rw [serialized]
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      apply ResultRefines.ok
      have relation := packing_refines (.scalar number actualWidth)
        (Ssz.uintBytes actualWidth number.value) (scalar_represents number actualWidth)
        (some (Serialize.count ((actualWidth + 31) / 32))) none
      have rounding : actualWidth + 32 - 1 = actualWidth + 31 := by omega
      simpa only [Option.map, Serialize.count_value _ countBound,
        Ssz.packBytes, Ssz.uintBytes_size, Array.size_ofFn, Ssz.bytesPerChunk, rounding] using relation

private theorem packing_capacity_refines (packed : Packed) (bytes : Ssz.Bytes)
    (represented : RepresentsBytes packed bytes) (capacity : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (mixin : Option Ssz.Bytes) (nonzero : divisor ≠ 0) :
    Refines LayoutRefines
      (bind (ceilDiv capacity divisor arena) fun limit used =>
        unchanged used (.ok ⟨.packed packed, some limit, mixin⟩))
      (.ok (Ssz.MerkleLayout.packing (Ssz.packBytes bytes)
        (some ((capacity.value + divisor.toNat - 1) / divisor.toNat)) mixin)) := by
  cases divided : (ceilDiv capacity divisor arena).result with
  | error reason =>
      have exhausted := ceilDiv_onlyExhaustion capacity divisor arena nonzero reason divided
      subst reason
      simp only [bind, divided]
      exact .exhausted _
  | ok limit =>
      have arithmetic := ceilDiv_value capacity divisor arena nonzero limit divided
      simp only [bind, divided, unchanged]
      apply ResultRefines.ok
      simpa only [Option.map, arithmetic] using
        packing_refines packed bytes represented (some limit) mixin

private theorem count_error_refines (expected : NatOperand) (actual : BitVec 128)
    (arena : Delimited.ArenaState) (limit : Bool) :
    Refines LayoutRefines
      (bind (fromWide actual arena) fun operand used => unchanged used
        (.error (.codec (.primitive (if limit then .limit expected operand else .scope expected operand)))))
      (.error (if limit then .overLimit expected.value actual.toNat else .scope expected.value actual.toNat)) := by
  cases constructed : (fromWide actual arena).result with
  | error reason =>
      have exhausted := fromWide_onlyExhaustion actual arena reason constructed
      subst reason
      simp only [bind, constructed]
      exact .exhausted _
  | ok operand =>
      have number := fromWide_value actual arena operand constructed
      simp only [bind, constructed, unchanged]
      apply ResultRefines.error
      cases limit <;> simp only [Bool.false_eq_true, ↓reduceIte, eraseResult, Codec.eraseResult,
        Serialize.eraseResult, number]

private theorem countWord_nat (count : Nat) (physical : count < 2 ^ 64) :
    countWord128 (BitVec.ofNat 128 count) = Ssz.lengthWord count := by
  rw [countWord128_eq_lengthWord]
  have wide : count < 2 ^ 128 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide]

private theorem activeCount_le (active : List Bool) : active.countP id ≤ active.length := by
  induction active with
  | nil => simp
  | cons bit rest ih => cases bit <;> simp_all <;> omega

/-- Raw layout success and rejection agree with the pinned definition on the
source-supported recursive width and physical-slice domain. Only an actually
returned arithmetic scratch failure may interrupt this agreement. -/
theorem layout_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical) :
    Refines LayoutRefines (layout desc value arena) (Ssz.merkleLayout desc.erase value.erase) := by
  cases desc with
  | primitive shape =>
      cases shape with
      | bool =>
          exact scalar_layout_refines (.primitive .bool) value 1 rfl arena
      | uint width =>
          exact scalar_layout_refines (.primitive (.uint width)) value width.value
            (by simp only [basicWidth, show width.value ≤ 32 from safe, ↓reduceIte]) arena
      | byteVector length =>
          cases value with
          | bytes data =>
              have physical : data.size < 2 ^ 64 := valuePhysical
              by_cases matched : length.value = data.size
              · have countBound : (data.size + 31) / 32 < 2 ^ 64 := by omega
                simp only [layout, guarded_true matched, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Ssz.fixedLeaf, Ssz.serialize,
                  show (data.size == length.value) = true from by simp [matched],
                  ↓reduceIte]
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                apply ResultRefines.ok
                have relation := packing_refines (.bytes data) data (bytes_represents data)
                  (some (Serialize.count ((data.size + 31) / 32))) none
                have rounding : data.size + 32 - 1 = data.size + 31 := by omega
                simpa only [Option.map, Serialize.count_value _ countBound,
                  Ssz.packBytes, Array.size_ofFn, Ssz.bytesPerChunk, rounding] using relation
              · simp only [layout, matched, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Ssz.fixedLeaf, Ssz.serialize,
                  show (data.size == length.value) = false from by simp [Ne.symm matched],
                  Bool.false_eq_true, ↓reduceIte]
                dsimp only [Bind.bind, Except.bind]
                apply ResultRefines.error
                simp only [eraseResult, Codec.eraseResult, Serialize.eraseResult,
                  Serialize.count_value data.size physical]
          | _ =>
              dsimp only [layout, Desc.erase, Serialize.Desc.erase, Value.erase,
                Ssz.merkleLayout, Ssz.fixedLeaf, Ssz.serialize, Bind.bind, Except.bind]
              simp only [Ssz.serialize]
              exact .error wrongType .typeMismatch rfl
      | byteList limit =>
          cases value with
          | bytes data =>
              have physical : data.size < 2 ^ 64 := valuePhysical
              by_cases over : limit.value < data.size
              · simp only [layout, over, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout]
                apply ResultRefines.error
                simp only [eraseResult, Codec.eraseResult, Serialize.eraseResult,
                  Serialize.count_value data.size physical]
              · simp only [layout, over, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, countWord_nat data.size physical]
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                simpa only [Ssz.chunksForBytes, Ssz.bytesPerChunk,
                  show (32 : BitVec 64).toNat = 32 from rfl] using
                  packing_capacity_refines (.bytes data) data (bytes_represents data)
                    limit 32 arena (some (Ssz.lengthWord data.size)) (by decide)
          | _ => exact .error wrongType .typeMismatch rfl
      | bitVector length =>
          cases value with
          | bits data =>
              by_cases matched : length.value = data.count.toNat
              · simp only [layout, guarded_true matched, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Packing.unpackBits_size,
                  show (data.count.toNat != length.value) = false from by simp [matched],
                  Bool.false_eq_true, ↓reduceIte, packedBits_eq]
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                simpa only [Ssz.chunksForBits, Ssz.bytesPerChunk,
                  show (256 : BitVec 64).toNat = 256 from rfl] using
                  packing_capacity_refines (.bits data)
                    (PackedBits.canonicalBytes data.bytes data.count.toNat)
                    (bits_represents data) length 256 arena none (by decide)
              · simp only [layout, matched, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Packing.unpackBits_size,
                  show (data.count.toNat != length.value) = true from by simp [Ne.symm matched],
                  ↓reduceIte]
                exact count_error_refines length data.count arena false
          | _ => exact .error wrongType .typeMismatch rfl
      | bitList limit =>
          cases value with
          | bits data =>
              by_cases over : limit.value < data.count.toNat
              · simp only [layout, over, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Packing.unpackBits_size]
                exact count_error_refines limit data.count arena true
              · simp only [layout, over, ↓reduceIte, Desc.erase, Serialize.Desc.erase,
                  Value.erase, Ssz.merkleLayout, Packing.unpackBits_size,
                  packedBits_eq, countWord128_eq_lengthWord]
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                simpa only [Ssz.chunksForBits, Ssz.bytesPerChunk,
                  show (256 : BitVec 64).toNat = 256 from rfl] using
                  packing_capacity_refines (.bits data)
                    (PackedBits.canonicalBytes data.bytes data.count.toNat)
                    (bits_represents data) limit 256 arena
                    (some (Ssz.lengthWord data.count.toNat)) (by decide)
          | _ => exact .error wrongType .typeMismatch rfl
      | progressiveBitList limit =>
          cases value with
          | bits data =>
              simp only [layout, Desc.erase, Serialize.Desc.erase, Value.erase,
                Ssz.merkleLayout, packedBits_eq, Packing.unpackBits_size,
                countWord128_eq_lengthWord]
              exact .ok _ _ (packing_refines (.bits data) _ (bits_represents data)
                none (some (Ssz.lengthWord data.count.toNat)))
          | _ => exact .error wrongType .typeMismatch rfl
  | vector element length =>
      cases value with
      | seq values =>
          have physical : values.length < 2 ^ 64 := valuePhysical.1
          by_cases matched : length.value = values.length
          · simp only [layout, guarded_true matched, Desc.erase, Value.erase,
              Ssz.merkleLayout, Value.eraseList_length,
              show (values.length != length.value) = false from by simp [matched],
              Bool.false_eq_true, ↓reduceIte]
            try dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            exact sequence_refines element values (some length) none arena safe
          · simp only [layout, matched, ↓reduceIte, Desc.erase, Value.erase,
              Ssz.merkleLayout, Value.eraseList_length,
              show (values.length != length.value) = true from by simp [Ne.symm matched],
              ↓reduceIte]
            apply ResultRefines.error
            simp only [eraseResult, Codec.eraseResult, Serialize.eraseResult,
              Serialize.count_value values.length physical]
      | _ => exact .error wrongType .typeMismatch rfl
  | list element limit =>
      cases value with
      | seq values =>
          have physical : values.length < 2 ^ 64 := valuePhysical.1
          by_cases over : limit.value < values.length
          · simp only [layout, over, ↓reduceIte, Desc.erase, Value.erase,
              Ssz.merkleLayout, Value.eraseList_length]
            apply ResultRefines.error
            simp only [eraseResult, Codec.eraseResult, Serialize.eraseResult,
              Serialize.count_value values.length physical]
          · simp only [layout, over, ↓reduceIte, Desc.erase, Value.erase,
              Ssz.merkleLayout, Value.eraseList_length, countWord_nat values.length physical]
            try dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            exact sequence_refines element values (some limit)
              (some (Ssz.lengthWord values.length)) arena safe
      | _ => exact .error wrongType .typeMismatch rfl
  | progressiveList element limit =>
      cases value with
      | seq values =>
          have physical : values.length < 2 ^ 64 := valuePhysical.1
          simpa only [layout, Desc.erase, Value.erase, Ssz.merkleLayout,
            Value.eraseList_length, countWord_nat values.length physical, Option.map] using
            sequence_refines element values none (some (Ssz.lengthWord values.length)) arena safe
      | _ => exact .error wrongType .typeMismatch rfl
  | container fields =>
      cases value with
      | seq values =>
          have physical : fields.length < 2 ^ 64 := descPhysical.1
          by_cases arity : fields.length = values.length
          · simp only [layout, guarded_true arity, Desc.erase, Value.erase,
              Ssz.merkleLayout, Desc.eraseFields_length, Value.eraseList_length,
              show (fields.length != values.length) = false from by simp [arity],
              Bool.false_eq_true, ↓reduceIte]
            dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            apply ResultRefines.ok
            simpa only [Option.map, Serialize.count_value fields.length physical] using
              nesting_refines (.fields fields values) _ (Nested.fields_count fields values arity)
                (Nested.fields_at fields values) (some (Serialize.count fields.length)) none
          · simp only [layout, arity, ↓reduceIte, Desc.erase, Value.erase,
              Ssz.merkleLayout, Desc.eraseFields_length, Value.eraseList_length,
              show (fields.length != values.length) = true from by simp [arity],
              ↓reduceIte]
            exact .error wrongType .typeMismatch rfl
      | _ => exact .error wrongType .typeMismatch rfl
  | progressiveContainer active fields =>
      cases value with
      | seq values =>
          have fieldsPhysical : fields.length < 2 ^ 64 := descPhysical.2.1
          have activePhysical : active.length < 2 ^ 64 := descPhysical.1
          have countPhysical : active.countP id < 2 ^ 64 :=
            Nat.lt_of_le_of_lt (activeCount_le active) activePhysical
          by_cases arity : fields.length = values.length
          · by_cases counted : active.countP id = fields.length
            · obtain ⟨slots, placed⟩ := layoutSlots_success active fields values arity counted
              simp only [layout, guarded_true arity, guarded_true counted, Desc.erase, Value.erase,
                Ssz.merkleLayout, placed, MerkleWords.activeFieldsWord_eq_upstream]
              dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
              exact .ok _ _ (nesting_refines (.progressive active fields values) slots
                (Nested.progressive_count placed) (Nested.progressive_at placed) none
                (some (Ssz.activeFieldsWord active)))
            · have rejected := layoutSlots_count_error active fields values arity counted
              simp only [layout, guarded_true arity, guarded_false counted, Desc.erase, Value.erase,
                Ssz.merkleLayout, rejected]
              dsimp only [Bind.bind, Except.bind]
              apply ResultRefines.error
              simp only [eraseResult, Serialize.count_value _ countPhysical,
                Serialize.count_value _ fieldsPhysical]
          · have rejected := layoutSlots_arity_error active fields values arity
            simp only [layout, arity, ↓reduceIte, Desc.erase, Value.erase,
              Ssz.merkleLayout, rejected]
            dsimp only [Bind.bind, Except.bind]
            exact .error wrongType .typeMismatch rfl
      | _ => exact .error wrongType .typeMismatch rfl
  | compatibleUnion variants =>
      cases value with
      | union selector child =>
          cases selected : lookup variants selector with
          | none =>
              simp only [layout, Desc.erase, Value.erase, Ssz.merkleLayout,
                lookup_refines, selected]
              dsimp only [Bind.bind, Except.bind]
              exact .error (.codec (.unknownSelector selector)) (.unknownSelector selector.value) rfl
          | some chosen =>
              by_cases over : 255 < selector.value
              · simp only [layout, Desc.erase, Value.erase, Ssz.merkleLayout,
                  lookup_refines, selected, Ssz.selectorWord, over, ↓reduceIte]
                dsimp only [Bind.bind, Except.bind]
                apply ResultRefines.error
                rfl
              · simp only [layout, Desc.erase, Value.erase, Ssz.merkleLayout,
                  lookup_refines, selected, Ssz.selectorWord,
                  over, ↓reduceIte, MerkleWords.lengthWord_eq_upstream]
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
                exact .ok _ _ (nesting_refines (.union chosen child) _
                  rfl (Nested.union_at chosen child) (some (.small 1))
                  (some (Ssz.lengthWord selector.value)))
      | _ => exact .error wrongType .typeMismatch rfl

theorem layout_success (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (view : Layout) (success : (layout desc value arena).result = .ok view) :
    ∃ expected, Ssz.merkleLayout desc.erase value.erase = .ok expected ∧
      LayoutRefines view expected := by
  have refined := layout_refines desc value arena safe descPhysical valuePhysical
  unfold Refines at refined
  cases expectedEq : Ssz.merkleLayout desc.erase value.erase with
  | error reason =>
      rw [success, expectedEq] at refined
      cases refined
  | ok expected =>
      refine ⟨expected, rfl, ?_⟩
      rw [success, expectedEq] at refined
      cases refined with
      | ok _ _ related => exact related

end SszNative.HashLayout

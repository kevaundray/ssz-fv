import SszCodecDecodeSequenceCore

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

private theorem sequence_bind_pure {α β : Type} (used : Nat) (value : α)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.ok value)) next = next value used := by
  simp only [bind, unchanged, List.nil_append]

private theorem sequence_bind_error {α β : Type} (used : Nat) (reason : Error)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.error reason)) next = unchanged used (.error reason) := rfl

private theorem sequence_throw {α : Type} (reason : Ssz.Err) :
    (throw reason : Except Ssz.Err α) = .error reason := rfl

attribute [local simp] sequence_bind_pure sequence_bind_error sequence_throw
attribute [local simp] Bind.bind Pure.pure Functor.map Except.pure Except.bind Except.map Except.mapError

private theorem sequence_readOffsets_first (data : Ssz.Bytes) (count : Nat)
    (positive : 0 < count) :
    (Ssz.readOffsets data count)[0]?.getD 0 = Ssz.readUint data 0 4 := by
  cases count with
  | zero => omega
  | succ count => simp [Ssz.readOffsets, Ssz.bytesPerOffset, List.range_succ_eq_map]

private theorem sequence_bounded_continuation {α β : Type} (erase : α → β)
    (limit : Option NatOperand) (count used : Nat) (next : Nat → Outcome α)
    (expected : Except Ssz.Err β) (physical : count < 2 ^ 64)
    (nextRefines : ∀ used, Refines erase (next used) expected) :
    Refines erase (bind (bounded limit (Serialize.count count) used) (fun _ => next))
      (match limit with
       | none => expected
       | some cap => if cap.value < count then .error (.overLimit cap.value count) else expected) := by
  cases limit with
  | none => simpa only [Refines, bounded, Serialize.bounded, Serialize.unchanged,
      Except.mapError, bind] using nextRefines used
  | some cap =>
    by_cases over : cap.value < count
    · left
      simp [bounded, Serialize.bounded, count_value count physical,
        show ¬ count ≤ cap.value by omega, over, bind, Serialize.unchanged,
        Codec.eraseResult, Serialize.eraseResult]
    · simpa only [Refines, bounded, Serialize.bounded, count_value count physical,
        show count ≤ cap.value by omega, ↓reduceIte, Serialize.unchanged,
        Except.mapError, bind, over] using nextRefines used

/-- All fixed and variable vector paths, including zero-width elements and a
zero declared count, preserve the pinned decoder's exact semantic result. -/
theorem vector_refines (element : Desc) (length : NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodeErase (vector element length visit input arena)
      ((Ssz.vectorSlices element.erase length.value input.bytes).bind
        (fun slices => (Ssz.deserializeEach element.erase slices).map Ssz.Value.seq)) := by
  unfold vector
  by_cases oversized : 2 ^ 32 ≤ input.bytes.size
  · simp only [compositeSize, oversized, ↓reduceIte]
    rw [sequence_bind_error]
    left
    simp [oversized, unchanged, Codec.eraseResult,
      count_value input.bytes.size physical, Ssz.vectorSlices, Ssz.bytesPerOffset]
  · simp only [compositeSize, oversized, ↓reduceIte, sequence_bind_pure]
    apply sequence_bind_ok (Option.map NatOperand.value) nodeErase _ _ _ _
      (fixedSize_refines element arena)
    intro measured used correct
    cases measured with
    | some width =>
      simp only [Option.map] at correct
      simp [Ssz.vectorSlices, Ssz.bytesPerOffset, oversized, ← correct]
      apply sequence_bind_ok NatOperand.value nodeErase _ _ _ _
        (sequence_mul_refines width length { arena with used := used })
      intro expected used product
      by_cases scope : expected.value = input.bytes.size
      · have size : input.bytes.size = width.value * length.value := by omega
        simp [exact, scope, size]
        by_cases empty : length.value = 0
        · simp [empty, Refines, unchanged, nodeErase, Node.value,
            Node.values, Codec.Value.eraseList, Codec.eraseResult,
            Ssz.deserializeEach]
        · simp only [empty, ↓reduceIte]
          by_cases countFits : length.value < 2 ^ 64
          · rw [narrow_fits length scratch used countFits]
            rw [sequence_bind_pure]
            by_cases widthFits : width.value < 2 ^ 64
            · rw [narrow_fits width scratch used widthFits]
              rw [sequence_bind_pure]
              exact decodeFixed_refines element visit length.value width.value input
                { arena with used := used } physical visitRefines
            · right
              simp only [narrow, widthFits, ↓reduceIte]
              rw [sequence_bind_error]
              rfl
          · right
            simp only [narrow, countFits, ↓reduceIte]
            rw [sequence_bind_error]
            rfl
      · have mismatch : input.bytes.size ≠ width.value * length.value := by omega
        simp only [exact, scope, ↓reduceIte, sequence_bind_error]
        left
        simp [unchanged, mismatch, Codec.eraseResult,
          Serialize.eraseResult, count_value input.bytes.size physical, product]
    | none =>
      simp only [Option.map] at correct
      simp [Ssz.vectorSlices, Ssz.bytesPerOffset, oversized, ← correct]
      apply sequence_bind_ok NatOperand.value nodeErase _ _ _ _
        (sequence_mul_refines length (.small 4) { arena with used := used })
      intro leading used product
      have four : (NatOperand.small 4).value = 4 := rfl
      rw [four] at product
      by_cases tooSmall : input.bytes.size < leading.value
      · have short : input.bytes.size < length.value * 4 := by omega
        simp only [tooSmall, ↓reduceIte]
        left
        simp [short, product, unchanged, Codec.eraseResult,
          count_value input.bytes.size physical]
      · have table : length.value * 4 ≤ input.bytes.size := by omega
        simp only [tooSmall, ↓reduceIte, show ¬ input.bytes.size < length.value * 4 by omega]
        by_cases empty : length.value = 0
        · simp [empty, Refines, unchanged, nodeErase, Node.value,
            Node.values, Codec.Value.eraseList, Codec.eraseResult,
            Ssz.deserializeEach]
        · have positive : 0 < length.value := by omega
          have countFits : length.value < 2 ^ 64 := by omega
          simp [empty]
          rw [narrow_fits length scratch used countFits, sequence_bind_pure]
          rw [sequence_readOffsets_first input.bytes length.value positive]
          have firstFits : Ssz.readUint input.bytes 0 4 < 2 ^ 64 := by
            have bound := WordDecode.readUint_lt input.bytes 0 4
            omega
          by_cases first : leading.value = Ssz.readUint input.bytes 0 4
          · have equal : Ssz.readUint input.bytes 0 4 = length.value * 4 := by omega
            simp only [first, ↓reduceIte]
            have decoded := decodeOffsets_refines element visit length.value input
              { arena with used := used } physical visitRefines
            cases spans : Ssz.offsetSpans (Ssz.readOffsets input.bytes length.value) input.bytes.size <;>
              simpa [equal, spans] using decoded
          · have unequal : Ssz.readUint input.bytes 0 4 ≠ length.value * 4 := by omega
            simp only [first, ↓reduceIte]
            left
            simp [unequal, unchanged, Codec.eraseResult, product,
              count_value (Ssz.readUint input.bytes 0 4) firstFits]

/-- Empty input wins before measuring an element or examining a bound. Nonempty
fixed-width lists cannot reach the representation-failure narrowing branch. -/
theorem list_refines (element : Desc) (limit : Option NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodeErase (list element limit visit input arena)
      ((Ssz.listSlices element.erase (limit.map NatOperand.value) input.bytes).bind
        (fun slices => (Ssz.deserializeEach element.erase slices).map Ssz.Value.seq)) := by
  unfold list
  by_cases oversized : 2 ^ 32 ≤ input.bytes.size
  · simp only [compositeSize, oversized, ↓reduceIte]
    rw [sequence_bind_error]
    left
    simp [oversized, unchanged, Codec.eraseResult,
      count_value input.bytes.size physical, Ssz.listSlices, Ssz.bytesPerOffset]
  · simp only [compositeSize, oversized, ↓reduceIte, sequence_bind_pure]
    by_cases empty : input.bytes.size = 0
    · simp [empty, Refines, unchanged, nodeErase, Node.value,
        Node.values, Codec.Value.eraseList, Codec.eraseResult, Ssz.listSlices,
        Ssz.bytesPerOffset, Ssz.deserializeEach]
    · simp only [empty, ↓reduceIte]
      apply sequence_bind_ok (Option.map NatOperand.value) nodeErase _ _ _ _
        (fixedSize_refines element arena)
      intro measured used correct
      cases measured with
      | some width =>
        simp only [Option.map] at correct
        simp [Ssz.listSlices, Ssz.bytesPerOffset, oversized, empty, ← correct]
        by_cases zero : width.value = 0
        · left
          simp [zero, unchanged, Codec.eraseResult]
        · simp only [zero, ↓reduceIte]
          by_cases tooWide : input.bytes.size < width.value
          · have remainder : input.bytes.size % width.value ≠ 0 := by
              rw [Nat.mod_eq_of_lt tooWide]
              exact empty
            left
            simp [tooWide, remainder, unchanged, Codec.eraseResult,
              count_value input.bytes.size physical]
          · have fits : width.value < 2 ^ 64 := by omega
            simp only [tooWide, ↓reduceIte]
            rw [narrow_fits width representation used fits]
            rw [sequence_bind_pure]
            by_cases divided : input.bytes.size % width.value = 0
            · simp [divided]
              have countFits : input.bytes.size / width.value < 2 ^ 64 :=
                Nat.lt_of_le_of_lt (Nat.div_le_self _ _) physical
              have rest := sequence_bounded_continuation nodeErase limit
                (input.bytes.size / width.value) used
                (fun used => decodeFixed visit (input.bytes.size / width.value) width.value
                  input { arena with used := used })
                ((Ssz.deserializeEach element.erase ((List.range (input.bytes.size / width.value)).map
                  (fun index => input.bytes.extract (index * width.value)
                    ((index + 1) * width.value)))).map Ssz.Value.seq)
                countFits
                (fun used => decodeFixed_refines element visit _ _ input
                  { arena with used := used } physical visitRefines)
              cases limit with
              | none => simpa using rest
              | some cap =>
                by_cases over : cap.value < input.bytes.size / width.value <;>
                  simpa [over] using rest
            · left
              simp [divided, unchanged, Codec.eraseResult,
                count_value input.bytes.size physical, count_value width.value fits]
      | none =>
        simp only [Option.map] at correct
        simp [Ssz.listSlices, Ssz.bytesPerOffset, oversized, empty, ← correct]
        by_cases tooSmall : input.bytes.size < 4
        · left
          simp [tooSmall, unchanged, Codec.eraseResult, count_value input.bytes.size physical]
          rfl
        · simp [tooSmall]
          by_cases below : Ssz.readUint input.bytes 0 4 < 4
          · left
            simp [below, unchanged, Codec.eraseResult]
          · simp [below]
            by_cases aligned : Ssz.readUint input.bytes 0 4 % 4 = 0
            · simp [aligned]
              by_cases past : input.bytes.size < Ssz.readUint input.bytes 0 4
              · left
                simp [past, unchanged, Codec.eraseResult]
              · simp [past]
                have countFits : Ssz.readUint input.bytes 0 4 / 4 < 2 ^ 64 := by
                  have bound := Nat.div_le_self (Ssz.readUint input.bytes 0 4) 4
                  omega
                have rest := sequence_bounded_continuation nodeErase limit
                  (Ssz.readUint input.bytes 0 4 / 4) used
                  (fun used => decodeOffsets visit (Ssz.readUint input.bytes 0 4 / 4)
                    input { arena with used := used })
                  ((Ssz.offsetSpans (Ssz.readOffsets input.bytes
                    (Ssz.readUint input.bytes 0 4 / 4)) input.bytes.size).bind
                    (fun spans => (Ssz.deserializeEach element.erase
                      (((Ssz.readOffsets input.bytes (Ssz.readUint input.bytes 0 4 / 4)).zip spans).map
                        (fun pair => input.bytes.extract pair.1 (pair.1 + pair.2)))).map Ssz.Value.seq))
                  countFits
                  (fun used => decodeOffsets_refines element visit _ input
                    { arena with used := used } physical visitRefines)
                cases limit with
                | none =>
                  cases spans : Ssz.offsetSpans (Ssz.readOffsets input.bytes
                      (Ssz.readUint input.bytes 0 4 / 4)) input.bytes.size <;>
                    simpa [spans] using rest
                | some cap =>
                  by_cases over : cap.value < Ssz.readUint input.bytes 0 4 / 4 <;>
                    cases spans : Ssz.offsetSpans (Ssz.readOffsets input.bytes
                      (Ssz.readUint input.bytes 0 4 / 4)) input.bytes.size <;>
                    simpa [over, spans] using rest
            · left
              simp [aligned, unchanged, Codec.eraseResult]

end SszNative.CodecDecode

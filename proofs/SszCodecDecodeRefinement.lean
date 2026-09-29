import SszCodecDecodePrimitiveProofs
import SszCodecDecodeSequenceRefinement
import SszCodecDecodeStructRefinement
import SszCodecDecodeUnion

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc)

private theorem decode_bind_pure_map {α β : Type} (result : Except Ssz.Err α) (f : α → β) :
    result.bind (fun value => pure (f value)) = result.map f := by
  cases result <;> rfl

/-- One complete constructor layer. The hypothesis is induction on strict raw
schema children, not an assumed successful future execution. -/
theorem decodeStep_refines (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (visit : Visit desc.children) (physical : input.bytes.size < 2 ^ 64)
    (visits : ∀ child member input arena, input.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit child member input arena) (Ssz.deserialize child.erase input.bytes)) :
    Refines nodeErase (decodeStep desc input arena visit) (Ssz.deserialize desc.erase input.bytes) := by
  cases desc with
  | primitive shape => exact primitive_refines shape input arena physical
  | vector element length =>
    simpa only [decodeStep, Desc.erase, Ssz.deserialize, Bind.bind, decode_bind_pure_map] using
      vector_refines element length (visit element (by simp [Desc.children])) input arena physical
        (visits element (by simp [Desc.children]))
  | list element limit =>
    simpa only [decodeStep, Desc.erase, Ssz.deserialize, Option.map_some,
      Bind.bind, decode_bind_pure_map] using
      list_refines element (some limit) (visit element (by simp [Desc.children])) input arena physical
        (visits element (by simp [Desc.children]))
  | progressiveList element limit =>
    simpa only [decodeStep, Desc.erase, Ssz.deserialize, Bind.bind, decode_bind_pure_map] using
      list_refines element limit (visit element (by simp [Desc.children])) input arena physical
        (visits element (by simp [Desc.children]))
  | container fields =>
    simpa only [decodeStep, Desc.erase, Ssz.deserialize, Desc.eraseFields_eq_map,
      List.map_map, Function.comp_def, Bind.bind, decode_bind_pure_map] using
      structureValue_refines (fields.map Prod.snd) visit input arena physical visits
  | progressiveContainer active fields =>
    simpa only [decodeStep, Desc.erase, Ssz.deserialize, Desc.eraseFields_eq_map,
      List.map_map, Function.comp_def, Bind.bind, decode_bind_pure_map] using
      structureValue_refines (fields.map Prod.snd) visit input arena physical visits
  | compatibleUnion variants =>
    by_cases empty : input.bytes.size = 0
    · left
      simp only [decodeStep, empty, ↓reduceIte, unchanged, Except.map, Codec.eraseResult,
        Desc.erase, Ssz.deserialize]
      rfl
    · have nonempty : ¬ input.bytes.size < 1 := by omega
      have byteBound : input.bytes[0]!.toNat < 2 ^ 64 := by
        have small : input.bytes[0]!.toNat < 256 := input.bytes[0]!.toBitVec.isLt
        omega
      have selectorValue := count_value input.bytes[0]!.toNat byteBound
      simp only [Serialize.count] at selectorValue
      have result := unionOption_refines variants visit
        (.small (BitVec.ofNat 64 input.bytes[0]!.toNat))
        (input.slice 1 input.bytes.size) arena (slice_physical input 1 input.bytes.size physical) visits
      refine Eq.mpr ?_ result
      simp only [decodeStep, empty, ↓reduceIte, Desc.erase, Ssz.deserialize,
        nonempty, Input.slice, selectorValue] <;> rfl

/-- Full pinned-deserializer refinement for every finite raw native descriptor.
Only the physical input byte count is bounded. Logical widths, lengths, limits,
selectors and descriptor depth have no cap; invalid schemas are not excluded. -/
theorem decode_refines (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    Refines nodeErase (decode desc input arena) (Ssz.deserialize desc.erase input.bytes) := by
  induction desc using Desc.inductionOnChildren generalizing input arena with
  | step desc ih =>
    rw [decode]
    apply decodeStep_refines desc input arena _ physical
    intro child member childInput childArena childPhysical
    exact ih child member childInput childArena childPhysical

theorem run_refines (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : bytes.size < 2 ^ 64) :
    (run desc bytes arena).erase = .ok (Ssz.deserialize desc.erase bytes) ∨
      (run desc bytes arena).result = .error scratch :=
  decode_refines desc ⟨0, bytes⟩ arena physical

/-- The private representational guards cannot hide a semantic disagreement. -/
theorem decode_no_badRepresentation (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    (decode desc input arena).result ≠ .error representation := by
  intro failed
  rcases decode_refines desc input arena physical with correct | exhausted
  · simp only [failed, Except.map, representation, Codec.eraseResult,
      Serialize.eraseResult] at correct
    cases correct
  · rw [failed] at exhausted
    cases exhausted

theorem run_no_badRepresentation (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : bytes.size < 2 ^ 64) :
    (run desc bytes arena).result ≠ .error representation :=
  decode_no_badRepresentation desc ⟨0, bytes⟩ arena physical

/-- A successful native storage witness materializes exactly the pinned value. -/
theorem decode_success (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) (node : Node)
    (success : (decode desc input arena).result = .ok node) :
    Ssz.deserialize desc.erase input.bytes = .ok (nodeErase node) := by
  rcases decode_refines desc input arena physical with correct | exhausted
  · simpa only [success, Except.map, Codec.eraseResult, Except.ok.injEq] using correct.symm
  · rw [success] at exhausted
    cases exhausted

/-- Every exposed semantic rejection agrees as well; refinement is not merely
conditional correctness for successful decodes. -/
theorem decode_rejection (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) (reason : Codec.Error) (semantic : Ssz.Err)
    (failed : (decode desc input arena).result = .error reason)
    (erased : Codec.eraseResult (Except.error reason : Except Codec.Error Ssz.Value) =
      .ok (.error semantic)) :
    Ssz.deserialize desc.erase input.bytes = .error semantic := by
  rcases decode_refines desc input arena physical with correct | exhausted
  · simp only [failed, Except.map, erased, Except.ok.injEq] at correct
    exact correct.symm
  · have same : reason = scratch := by simpa only [failed, Except.error.injEq] using exhausted
    subst reason
    simp only [scratch, Codec.eraseResult, Serialize.eraseResult] at erased
    cases erased

end SszNative.CodecDecode

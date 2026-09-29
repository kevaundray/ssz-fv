import SszCodecDecodeRefinementCore

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc)

/-- Boxing can fail only at its real reservation; no child effect is undone. -/
theorem box_refines (selector : NatOperand) (child : Node) (arena : Delimited.ArenaState) :
    Refines nodeErase
      (bind (reserve valueLayout 1 arena) fun allocation used =>
        bind (writeValue allocation 0 child used) fun _ used =>
          unchanged used (.ok (.union selector allocation child)))
      (.ok (.union selector.value (nodeErase child))) := by
  cases allocated : TypedArena.reserve valueLayout arena.base arena.capacity arena.used 1 with
  | none =>
    right
    simp only [reserve, allocated, bind]
  | some allocation =>
    left
    simp only [reserve, allocated, bind, writeValue, unchanged, Except.map,
      Codec.eraseResult, nodeErase, Node.value, Codec.Value.erase]

/-- The first numerically matching variant wins, including duplicate declarations
and noncanonical selector representations. -/
theorem unionOption_refines (variants : List (NatOperand × Desc))
    (visit : Visit (variants.map Prod.snd)) (selector : NatOperand)
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (visits : ∀ child member input arena, input.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit child member input arena) (Ssz.deserialize child.erase input.bytes)) :
    Refines nodeErase (unionOption variants visit selector input arena)
      (Ssz.deserializeOption (variants.map (fun variant => variant.1.value))
        (Desc.eraseVariants variants) selector.value input.bytes) := by
  induction variants generalizing arena with
  | nil =>
    left
    simp only [unionOption, unchanged, List.map_nil, Desc.eraseVariants,
      Ssz.deserializeOption, Except.map, Codec.eraseResult]
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    by_cases selected : chosen.value = selector.value
    · simp only [unionOption, selected, ↓reduceIte, List.map_cons, Desc.eraseVariants,
        Ssz.deserializeOption, beq_iff_eq]
      apply refines_bind nodeErase nodeErase _ _ (Ssz.deserialize desc.erase input.bytes)
        (fun value => .ok (.union selector.value value))
      · exact visits desc (by simp) input arena physical
      · intro child used
        exact box_refines selector child { arena with used := used }
    · simp only [unionOption, selected, ↓reduceIte, List.map_cons, Desc.eraseVariants,
        Ssz.deserializeOption, beq_iff_eq]
      apply ih
      intro child member childInput childArena childPhysical
      exact visits child (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ member)
        childInput childArena childPhysical

/-- Array extraction never creates a physically larger byte slice. This is not
used to justify native accesses; window bounds are proved separately. -/
theorem slice_physical (input : Input) (start ending : Nat)
    (physical : input.bytes.size < 2 ^ 64) :
    (input.slice start ending).bytes.size < 2 ^ 64 := by
  simp only [Input.slice, Array.size_extract]
  omega

/-- Borrowed offsets accumulate relative to the original source, not to scratch. -/
theorem slice_offset (input : Input) (start ending : Nat) :
    (input.slice start ending).offset = input.offset + start := rfl

theorem nested_slice_offset (input : Input) (start ending innerStart innerEnd : Nat) :
    ((input.slice start ending).slice innerStart innerEnd).offset =
      input.offset + start + innerStart := rfl

end SszNative.CodecDecode

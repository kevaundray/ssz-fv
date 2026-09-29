import SszCodecDecodeResourcesWrites
import SszCodecDecodeBorrowed
import SszCodecDecodePrimitiveStorage
import SszCodecDecodeStructSlots

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Value)

theorem nodeValues_length (nodes : List Node) : (Node.values nodes).length = nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp only [Node.values, List.length_cons, ih]

private theorem physical_slice (input : Input) (start ending : Nat)
    (physical : input.bytes.size < 2 ^ 64) : (input.slice start ending).bytes.size < 2 ^ 64 := by
  simp only [Input.slice, Array.size_extract]
  omega

private theorem emptySequence_physical : (Node.seq none []).value.Physical := by
  exact ⟨by decide, True.intro⟩

theorem decodeWindows_physical (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit input arena))
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun nodes => Value.listPhysical (Node.values nodes) ∧ nodes.length = windows.length)
      (decodeWindows visit windows input allocation index arena) := by
  induction windows generalizing index arena with
  | nil => exact returns_unchanged _ _ _ ⟨True.intro, rfl⟩
  | cons window rest ih =>
    rw [decodeWindows]
    apply returns_bind (fun node => node.value.Physical)
    · exact visits _ _ (physical_slice input _ _ physical)
    · intro child used childPhysical
      apply returns_bind_next
      intro checked used
      apply returns_bind (fun nodes => Value.listPhysical (Node.values nodes) ∧ nodes.length = rest.length)
      · exact ih (index + 1) { arena with used := used }
      · intro nodes used tailPhysical
        exact returns_unchanged _ _ _
          ⟨⟨childPhysical, tailPhysical.1⟩, by simp only [List.length_cons, tailPhysical.2]⟩

theorem valueReserve_returns_count (count : Nat) (arena : Delimited.ArenaState) :
    Returns (fun _ => count < 2 ^ 64) (reserve valueLayout count arena) := by
  intro allocation success
  cases reserved : TypedArena.reserve valueLayout arena.base arena.capacity arena.used count with
  | none =>
    simp only [reserve, reserved] at success
    cases success
  | some allocated =>
    exact valueReserve_count_lt count arena allocated reserved

theorem decodeArray_physical (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit input arena))
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (decodeArray visit windows input arena) := by
  unfold decodeArray
  apply returns_bind (fun _ => windows.length < 2 ^ 64)
  · exact valueReserve_returns_count _ _
  · intro allocation used countBound
    apply returns_bind (fun nodes => Value.listPhysical (Node.values nodes) ∧ nodes.length = windows.length)
    · exact decodeWindows_physical visit visits windows input allocation 0
        { arena with used := used } physical
    · intro nodes used nodesPhysical
      apply returns_unchanged
      exact ⟨by rw [nodeValues_length, nodesPhysical.2]; exact countBound, nodesPhysical.1⟩

theorem decodeOffsets_physical (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit input arena))
    (count : Nat) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (decodeOffsets visit count input arena) := by
  unfold decodeOffsets
  apply returns_bind_next
  intro checked used
  exact decodeArray_physical visit visits _ input { arena with used := used } physical

theorem vector_physical (element : Desc) (length : NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit input arena))
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (vector element length visit input arena) := by
  unfold vector
  apply returns_bind_next
  intro checked used
  apply returns_bind_next
  intro width used
  cases width with
  | some width =>
    apply returns_bind_next
    intro expected used
    apply returns_bind_next
    intro checked used
    split
    · exact returns_unchanged _ _ _ emptySequence_physical
    · apply returns_bind_next
      intro count used
      apply returns_bind_next
      intro width used
      rw [decodeFixed_eq_decodeArray]
      exact decodeArray_physical visit visits _ input { arena with used := used } physical
  | none =>
    apply returns_bind_next
    intro leading used
    split
    · exact returns_error _ _ _
    · split
      · exact returns_unchanged _ _ _ emptySequence_physical
      · apply returns_bind_next
        intro count used
        dsimp only
        split
        · exact returns_error _ _ _
        · exact decodeOffsets_physical visit visits count input { arena with used := used } physical

theorem list_physical (element : Desc) (limit : Option NatOperand)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit input arena))
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (list element limit visit input arena) := by
  unfold list
  apply returns_bind_next
  intro checked used
  split
  · exact returns_unchanged _ _ _ emptySequence_physical
  · apply returns_bind_next
    intro width used
    cases width with
    | some width =>
      dsimp only
      split
      · exact returns_error _ _ _
      · split
        · exact returns_error _ _ _
        · apply returns_bind_next
          intro width used
          split
          · exact returns_error _ _ _
          · apply returns_bind_next
            intro checked used
            rw [decodeFixed_eq_decodeArray]
            exact decodeArray_physical visit visits _ input { arena with used := used } physical
    | none =>
      dsimp only
      split
      · exact returns_error _ _ _
      · split
        · exact returns_error _ _ _
        · split
          · exact returns_error _ _ _
          · split
            · exact returns_error _ _ _
            · apply returns_bind_next
              intro checked used
              exact decodeOffsets_physical visit visits _ input { arena with used := used } physical

theorem decodeEntries_physical {children : List Desc} (entries : List (Entry children))
    (visit : Visit children)
    (visits : ∀ child member input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit child member input arena))
    (input : Input) (allocation : Arena.Reservation) (index : Nat)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun nodes => Value.listPhysical (Node.values nodes) ∧ nodes.length = entries.length)
      (decodeEntries entries visit input allocation index arena) := by
  induction entries generalizing index arena with
  | nil => exact returns_unchanged _ _ _ ⟨True.intro, rfl⟩
  | cons entry rest ih =>
    rw [decodeEntries]
    apply returns_bind (fun node => node.value.Physical)
    · exact visits _ _ _ _ (physical_slice input _ _ physical)
    · intro child used childPhysical
      apply returns_bind_next
      intro checked used
      apply returns_bind (fun nodes => Value.listPhysical (Node.values nodes) ∧ nodes.length = rest.length)
      · exact ih (index + 1) { arena with used := used }
      · intro nodes used tailPhysical
        exact returns_unchanged _ _ _
          ⟨⟨childPhysical, tailPhysical.1⟩, by simp only [List.length_cons, tailPhysical.2]⟩

theorem structureValue_physical (children : List Desc) (visit : Visit children)
    (visits : ∀ child member input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit child member input arena))
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (structureValue children visit input arena) := by
  unfold structureValue
  apply returns_bind_next
  intro checked used
  apply returns_bind_next
  intro slots used
  apply returns_bind_next
  intro checked used
  apply returns_bind (fun measured => measured.entries.length = children.length)
  · intro measured success
    simpa only [initialEntries, List.length_map, List.length_attach] using
      measureSlots_length_success _ _ _ _ _ _ measured success
  · intro measured used measuredLength
    apply returns_bind_next
    intro checked used
    apply returns_bind (fun positioned => positioned.1.length = children.length)
    · intro positioned success
      exact (positionSlots_length_success _ _ _ _ _ _ positioned success).trans measuredLength
    · intro positioned used positionedLength
      apply returns_bind_next
      intro checked used
      apply returns_bind (fun _ => children.length < 2 ^ 64)
      · exact valueReserve_returns_count _ _
      · intro allocation used countBound
        apply returns_bind (fun nodes => Value.listPhysical (Node.values nodes) ∧
          nodes.length = (closeSlots positioned.1 input.bytes.size).length)
        · exact decodeEntries_physical _ visit visits input allocation 0
            { arena with used := used } physical
        · intro nodes used nodesPhysical
          apply returns_unchanged
          refine ⟨?_, nodesPhysical.1⟩
          rw [nodeValues_length, nodesPhysical.2, closeSlots_length, positionedLength]
          exact countBound

theorem unionOption_physical (variants : List (NatOperand × Desc))
    (visit : Visit (variants.map Prod.snd))
    (visits : ∀ child member input arena, input.bytes.size < 2 ^ 64 →
      Returns (fun node => node.value.Physical) (visit child member input arena))
    (selector : NatOperand) (selectorPhysical : Codec.operandSliceSized selector)
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (unionOption variants visit selector input arena) := by
  induction variants generalizing arena with
  | nil => exact returns_error _ _ _
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    rw [unionOption]
    split
    · apply returns_bind (fun node => node.value.Physical)
      · exact visits _ _ _ _ physical
      · intro child used childPhysical
        apply returns_bind_next
        intro allocation used
        apply returns_bind_next
        intro checked used
        exact returns_unchanged _ _ _ ⟨selectorPhysical, childPhysical⟩
    · apply ih
      intro child member input arena physical
      exact visits child (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ member)
        input arena physical

/-- Successful decoding materializes physically bounded native slice counts,
without imposing any bound or canonicality condition on the raw descriptor. -/
theorem decode_physical (desc : Desc) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (decode desc input arena) := by
  induction desc using Desc.inductionOnChildren generalizing input arena with
  | step desc ih =>
    rw [decode]
    cases desc with
    | primitive shape => exact primitive_physical shape input arena physical
    | vector element length =>
      exact vector_physical element length _ (ih element (by simp [Desc.children]))
        input arena physical
    | list element limit =>
      exact list_physical element (some limit) _ (ih element (by simp [Desc.children]))
        input arena physical
    | progressiveList element limit =>
      exact list_physical element limit _ (ih element (by simp [Desc.children]))
        input arena physical
    | container fields => exact structureValue_physical _ _ ih input arena physical
    | progressiveContainer active fields =>
      exact structureValue_physical _ _ ih input arena physical
    | compatibleUnion variants =>
      unfold decodeStep
      dsimp only
      split
      · exact returns_error _ _ _
      · exact unionOption_physical variants _ ih
          (.small (BitVec.ofNat 64 input.bytes[0]!.toNat)) True.intro
          (input.slice 1 input.bytes.size) arena
          (physical_slice input 1 input.bytes.size physical)

theorem run_physical (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : bytes.size < 2 ^ 64) :
    Returns (fun node => node.value.Physical) (run desc bytes arena) :=
  decode_physical desc ⟨0, bytes⟩ arena physical

end SszNative.CodecDecode

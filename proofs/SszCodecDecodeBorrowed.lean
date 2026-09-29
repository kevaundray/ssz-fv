import SszCodecDecode

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc)

/- Only the borrowed payloads are observed here. Integer limbs, array stores,
boxed values and allocator frames belong to the separate resource relation.
Read-only aliases are allowed; no ownership copies or disjointness are asserted. -/
mutual
  def Node.BorrowedAt (observe : Nat → Nat → Option Nat) (source : Nat) : Node → Prop
    | .bool _ | .uint _ => True
    | .bytes offset data => ByteView.BytesAt observe (source + offset) data
    | .bits offset data => ByteView.BytesAt observe (source + offset) data.bytes
    | .seq _ children => nodesBorrowedAt observe source children
    | .union _ _ child => child.BorrowedAt observe source

  def nodesBorrowedAt (observe : Nat → Nat → Option Nat) (source : Nat) : List Node → Prop
    | [] => True
    | child :: rest => child.BorrowedAt observe source ∧ nodesBorrowedAt observe source rest
end

def Input.At (input : Input) (observe : Nat → Nat → Option Nat) (source : Nat) : Prop :=
  ByteView.BytesAt observe (source + input.offset) input.bytes

theorem Input.slice_at (input : Input) (observe : Nat → Nat → Option Nat) (source start ending : Nat)
    (memory : input.At observe source) : (input.slice start ending).At observe source := by
  intro index inside
  change index < (input.bytes.extract start ending).size at inside
  have originalInside : start + index < input.bytes.size := by
    simp only [Array.size_extract] at inside
    omega
  have original := memory (start + index) originalInside
  change observe (source + (input.offset + start) + index) 1 =
    some ((input.bytes.extract start ending)[index]?.getD 0).toNat
  simpa only [Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem originalInside,
    Option.getD_some, Array.getElem_extract, Nat.add_assoc] using original

def Returns {α : Type} (property : α → Prop) (outcome : Outcome α) : Prop :=
  ∀ value, outcome.result = .ok value → property value

theorem returns_unchanged {α : Type} (property : α → Prop) (used : Nat) (value : α)
    (holds : property value) : Returns property (unchanged used (.ok value)) := by
  intro result success
  cases success
  exact holds

theorem returns_error {α : Type} (property : α → Prop) (used : Nat) (reason : Codec.Error) :
    Returns property (unchanged used (.error reason)) := by
  intro result success
  cases success

theorem returns_bind {α β : Type} (property : α → Prop) (post : β → Prop)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (before : Returns property first)
    (after : ∀ value used, property value → Returns post (next value used)) :
    Returns post (bind first next) := by
  intro result success
  cases firstResult : first.result with
  | error reason => simp only [bind, firstResult] at success; cases success
  | ok value =>
    exact after value first.used (before value firstResult) result
      (by simpa only [bind, firstResult] using success)

theorem returns_bind_next {α β : Type} (post : β → Prop)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (after : ∀ value used, Returns post (next value used)) : Returns post (bind first next) :=
  returns_bind (fun _ => True) post first next (fun _ _ => True.intro)
    (fun value used _ => after value used)

theorem packed_borrowed (observe : Nat → Nat → Option Nat) (source offset : Nat)
    (bytes : Ssz.Bytes) (count : BitVec 128) (used : Nat)
    (memory : ByteView.BytesAt observe (source + offset) bytes) :
    Returns (Node.BorrowedAt observe source) (packed offset bytes count used) := by
  unfold packed
  split
  · exact returns_unchanged _ _ _ memory
  · exact returns_error _ _ _

theorem unsigned_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (input : Input) (arena : Delimited.ArenaState) :
    Returns (Node.BorrowedAt observe source) (unsigned input arena) := by
  intro node success
  unfold unsigned at success
  dsimp only at success
  split at success
  · cases success; trivial
  · split at success
    · cases success
    · cases success; trivial

theorem primitive_borrowedAt (observe : Nat → Nat → Option Nat) (source : Nat)
    (shape : Serialize.Desc) (input : Input) (arena : Delimited.ArenaState)
    (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (primitive shape input arena) := by
  have delimit (limit : Option NatOperand) :
      Returns (Node.BorrowedAt observe source) (delimited limit input arena) := by
    unfold delimited
    change Returns (Node.BorrowedAt observe source) _
    intro node success
    dsimp only at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · rename_i ready prepared
          exact (returns_bind_next _ _ _ (fun _ used =>
            packed_borrowed observe source input.offset _ _ used
              (by simpa only [Input.slice, Input.At, Nat.add_zero] using
                Input.slice_at input observe source 0 _ memory))) node success
  cases shape with
  | bool =>
    unfold primitive
    apply returns_bind_next
    intro _ used
    dsimp only
    split
    · exact returns_unchanged _ _ _ True.intro
    · split
      · exact returns_unchanged _ _ _ True.intro
      · exact returns_error _ _ _
  | uint width =>
    unfold primitive
    apply returns_bind_next
    intro _ used
    exact unsigned_borrowed observe source input { arena with used := used }
  | byteVector length | byteList length =>
    unfold primitive
    apply returns_bind_next
    intro _ used
    exact returns_unchanged _ _ _ memory
  | bitVector length =>
    unfold primitive bitVector
    apply returns_bind_next
    intro count used
    exact packed_borrowed observe source input.offset input.bytes count used memory
  | bitList limit => exact delimit (some limit)
  | progressiveBitList limit => exact delimit limit

theorem decodeWindows_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit input arena))
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (nodesBorrowedAt observe source) (decodeWindows visit windows input allocation index arena) := by
  induction windows generalizing index arena with
  | nil => exact returns_unchanged _ _ _ True.intro
  | cons window rest ih =>
    unfold decodeWindows
    apply returns_bind (Node.BorrowedAt observe source)
    · exact visits _ arena (Input.slice_at input observe source _ _ memory)
    · intro child used borrowed
      apply returns_bind_next
      intro _ used
      apply returns_bind (nodesBorrowedAt observe source)
      · exact ih (index + 1) { arena with used := used }
      · intro nodes used tailBorrowed
        exact returns_unchanged _ _ _ ⟨borrowed, tailBorrowed⟩

theorem decodeArray_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit input arena))
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (decodeArray visit windows input arena) := by
  unfold decodeArray
  apply returns_bind_next
  intro allocation used
  apply returns_bind (nodesBorrowedAt observe source)
  · exact decodeWindows_borrowed observe source visit visits windows input allocation 0
      { arena with used := used } memory
  · intro children used borrowed
    exact returns_unchanged _ _ _ borrowed

theorem decodeOffsets_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit input arena))
    (count : Nat) (input : Input) (arena : Delimited.ArenaState)
    (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (decodeOffsets visit count input arena) := by
  unfold decodeOffsets
  apply returns_bind_next
  intro _ used
  exact decodeArray_borrowed observe source visit visits _ input { arena with used := used } memory

theorem vector_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (element : Desc) (length : NatOperand) (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit input arena))
    (input : Input) (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (vector element length visit input arena) := by
  unfold vector
  apply returns_bind_next
  intro _ used
  apply returns_bind_next
  intro width used
  cases width with
  | some width =>
    apply returns_bind_next
    intro expected used
    apply returns_bind_next
    intro _ used
    split
    · exact returns_unchanged _ _ _ True.intro
    · apply returns_bind_next
      intro count used
      apply returns_bind_next
      intro width used
      rw [decodeFixed_eq_decodeArray]
      exact decodeArray_borrowed observe source visit visits _ input { arena with used := used } memory
  | none =>
    apply returns_bind_next
    intro leading used
    split
    · exact returns_error _ _ _
    · split
      · exact returns_unchanged _ _ _ True.intro
      · apply returns_bind_next
        intro count used
        dsimp only
        split
        · exact returns_error _ _ _
        · exact decodeOffsets_borrowed observe source visit visits count input
            { arena with used := used } memory

theorem list_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (element : Desc) (limit : Option NatOperand) (visit : Input → Delimited.ArenaState → Outcome Node)
    (visits : ∀ input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit input arena))
    (input : Input) (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (list element limit visit input arena) := by
  unfold list
  apply returns_bind_next
  intro _ used
  split
  · exact returns_unchanged _ _ _ True.intro
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
            intro _ used
            rw [decodeFixed_eq_decodeArray]
            exact decodeArray_borrowed observe source visit visits _ input { arena with used := used } memory
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
              intro _ used
              exact decodeOffsets_borrowed observe source visit visits _ input { arena with used := used } memory

theorem decodeEntries_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    {children : List Desc} (entries : List (Entry children)) (visit : Visit children)
    (visits : ∀ child member input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit child member input arena))
    (input : Input) (allocation : Arena.Reservation) (index : Nat)
    (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (nodesBorrowedAt observe source) (decodeEntries entries visit input allocation index arena) := by
  induction entries generalizing index arena with
  | nil => exact returns_unchanged _ _ _ True.intro
  | cons entry rest ih =>
    unfold decodeEntries
    apply returns_bind (Node.BorrowedAt observe source)
    · exact visits _ _ _ arena (Input.slice_at input observe source _ _ memory)
    · intro child used borrowed
      apply returns_bind_next
      intro _ used
      apply returns_bind (nodesBorrowedAt observe source)
      · exact ih (index + 1) { arena with used := used }
      · intro nodes used tailBorrowed
        exact returns_unchanged _ _ _ ⟨borrowed, tailBorrowed⟩

theorem structureValue_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (children : List Desc) (visit : Visit children)
    (visits : ∀ child member input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit child member input arena))
    (input : Input) (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (structureValue children visit input arena) := by
  unfold structureValue
  apply returns_bind_next
  intro _ used
  apply returns_bind_next
  intro slots used
  apply returns_bind_next
  intro _ used
  apply returns_bind_next
  intro measured used
  apply returns_bind_next
  intro _ used
  apply returns_bind_next
  intro positioned used
  apply returns_bind_next
  intro _ used
  apply returns_bind_next
  intro allocation used
  apply returns_bind (nodesBorrowedAt observe source)
  · exact decodeEntries_borrowed observe source _ visit visits input allocation 0
      { arena with used := used } memory
  · intro decoded used borrowed
    exact returns_unchanged _ _ _ borrowed

theorem unionOption_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (variants : List (NatOperand × Desc)) (visit : Visit (variants.map Prod.snd))
    (visits : ∀ child member input arena, input.At observe source →
      Returns (Node.BorrowedAt observe source) (visit child member input arena))
    (selector : NatOperand) (input : Input) (arena : Delimited.ArenaState)
    (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (unionOption variants visit selector input arena) := by
  induction variants generalizing arena with
  | nil => exact returns_error _ _ _
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    unfold unionOption
    split
    · apply returns_bind (Node.BorrowedAt observe source)
      · exact visits desc (by simp) input arena memory
      · intro child used borrowed
        apply returns_bind_next
        intro allocation used
        apply returns_bind_next
        intro _ used
        exact returns_unchanged _ _ _ borrowed
    · apply ih
      intro child member childInput childArena childMemory
      exact visits child (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ member)
        childInput childArena childMemory

/-- The public decoder's native byte/bit views refer to the original input base,
including all nested slices and delimiter-retained bytes. Resource failure makes
no provenance claim about an absent value. No canonical schema is assumed. -/
theorem decode_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (desc : Desc) (input : Input) (arena : Delimited.ArenaState) (memory : input.At observe source) :
    Returns (Node.BorrowedAt observe source) (decode desc input arena) := by
  induction desc using Desc.inductionOnChildren generalizing input arena with
  | step desc ih =>
    rw [decode]
    cases desc with
    | primitive shape => exact primitive_borrowedAt observe source shape input arena memory
    | vector element length =>
      exact vector_borrowed observe source element length _
        (ih element (by simp [Desc.children])) input arena memory
    | list element limit =>
      exact list_borrowed observe source element (some limit) _
        (ih element (by simp [Desc.children])) input arena memory
    | progressiveList element limit =>
      exact list_borrowed observe source element limit _
        (ih element (by simp [Desc.children])) input arena memory
    | container fields => exact structureValue_borrowed observe source _ _ ih input arena memory
    | progressiveContainer active fields =>
      exact structureValue_borrowed observe source _ _ ih input arena memory
    | compatibleUnion variants =>
      unfold decodeStep
      dsimp only
      split
      · exact returns_error _ _ _
      · exact unionOption_borrowed observe source variants _ ih _ _ arena
          (Input.slice_at input observe source 1 input.bytes.size memory)

theorem run_borrowed (observe : Nat → Nat → Option Nat) (source : Nat)
    (desc : Desc) (bytes : Ssz.Bytes) (arena : Delimited.ArenaState)
    (memory : ByteView.BytesAt observe source bytes) :
    Returns (Node.BorrowedAt observe source) (run desc bytes arena) := by
  apply decode_borrowed observe source desc ⟨0, bytes⟩ arena
  simpa only [Input.At, Nat.add_zero] using memory

end SszNative.CodecDecode

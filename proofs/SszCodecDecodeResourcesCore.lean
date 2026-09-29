import SszCodecDecode
import SszCodecMeasureResourcesCore

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

abbrev CursorSafe := CodecMeasure.CursorSafe

abbrev cursorSafe_refl := CodecMeasure.cursorSafe_refl
abbrev cursorSafe_trans := CodecMeasure.cursorSafe_trans

theorem bind_cursorSafe {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (safeFirst : CursorSafe arena first.used)
    (safeNext : ∀ value used, CursorSafe { arena with used := used } (next value used).used) :
    CursorSafe arena (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using safeFirst
  | ok value =>
    simpa only [bind, result] using
      cursorSafe_trans arena first.used _ safeFirst (safeNext value first.used)

private theorem serialize_bind_cursorSafe {α β : Type} (arena : Delimited.ArenaState)
    (first : Serialize.Outcome α) (next : α → Nat → Serialize.Outcome β)
    (safeFirst : CursorSafe arena first.used)
    (safeNext : ∀ value used, CursorSafe { arena with used := used } (next value used).used) :
    CursorSafe arena (Serialize.bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [Serialize.bind, result] using safeFirst
  | ok value =>
    simpa only [Serialize.bind, result] using
      cursorSafe_trans arena first.used _ safeFirst (safeNext value first.used)

theorem typedReserve_cursorSafe (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) (allocation : Arena.Reservation)
    (reserved : TypedArena.reserve layout arena.base arena.capacity arena.used count =
      some allocation) : CursorSafe arena allocation.used := by
  constructor
  · unfold TypedArena.reserve at reserved
    split at reserved
    · cases reserved
      exact Nat.le_refl _
    · split at reserved
      · cases reserved
        exact TypedArena.used_le_finish _ _ _ _
      · cases reserved
  · intro valid
    exact ⟨valid.1, valid.2.1, valid.2.2.1,
      (TypedArena.reserve_cursor_bounds _ _ _ _ _ valid allocation reserved).2⟩

theorem reserve_cursorSafe (layout : TypedArena.Layout) (count : Nat)
    (arena : Delimited.ArenaState) : CursorSafe arena (reserve layout count arena).used := by
  unfold reserve
  dsimp only
  split
  · exact cursorSafe_refl arena
  · rename_i allocation reserved
    exact typedReserve_cursorSafe layout count arena allocation reserved

theorem exact_resources (expected : NatOperand) (actual used : Nat) :
    (exact expected actual used).used = used ∧ (exact expected actual used).effects = [] := by
  unfold exact
  split <;> exact ⟨rfl, rfl⟩

theorem bounded_resources (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    (bounded limit actual used).used = used ∧ (bounded limit actual used).effects = [] :=
  ⟨(Serialize.bounded_resources limit actual used).1, rfl⟩

theorem compositeSize_resources (size used : Nat) :
    (compositeSize size used).used = used ∧ (compositeSize size used).effects = [] := by
  unfold compositeSize
  split <;> exact ⟨rfl, rfl⟩

theorem narrow_resources (number : NatOperand) (failure : Error) (used : Nat) :
    (narrow number failure used).used = used ∧ (narrow number failure used).effects = [] := by
  unfold narrow
  split <;> exact ⟨rfl, rfl⟩

theorem packed_resources (offset : Nat) (bytes : Ssz.Bytes) (count : BitVec 128) (used : Nat) :
    (packed offset bytes count used).used = used ∧ (packed offset bytes count used).effects = [] := by
  unfold packed
  split <;> exact ⟨rfl, rfl⟩

theorem add_cursorSafe (left right : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (add left right arena).used :=
  CodecMeasure.add_cursorSafe left right arena

theorem mul_cursorSafe (left right : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (mul left right arena).used := by
  refine ⟨FixedSize.mul_used_mono left right arena, ?_⟩
  intro valid
  change Arena.Valid arena.base arena.capacity
    (NatMul.run left right arena.base arena.capacity arena.used).used
  rcases NatMul.run_resources left right arena.base arena.capacity arena.used with
    ⟨result, same, _⟩ | ⟨allocation, words, positive, reserved, same⟩
  · rw [same]
    exact valid
  · rw [same]
    exact Arena.valid_after_success _ _ _ _ valid allocation reserved

theorem division_cursorSafe (number : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) :
    CursorSafe arena (NatDivision.run number divisor arena.base arena.capacity arena.used).used := by
  cases allocated : (NatDivision.run number divisor arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatDivision.no_allocation_resources _ _ _ _ _ allocated).1]
    exact cursorSafe_refl arena
  | some allocation =>
    obtain ⟨cursor, _, checked, _, ending, _⟩ :=
      NatDivision.allocation_resources _ _ _ _ _ allocation allocated
    rw [cursor, ending]
    constructor
    · have start := Arena.used_le_start arena.base arena.used
      unfold Arena.finish
      omega
    · intro valid
      exact ⟨valid.1, valid.2.1, valid.2.2.1, checked.2.2.2.2.2⟩

private theorem fixedBitWidth_cursorSafe (length : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (FixedSize.bitWidth length arena).used := by
  unfold FixedSize.bitWidth
  apply serialize_bind_cursorSafe _ _ _ (division_cursorSafe length 8 arena)
  intro divided used
  split
  · exact cursorSafe_refl _
  · exact add_cursorSafe _ _ _

private theorem fixedPrimitive_cursorSafe (shape : Serialize.Desc) (arena : Delimited.ArenaState) :
    CursorSafe arena (FixedSize.measurePrimitive shape arena).used := by
  cases shape with
  | bitVector length =>
    unfold FixedSize.measurePrimitive
    apply serialize_bind_cursorSafe _ _ _ (fixedBitWidth_cursorSafe length arena)
    intro width used
    exact cursorSafe_refl _
  | _ => exact cursorSafe_refl _

mutual
  private theorem fixedMeasure_cursorSafe (desc : Desc) (arena : Delimited.ArenaState) :
      CursorSafe arena (FixedSize.measureFixed desc arena).used := by
    cases desc with
    | primitive shape => exact fixedPrimitive_cursorSafe shape arena
    | vector element length =>
      simp only [FixedSize.measureFixed]
      apply serialize_bind_cursorSafe _ _ _ (fixedMeasure_cursorSafe element arena)
      intro measured used
      cases measured with
      | none => exact cursorSafe_refl _
      | some width =>
        apply serialize_bind_cursorSafe _ _ _ (mul_cursorSafe width length { arena with used := used })
        intro total used
        exact cursorSafe_refl _
    | container fields => exact fixedFields_cursorSafe fields (.small 0) arena
    | progressiveContainer active fields => exact fixedFields_cursorSafe fields (.small 0) arena
    | _ => exact cursorSafe_refl _

  private theorem fixedFields_cursorSafe (fields : List (String × Desc)) (total : NatOperand)
      (arena : Delimited.ArenaState) :
      CursorSafe arena (FixedSize.measureFields fields total arena).used := by
    cases fields with
    | nil => exact cursorSafe_refl _
    | cons field rest =>
      rcases field with ⟨name, shape⟩
      simp only [FixedSize.measureFields]
      apply serialize_bind_cursorSafe _ _ _ (fixedMeasure_cursorSafe shape arena)
      intro measured used
      cases measured with
      | none => exact cursorSafe_refl _
      | some width =>
        apply serialize_bind_cursorSafe _ _ _ (add_cursorSafe total width { arena with used := used })
        intro next used
        exact fixedFields_cursorSafe rest next { arena with used := used }
end

theorem fixedSize_cursorSafe (desc : Desc) (arena : Delimited.ArenaState) :
    CursorSafe arena (fixedSize desc arena).used := by
  change CursorSafe arena (FixedSize.fixedSize desc arena).used
  unfold FixedSize.fixedSize
  split
  · exact fixedMeasure_cursorSafe desc arena
  · exact cursorSafe_refl _

theorem unsigned_cursorSafe (input : Input) (arena : Delimited.ArenaState) :
    CursorSafe arena (unsigned input arena).used := by
  unfold unsigned
  dsimp only
  split
  · exact cursorSafe_refl arena
  · split
    · exact cursorSafe_refl arena
    · rename_i allocation reserved
      exact CodecMeasure.reserve_cursorSafe arena _ allocation reserved

private theorem bitVectorRun_cursorSafe (length : NatOperand) (input : Input)
    (arena : Delimited.ArenaState) : CursorSafe arena (BitVector.run length input.bytes arena).used := by
  have divided := division_cursorSafe length 8 arena
  unfold BitVector.run
  dsimp only
  split
  · exact divided
  · rename_i quotient remainder dividedResult
    split
    · exact divided
    · have rounded := add_cursorSafe quotient (.small 1)
        { arena with used := (NatDivision.run length 8 arena.base arena.capacity arena.used).used }
      split <;> exact cursorSafe_trans arena _ _ divided rounded

theorem bitVector_cursorSafe (length : NatOperand) (input : Input)
    (arena : Delimited.ArenaState) : CursorSafe arena (bitVector length input arena).used := by
  unfold bitVector
  apply bind_cursorSafe _ _ _ (bitVectorRun_cursorSafe length input arena)
  intro count used
  rw [(packed_resources _ _ _ _).1]
  exact cursorSafe_refl _

theorem prepare_cursorSafe (arena : Delimited.ArenaState) (count : Delimited.CountWords)
    (ready : Delimited.Prepared) (prepared : Delimited.prepare arena count = some ready) :
    CursorSafe arena ready.used := by
  unfold Delimited.prepare at prepared
  split at prepared
  · cases prepared
    exact cursorSafe_refl arena
  · split at prepared
    · cases prepared
    · rename_i allocation reserved
      cases prepared
      exact CodecMeasure.reserve_cursorSafe arena 2 allocation reserved

theorem delimited_cursorSafe (limit : Option NatOperand) (input : Input)
    (arena : Delimited.ArenaState) : CursorSafe arena (delimited limit input arena).used := by
  unfold delimited
  dsimp only
  split
  · exact cursorSafe_refl arena
  · split
    · exact cursorSafe_refl arena
    · split
      · exact cursorSafe_refl arena
      · rename_i ready prepared
        apply cursorSafe_trans arena ready.used _ (prepare_cursorSafe arena _ ready prepared)
        apply bind_cursorSafe _ _ _
          (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl _)
        intro checked used
        rw [(packed_resources _ _ _ _).1]
        exact cursorSafe_refl _

theorem primitive_cursorSafe (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) : CursorSafe arena (primitive shape input arena).used := by
  cases shape with
  | bool =>
    unfold primitive
    apply bind_cursorSafe _ _ _
      (by rw [(exact_resources _ _ _).1]; exact cursorSafe_refl arena)
    intro checked used
    dsimp only
    split
    · exact cursorSafe_refl _
    · split <;> exact cursorSafe_refl _
  | uint width =>
    unfold primitive
    apply bind_cursorSafe _ _ _
      (by rw [(exact_resources _ _ _).1]; exact cursorSafe_refl arena)
    intro checked used
    exact unsigned_cursorSafe input _
  | byteVector length =>
    unfold primitive
    apply bind_cursorSafe _ _ _
      (by rw [(exact_resources _ _ _).1]; exact cursorSafe_refl arena)
    intro checked used
    exact cursorSafe_refl _
  | byteList limit =>
    unfold primitive
    apply bind_cursorSafe _ _ _
      (by rw [(bounded_resources _ _ _).1]; exact cursorSafe_refl arena)
    intro checked used
    exact cursorSafe_refl _
  | bitVector length => exact bitVector_cursorSafe length input arena
  | bitList limit => exact delimited_cursorSafe (some limit) input arena
  | progressiveBitList limit => exact delimited_cursorSafe limit input arena

end SszNative.CodecDecode

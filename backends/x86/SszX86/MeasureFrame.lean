import SszX86.MeasureCore
import SszX86.EmitOwnedMemory

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

abbrev frame_load := Emit.frame_load
abbrev span_shift := Emit.span_shift

theorem frame_load_window (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (pointer : BitVec 64)
    (off byteCount total : Nat) (bound : off + byteCount ≤ total)
    (safe : ∀ a, InSpan a pointer total → ¬ writable a) :
    Mem.loadInt after (pointer + BitVec.ofNat 64 off) byteCount =
      Mem.loadInt before (pointer + BitVec.ofNat 64 off) byteCount := by
  apply frame_load before after writable frame
  intro i hi
  exact safe _ (span_shift pointer off byteCount total bound ⟨i, hi, rfl⟩)

theorem operand_frame (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (operand : NatOperand)
    (safe : ∀ a, Emit.NatBorrowed operand a → ¬ writable a)
    (stored : operand.At (widthLoad before)) : operand.At (widthLoad after) := by
  cases operand with
  | small limb => trivial
  | large pointer limbs =>
    obtain ⟨positive, aligned, bound, observations⟩ := stored
    refine ⟨positive, aligned, bound, ?_⟩
    intro i
    have same : widthLoad after (pointer.toNat + 8 * i.val) 8 =
        widthLoad before (pointer.toNat + 8 * i.val) 8 := by
      unfold widthLoad
      rw [width_address]
      congr 1
      apply frame_load_window before after writable frame pointer
        (8 * i.val) 8 (8 * limbs.length) (by have := i.isLt; omega)
      exact safe
    rw [same]
    exact observations i

theorem descriptor_frame (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (pointer : BitVec 64) (desc : Desc)
    (safe : ∀ a, DescLive pointer desc a ∨ DescBorrowed desc a → ¬ writable a)
    (stored : DescAt before pointer desc) : DescAt after pointer desc := by
  refine ⟨?_, ?_⟩
  · rw [frame_load before after writable frame pointer 8 (by
      intro i hi
      exact safe _ (Or.inl (Or.inl ⟨i, hi, rfl⟩)))]
    exact stored.1
  · have payload := stored.2
    cases desc with
    | bool => trivial
    | uint operand | byteVector operand | byteList operand | bitVector operand | bitList operand =>
      apply Emit.natAt_frame before after writable frame (pointer + 8) operand
      · intro a inside
        exact safe a (Or.inl (Or.inr inside))
      · intro a inside
        exact safe a (Or.inr inside)
      · exact payload
    | progressiveBitList limit =>
      cases limit with
      | none =>
        change Mem.loadInt after (pointer + 8) 4 = some 0
        rw [frame_load before after writable frame (pointer + 8) 4 (by
          intro i hi
          exact safe _ (Or.inl (Or.inr ⟨i, hi, rfl⟩)))]
        exact payload
      | some operand =>
        refine ⟨?_, ?_⟩
        · rw [frame_load before after writable frame (pointer + 8) 4 (by
            intro i hi
            exact safe _ (Or.inl (Or.inr (Or.inl ⟨i, hi, rfl⟩))))]
          exact payload.1
        · apply Emit.natAt_frame before after writable frame (pointer + 16) operand
          · intro a inside
            exact safe a (Or.inl (Or.inr (Or.inr inside)))
          · intro a inside
            exact safe a (Or.inr inside)
          · exact payload.2

theorem value_frame (before after : DataMem) (writable : BitVec 64 → Prop)
    (frame : MemoryFrame before after writable) (pointer buffer : BitVec 64) (value : Value)
    (safe : ∀ a, ValueLive pointer value a ∨ ValueBorrowed value buffer a → ¬ writable a)
    (stored : ValueAt before pointer buffer value) : ValueAt after pointer buffer value := by
  refine ⟨?_, ?_⟩
  · rw [frame_load before after writable frame pointer 1 (by
      intro i hi
      exact safe _ (Or.inl (Or.inl ⟨i, hi, rfl⟩)))]
    exact stored.1
  · have payload := stored.2
    cases value with
    | bool boolean =>
      change Mem.loadInt after (pointer + 1) 1 = some (if boolean then 1 else 0)
      rw [frame_load before after writable frame (pointer + 1) 1 (by
        intro i hi
        exact safe _ (Or.inl (Or.inr ⟨i, hi, rfl⟩)))]
      exact payload
    | uint operand =>
      apply Emit.natAt_frame before after writable frame (pointer + 8) operand
      · intro a inside
        exact safe a (Or.inl (Or.inr inside))
      · intro a inside
        exact safe a (Or.inr inside)
      · exact payload
    | bytes data =>
      have fields (off : Nat) (bound : off + 8 ≤ 16) :=
        frame_load_window before after writable frame (pointer + 8) off 8 16 bound
          (fun a inside => safe a (Or.inl (Or.inr inside)))
      have first := fields 0 (by decide)
      have second := fields 8 (by decide)
      simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at first second
      refine ⟨first.trans payload.1, second.trans payload.2.1, ?_, payload.2.2.2⟩
      intro i hi
      rw [frame _ (safe _ (Or.inr ⟨i, hi, rfl⟩))]
      exact payload.2.2.1 i hi
    | bits data =>
      have fields (off : Nat) (bound : off + 8 ≤ 32) :=
        frame_load_window before after writable frame (pointer + 16) off 8 32 bound
          (fun a inside => safe a (Or.inl (Or.inr inside)))
      have first := fields 0 (by decide)
      have second := fields 8 (by decide)
      have third := fields 16 (by decide)
      have fourth := fields 24 (by decide)
      simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
        at first second third fourth
      refine ⟨first.trans payload.1, second.trans payload.2.1,
        third.trans payload.2.2.1, fourth.trans payload.2.2.2.1, ?_, payload.2.2.2.2.2⟩
      intro i hi
      rw [frame _ (safe _ (Or.inr ⟨i, hi, rfl⟩))]
      exact payload.2.2.2.2.1 i hi
    | seq _ | union _ _ => trivial

theorem resultWrites_span (out : BitVec 64) (outcome : Outcome NatOperand)
    (a : BitVec 64) (writes : ResultWrites out outcome a) : InSpan a out 72 := by
  cases result : outcome.result with
  | ok operand =>
    simp only [ResultWrites, result] at writes
    rcases writes with ⟨i, hi, equal⟩ | inside
    · exact ⟨i, by omega, equal⟩
    · exact span_shift out 64 4 72 (by decide) inside
  | error reason =>
    simp only [ResultWrites, result] at writes
    rcases writes with ⟨i, hi, equal⟩ | ⟨_, inside⟩
    · exact ⟨i, by omega, equal⟩
    · exact span_shift out 68 4 72 (by decide) inside

end SszX86.Measure

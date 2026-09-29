import SszArm.NatCompareMemory
import SszArm.DelimitedOption
import SszLimbMul

namespace SszArm.NatMul

open NatCompare (Words)
open Delimited (Span Protected MemoryFrame)

/-- The high-product lowering spill and the current output allocation. -/
def loopWrites (sp pointer : BitVec 64) (count : Nat) : List Span :=
  [(sp.toNat - 48, 48), (pointer.toNat, 8 * count)]

structure LoopSpace (sp pointer : BitVec 64) (count : Nat) : Prop where
  stack : 48 ≤ sp.toNat
  physical : pointer.toNat + 8 * count ≤ 2^64
  apart : pointer.toNat + 8 * count ≤ sp.toNat - 48 ∨ sp.toNat ≤ pointer.toNat

theorem LoopSpace.address {sp pointer : BitVec 64} {count index : Nat}
    (space : LoopSpace sp pointer count) (hi : index < count) :
    (pointer + BitVec.ofNat 64 (8 * index)).toNat = pointer.toNat + 8 * index := by
  have hp := pointer.isLt
  have physical := space.physical
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem LoopSpace.prefix {sp pointer : BitVec 64} {count n : Nat}
    (space : LoopSpace sp pointer count) (hn : n ≤ count) : LoopSpace sp pointer n :=
  ⟨space.stack, by have := space.physical; omega, by have := space.apart; omega⟩

private theorem word_address_add (pointer : BitVec 64) (i j : Nat) :
    pointer + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (8 * j) =
      pointer + BitVec.ofNat 64 (8 * (i + j)) := by
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- Split the current memory observation at the emitted prefix boundary. -/
theorem words_append (s : ArmState) (pointer : BitVec 64)
    (doneWords unread : List (BitVec 64)) :
    Words s pointer (doneWords ++ unread) ↔
      Words s pointer doneWords ∧
      Words s (pointer + BitVec.ofNat 64 (8 * doneWords.length)) unread := by
  constructor
  · intro observed
    constructor
    · intro i
      have h := observed ⟨i.val, by simp only [List.length_append]; omega⟩
      simpa only [Fin.getElem_fin, List.getElem_append_left i.isLt] using h
    · intro i
      have h := observed ⟨doneWords.length + i.val, by simp only [List.length_append]; omega⟩
      simp only [Fin.getElem_fin] at h ⊢
      rw [List.getElem_append_right (by omega)] at h
      simpa only [Nat.add_sub_cancel_left, word_address_add] using h
  · rintro ⟨doneAt, unreadAt⟩ i
    have hi := i.isLt
    simp only [Fin.getElem_fin]
    by_cases low : i.val < doneWords.length
    · simpa only [Fin.getElem_fin, List.getElem_append_left low] using doneAt ⟨i.val, low⟩
    · rw [List.getElem_append_right (by omega)]
      have h := unreadAt ⟨i.val - doneWords.length, by simp only [List.length_append] at hi; omega⟩
      simpa only [Fin.getElem_fin, word_address_add,
        Nat.add_sub_of_le (by omega : doneWords.length ≤ i.val)] using h

theorem words_take {s : ArmState} {pointer : BitVec 64} {words : List (BitVec 64)}
    (observed : Words s pointer words) (n : Nat) : Words s pointer (words.take n) := by
  intro i
  have hi : i.val < words.length := by have := i.isLt; simp only [List.length_take] at this; omega
  simpa only [Fin.getElem_fin, List.getElem_take] using observed ⟨i.val, hi⟩

theorem words_drop {s : ArmState} {pointer : BitVec 64} {words : List (BitVec 64)}
    (observed : Words s pointer words) (n : Nat) :
    Words s (pointer + BitVec.ofNat 64 (8 * n)) (words.drop n) := by
  intro i
  have hi : n + i.val < words.length := by
    have := i.isLt
    simp only [List.length_drop] at this
    omega
  simpa only [Fin.getElem_fin, word_address_add, List.getElem_drop] using observed ⟨n + i.val, hi⟩

/-- A round's proved frame and its actual stored-word observation update the
current list. No unread output word is postulated or initialized by this lemma. -/
theorem words_set_of_frame {s t : ArmState} {sp pointer value : BitVec 64}
    {words : List (BitVec 64)} (space : LoopSpace sp pointer words.length)
    (observed : Words s pointer words) (index : Nat) (hi : index < words.length)
    (frame : MemoryFrame [(sp.toNat - 48, 48),
      ((pointer + BitVec.ofNat 64 (8 * index)).toNat, 8)] s t)
    (stored : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * index)) t = value) :
    Words t pointer (words.set index value) := by
  intro j
  have hj : j.val < words.length := by simpa only [List.length_set] using j.isLt
  simp only [Fin.getElem_fin, List.getElem_set]
  by_cases same : index = j.val
  · rw [if_pos same]
    simpa only [same] using stored
  · rw [if_neg same]
    rw [frame.read _ 8]
    · exact observed ⟨j.val, hj⟩
    · rw [space.address hj]
      have := space.physical
      omega
    · rw [space.address hj]
      right
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have := space.apart
        have := space.stack
        omega
      · rw [space.address hi]
        omega

/-- Direct single-store specialization, deriving both observation and frame
from the architectural byte store rather than accepting a future memory list. -/
theorem words_store {s : ArmState} {sp pointer : BitVec 64} {words : List (BitVec 64)}
    (space : LoopSpace sp pointer words.length) (observed : Words s pointer words)
    (index : Nat) (hi : index < words.length) (value : BitVec 64) :
    Words (write_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * index)) value s)
      pointer (words.set index value) := by
  have physical : (pointer + BitVec.ofNat 64 (8 * index)).toNat + 8 ≤ 2^64 := by
    rw [space.address hi]
    have := space.physical
    omega
  apply words_set_of_frame space observed index hi
  · intro address outside
    exact BoolCodec.write_mem_bytes_frame s _ 8 value address physical
      (outside ((pointer + BitVec.ofNat 64 (8 * index)).toNat, 8) (by simp))
  · exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ value physical

/-- Advancing the emitted prefix is just replacement at its current length. -/
theorem words_replace_of_frame {s t : ArmState} {sp pointer old value : BitVec 64}
    (doneWords unread : List (BitVec 64))
    (space : LoopSpace sp pointer (doneWords ++ old :: unread).length)
    (observed : Words s pointer (doneWords ++ old :: unread))
    (frame : MemoryFrame [(sp.toNat - 48, 48),
      ((pointer + BitVec.ofNat 64 (8 * doneWords.length)).toNat, 8)] s t)
    (stored : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * doneWords.length)) t = value) :
    Words t pointer ((doneWords ++ [value]) ++ unread) := by
  have updated := words_set_of_frame space observed doneWords.length
    (by simp only [List.length_append, List.length_cons]; omega) frame stored
  simpa only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero, List.append_assoc, List.singleton_append] using updated

end SszArm.NatMul

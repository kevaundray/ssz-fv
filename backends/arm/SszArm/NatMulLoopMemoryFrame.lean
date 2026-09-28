import SszArm.NatMulLoopMemory

namespace SszArm.NatMul

open NatCompare (Words)
open Delimited (Span Protected MemoryFrame)

/-- Preserve every original limb, including redundant high zero limbs, from
static separation and the actual memory frame. -/
theorem words_preserve {s t : ArmState} {writes : List Span}
    {pointer : BitVec 64} {words : List (BitVec 64)}
    (frame : MemoryFrame writes s t)
    (physical : pointer.toNat + 8 * words.length ≤ 2^64)
    (separate : Protected writes pointer.toNat (8 * words.length))
    (observed : Words s pointer words) : Words t pointer words := by
  intro i
  have hi := i.isLt
  have address : (pointer + BitVec.ofNat 64 (8 * i.val)).toNat =
      pointer.toNat + 8 * i.val := by
    have hp := pointer.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [frame.read _ 8]
  · exact observed i
  · rw [address]
    omega
  · rw [address]
    exact separate.subspan (8 * i.val) 8 (by omega)

/-- Widen a proved single-cell round frame to its complete output allocation. -/
theorem loopFrame_of_cell {s t : ArmState} {sp pointer : BitVec 64} {count : Nat}
    (space : LoopSpace sp pointer count) (index : Nat) (hi : index < count)
    (frame : MemoryFrame [(sp.toNat - 48, 48),
      ((pointer + BitVec.ofNat 64 (8 * index)).toNat, 8)] s t) :
    MemoryFrame (loopWrites sp pointer count) s t := by
  intro address outside
  apply frame address
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [loopWrites])
  · have output := outside (pointer.toNat, 8 * count) (by simp [loopWrites])
    simp only [Prod.fst, Prod.snd] at output ⊢
    rw [space.address hi]
    omega

/-- Appending the first observation of a newly written cell requires no old
value or initialization assumption for that cell. -/
theorem words_snoc_of_frame {s t : ArmState} {sp pointer value : BitVec 64}
    {doneWords : List (BitVec 64)} (space : LoopSpace sp pointer (doneWords.length + 1))
    (observed : Words s pointer doneWords)
    (frame : MemoryFrame [(sp.toNat - 48, 48),
      ((pointer + BitVec.ofNat 64 (8 * doneWords.length)).toNat, 8)] s t)
    (stored : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * doneWords.length)) t = value) :
    Words t pointer (doneWords ++ [value]) := by
  let old := read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * doneWords.length)) s
  have current : Words s pointer (doneWords ++ [old]) := by
    apply (words_append s pointer doneWords [old]).mpr
    refine ⟨observed, ?_⟩
    intro i
    have zero : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
    simpa [zero, old]
  have sized : LoopSpace sp pointer (doneWords ++ [old]).length := by simpa using space
  have updated := words_set_of_frame sized current doneWords.length
    (by simp only [List.length_append, List.length_singleton]; omega) frame stored
  simpa only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero] using updated

/-- Actual byte-store specialization of prefix growth. -/
theorem words_snoc_store {s : ArmState} {sp pointer : BitVec 64}
    {doneWords : List (BitVec 64)} (space : LoopSpace sp pointer (doneWords.length + 1))
    (observed : Words s pointer doneWords) (value : BitVec 64) :
    Words (write_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * doneWords.length)) value s)
      pointer (doneWords ++ [value]) := by
  have index : doneWords.length < doneWords.length + 1 := by omega
  have physical : (pointer + BitVec.ofNat 64 (8 * doneWords.length)).toNat + 8 ≤ 2^64 := by
    rw [space.address index]
    have := space.physical
    omega
  apply words_snoc_of_frame space observed
  · intro address outside
    exact BoolCodec.write_mem_bytes_frame s _ 8 value address physical
      (outside ((pointer + BitVec.ofNat 64 (8 * doneWords.length)).toNat, 8) (by simp))
  · exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ value physical

end SszArm.NatMul

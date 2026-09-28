import SszX86.MeasurePost

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

/-- Only actually published result bytes are excluded from the result frame.
Neither arena allocation nor cursor/activation writes can silently clobber the
remaining owned result bytes. Propagated errors alone may write68..71. -/
theorem Owned.result_untouched {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (i : Nat) (hi : i < 72)
    (padding : ¬ ResultWrites s.regs.rdi.toBitVec
      (measure desc value (arenaState address capacity used))
      (s.regs.rdi.toBitVec + BitVec.ofNat 64 i)) :
    ¬ Writable s (measure desc value (arenaState address capacity used))
      (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) := by
  intro writes
  rcases writes with result | allocation | ⟨_, cursor⟩ | stack
  · exact padding result
  · obtain ⟨j, hj, equal⟩ := allocation_in_free desc value address capacity used _ allocation
    have arenaBound := owned.arenaBound
    have resultBound := owned.resultBound
    have apart := owned.freeResult
    have equality : address.toNat + used.toNat + j = s.regs.rdi.toNat + i := by
      simp only [← UInt64.toNat_toBitVec] at resultBound ⊢
      bv_omega
    unfold Body.Apart at apart
    omega
  · obtain ⟨j, hj, equal⟩ := cursor
    apply owned.resultHeader i hi (16 + j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal
  · obtain ⟨j, hj, equal⟩ := stack
    exact owned.resultStack i hi j (by omega) equal

/-- Wrapper-facing preservation of uninitialized/arbitrary result padding. No
initial padding values are read as semantic input or asserted to be zero. -/
theorem Post.result_padding {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool} {t : MachineState}
    (post : Post s desc value buffer address capacity used ra t)
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (i : Nat) (hi : i < 72)
    (padding : ¬ ResultWrites s.regs.rdi.toBitVec
      (measure desc value (arenaState address capacity used))
      (s.regs.rdi.toBitVec + BitVec.ofNat 64 i)) :
    t.1.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) =
      s.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) :=
  post.frame _ (owned.result_untouched i hi padding)

end SszX86.Measure

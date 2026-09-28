import SszArm.BitVectorValueCorrect
import SszArm.BitVectorMemory

namespace SszArm.BitVector.ValueTail

/-- The terminal storage obligations follow from the original physical body
ownership and the actual preserved output/SP registers. -/
theorem space_of_owned (entry s : ArmState) (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : BitVector.Owned entry length data)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) entry)
    (out : r (.GPR 23#5) s = r (.GPR 0#5) entry) : Space s := by
  have stackLow := owned.stackLow
  have stackHigh := owned.stackHigh
  have output := owned.outputBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sp]; omega
  · rw [sp]; omega
  · rw [out]; omega
  · rw [sp, out]
    rcases owned.outputStack with empty | separate
    · omega
    · have disjoint := separate ((r (.GPR 31#5) entry).toNat - 80, 448) (by simp)
      simp only [Prod.fst, Prod.snd] at disjoint
      omega

theorem writes_covered (entry s : ArmState)
    (stackLow : 80 ≤ (r (.GPR 31#5) entry).toNat)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) entry)
    (out : r (.GPR 23#5) s = r (.GPR 0#5) entry) :
    BitVector.Covers (BitVector.localWrites entry) (writes s) := by
  intro span member
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false, sp, out] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨((r (.GPR 0#5) entry).toNat, 80), by simp [BitVector.localWrites], by omega, by omega⟩
  · exact ⟨((r (.GPR 0#5) entry).toNat, 80), by simp [BitVector.localWrites], by omega, by omega⟩
  · exact ⟨((r (.GPR 0#5) entry).toNat, 80), by simp [BitVector.localWrites], by omega, by omega⟩
  · exact ⟨((r (.GPR 31#5) entry).toNat - 80, 352), by simp [BitVector.localWrites], by omega, by omega⟩

/-- This is a weakening of the proved exact frame, not an extra writable-memory
assumption. It composes directly with the helper/body resource frame. -/
theorem final_body_frame (entry s : ArmState) (base : BitVec 64)
    (outcome : SszNative.BitVector.Outcome) (space : Space s)
    (stackLow : 80 ≤ (r (.GPR 31#5) entry).toNat)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) entry)
    (out : r (.GPR 23#5) s = r (.GPR 0#5) entry) :
    Delimited.MemoryFrame (BitVector.writesFor entry outcome) s (result s base) :=
  ((BitVector.local_covered entry outcome).trans (writes_covered entry s stackLow sp out)).frame
    (final_frame s base space)

end SszArm.BitVector.ValueTail

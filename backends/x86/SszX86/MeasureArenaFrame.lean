import SszX86.MeasureResources
import SszX86.MeasureFrame

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem allocation_in_free (desc : Desc) (value : Value)
    (address capacity used a : BitVec 64)
    (writes : AllocationWrites (measure desc value (arenaState address capacity used)).calls a) :
    InSpan a (address + used) (capacity.toNat - used.toNat) := by
  obtain ⟨call, member, reservation, allocated, i, hi, rfl⟩ := writes
  obtain ⟨low, high⟩ :=
    (measure_resources desc value (arenaState address capacity used)).allocations call member reservation allocated
  simp only [arenaState] at low high
  refine ⟨reservation.pointer - (address.toNat + used.toNat) + i, by omega, ?_⟩
  bv_omega

/-- The actual writable body footprint excludes all six saved words and RET's
slot. Allocations are proved inside the original free suffix, not presumed safe. -/
theorem BodyOwned.saved_untouched {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (i : Nat) (hi : i < 56) :
    ¬ BodyWritable s (measure desc value (arenaState address capacity used))
      (s.regs.rsp.toBitVec + 216 + BitVec.ofNat 64 i) := by
  intro writes
  have addressEq : s.regs.rsp.toBitVec + 216 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 (232 + i) := by bv_omega
  rcases writes with result | allocation | ⟨_, cursor⟩ | scratch
  · obtain ⟨j, hj, equal⟩ := resultWrites_span _ _ _ result
    apply owned.resultStack j hj (232 + i) (by omega)
    rw [← addressEq]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := allocation_in_free desc value address capacity used _ allocation
    have arenaBound := owned.arenaBound
    have stackLow := owned.stackLow
    have stackBound := owned.stackBound
    have apart := owned.freeStack
    have lower : used.toNat < capacity.toNat := by omega
    have equality : address.toNat + used.toNat + j = s.regs.rsp.toNat + 216 + i := by
      simp only [← UInt64.toNat_toBitVec] at stackLow stackBound ⊢
      bv_omega
    unfold Body.Apart at apart
    omega
  · obtain ⟨j, hj, equal⟩ := cursor
    apply owned.headerStack (16 + j) (by omega) (232 + i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← addressEq]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := scratch
    bv_omega

end SszX86.Measure

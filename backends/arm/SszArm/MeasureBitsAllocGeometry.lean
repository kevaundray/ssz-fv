import SszArm.MeasureBitsAllocModel

namespace SszArm.Measure.Bits.Alloc

structure CommitSpace (site : Site) (s : ArmState) : Prop where
  header : (r (.GPR 20#5) s).toNat + 24 ≤ 2^64
  positive : 0 < (allocatedPointer site s).toNat
  aligned : (allocatedPointer site s).toNat % 8 = 0
  payload : (allocatedPointer site s).toNat + 16 ≤ 2^64
  separate : (allocatedPointer site s).toNat + 16 ≤ (r (.GPR 20#5) s).toNat ∨
    (r (.GPR 20#5) s).toNat + 24 ≤ (allocatedPointer site s).toNat

theorem Input.commitSpace {site : Site} {s t : ArmState}
    (input : Input s) (reached : Checkpoint site s t)
    (checks : SszNative.Arena.Checks (addressWord s).toNat (capacityWord s).toNat (usedWord s).toNat 2)
    (address : r (.GPR site.baseReg) t = addressWord s)
    (start : (r (.GPR site.usedReg) t).toNat = SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat) :
    CommitSpace site t ∧ (allocatedPointer site t).toNat =
      (addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat := by
  have before := SszNative.Arena.used_le_start (addressWord s).toNat (usedWord s).toNat
  have finish := checks.2.2.2.2.2
  have finishEq : SszNative.Arena.finish (addressWord s).toNat (usedWord s).toNat 2 =
      SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat + 16 := rfl
  have storage := input.storage
  have positive := input.nonnull (by omega)
  have pointerNat : (allocatedPointer site t).toNat =
      (addressWord s).toNat + SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat := by
    simp only [allocatedPointer, BitVec.toNat_add, address, start]
    exact Nat.mod_eq_of_lt (by omega)
  have header := reached.frame.registers 20#5 (by cases site <;> decide)
  have separate : (allocatedPointer site t).toNat + 16 ≤ (r (.GPR 20#5) s).toNat ∨
      (r (.GPR 20#5) s).toNat + 24 ≤ (allocatedPointer site t).toNat := by
    rcases input.freeHeader with empty | disjoint
    · omega
    · have apart := disjoint ((r (.GPR 20#5) s).toNat, 24) (by simp)
      rw [pointerNat]
      dsimp at apart
      omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, pointerNat⟩
  · simpa only [header] using input.header
  · rw [pointerNat]; omega
  · rw [pointerNat, SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  · rw [pointerNat]; omega
  · simpa only [header] using separate

end SszArm.Measure.Bits.Alloc

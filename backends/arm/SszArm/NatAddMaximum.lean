import SszArm.NatAddSelect

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The native maximum selection and checked count increment retain the original
operand payloads. Physically representable limb counts cannot take the wrap edge. -/
theorem maximum_select (s : ArmState) (base : BitVec 64) (leftCount rightCount : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 128#64)
    (leftBound : leftCount < 2^64) (rightBound : rightCount < 2^64)
    (allocatedBound : max leftCount rightCount + 1 < 2^64)
    (leftReg : r (.GPR 8#5) s = BitVec.ofNat 64 leftCount)
    (rightReg : r (.GPR 10#5) s = BitVec.ofNat 64 rightCount) :
    let t := block base [.p128, .p132, .p136, .p140] s
    run 4 s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (max leftCount rightCount) ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 10#5) t = r (.GPR 10#5) s ∧ read_pc t = base + 144#64 := by
  have hpc : r .PC s = base + 128#64 := hp
  have leftValue : (BitVec.ofNat 64 leftCount).toNat = leftCount := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound]
  have rightValue : (BitVec.ofNat 64 rightCount).toNat = rightCount := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt rightBound]
  have selected : (if (AddWithCarry (BitVec.ofNat 64 rightCount)
        (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.c = 1#1 ∧
        (AddWithCarry (BitVec.ofNat 64 rightCount)
          (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.z = 0#1
      then BitVec.ofNat 64 rightCount else BitVec.ofNat 64 leftCount) =
        BitVec.ofNat 64 (max leftCount rightCount) := by
    have cmpz := Udivti3.cmp_zero (BitVec.ofNat 64 rightCount) (BitVec.ofNat 64 leftCount)
    have cmpc := Udivti3.cmp_carry (BitVec.ofNat 64 rightCount) (BitVec.ofNat 64 leftCount)
    have zbit := (AddWithCarry (BitVec.ofNat 64 rightCount)
      (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.z.isLt
    have equal : BitVec.ofNat 64 rightCount = BitVec.ofNat 64 leftCount ↔ rightCount = leftCount := by
      constructor
      · intro same
        have value := congrArg BitVec.toNat same
        simpa only [leftValue, rightValue] using value
      · intro same; rw [same]
    rw [leftValue, rightValue] at cmpc
    rw [equal] at cmpz
    by_cases less : leftCount < rightCount
    · have flags : (AddWithCarry (BitVec.ofNat 64 rightCount)
          (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.c = 1#1 ∧
          (AddWithCarry (BitVec.ofNat 64 rightCount)
            (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.z = 0#1 := by
        constructor
        · exact cmpc.mpr (by omega)
        · bv_omega
      simp [flags, Nat.max_eq_right (by omega : leftCount ≤ rightCount)]
    · have flags : ¬ ((AddWithCarry (BitVec.ofNat 64 rightCount)
          (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.c = 1#1 ∧
          (AddWithCarry (BitVec.ofNat 64 rightCount)
            (~~~(BitVec.ofNat 64 leftCount)) 1#1).2.z = 0#1) := by
        intro both
        have le := cmpc.mp both.1
        have eq : rightCount = leftCount := by omega
        have z := cmpz.mpr eq
        bv_omega
      simp only [flags, ↓reduceIte, Nat.max_eq_left (by omega : rightCount ≤ leftCount)]
  simp only [NatCompare.cmp_zero_bit] at selected
  have nowrap : BitVec.ofNat 64 (max leftCount rightCount) + 1#64 ≠ 0#64 := by bv_omega
  have follow : Follows base [.p128, .p132, .p136, .p140] s := by
    simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follow, scan_frame base _ s (by decide),
    scan_zero base _ s (by decide), ?_, ?_, ?_, ?_⟩
  all_goals simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, leftReg, rightReg, selected, nowrap]

end SszArm.NatAdd

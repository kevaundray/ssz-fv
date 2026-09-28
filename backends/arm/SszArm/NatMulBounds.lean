import SszArm.NatMulExec

namespace SszArm.NatMul

theorem inner_index_lt (left right i j : Nat) (leftIndex : i < left)
    (rightIndex : j < right) : i + j < left + right := by omega

theorem carry_index_lt (left right i : Nat) (leftIndex : i < left) :
    i + right < left + right := by omega

theorem inner_guard_run (s : ArmState) (base : BitVec 64)
    (left right i j : Nat) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 680#64)
    (row : r (.GPR 12#5) s = BitVec.ofNat 64 i)
    (column : r (.GPR 16#5) s = BitVec.ofNat 64 j)
    (count : r (.GPR 19#5) s = BitVec.ofNat 64 (left + right))
    (physicalCount : left + right < 2^64)
    (leftIndex : i < left) (rightIndex : j < right) :
    run 3 s = block base [.p680, .p684, .p688] s ∧
      read_pc (run 3 s) = base + 692#64 ∧
      r (.GPR 0#5) (run 3 s) = BitVec.ofNat 64 (i + j) := by
  have indexBound := inner_index_lt left right i j leftIndex rightIndex
  have safe : ¬(AddWithCarry (BitVec.ofNat 64 i + BitVec.ofNat 64 j)
      (~~~BitVec.ofNat 64 (left + right)) 1#1).2.c = 1#1 := by
    rw [Udivti3.cmp_carry, ← BitVec.ofNat_add]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physicalCount,
      Nat.mod_eq_of_lt (show i + j < 2^64 by omega)]
    omega
  have hpc : r .PC s = base + 680#64 := pc
  have execution : run 3 s = block base [.p680, .p684, .p688] s := by
    apply block_run base [.p680, .p684, .p688] s code error aligned
    simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨execution, ?_, ?_⟩
  · rw [execution]
    simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, row, column, count, safe]
  · rw [execution]
    simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, row, column, ← BitVec.ofNat_add]

theorem carry_guard_run (s : ArmState) (base : BitVec 64)
    (left right i : Nat) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 952#64)
    (row : r (.GPR 12#5) s = BitVec.ofNat 64 i)
    (width : r (.GPR 22#5) s = BitVec.ofNat 64 right)
    (count : r (.GPR 19#5) s = BitVec.ofNat 64 (left + right))
    (physicalCount : left + right < 2^64) (leftIndex : i < left) :
    run 3 s = block base [.p952, .p956, .p960] s ∧
      read_pc (run 3 s) = base + 964#64 ∧
      r (.GPR 0#5) (run 3 s) = BitVec.ofNat 64 (i + right) := by
  have indexBound := carry_index_lt left right i leftIndex
  have safe : ¬(AddWithCarry (BitVec.ofNat 64 i + BitVec.ofNat 64 right)
      (~~~BitVec.ofNat 64 (left + right)) 1#1).2.c = 1#1 := by
    rw [Udivti3.cmp_carry, ← BitVec.ofNat_add]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physicalCount,
      Nat.mod_eq_of_lt (show i + right < 2^64 by omega)]
    omega
  have hpc : r .PC s = base + 952#64 := pc
  have execution : run 3 s = block base [.p952, .p956, .p960] s := by
    apply block_run base [.p952, .p956, .p960] s code error aligned
    simp [Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  refine ⟨execution, ?_, ?_⟩
  · rw [execution]
    simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, row, width, count, safe]
  · rw [execution]
    simp [block, Op.effect, put, next, Udivti3.compare, Udivti3.next,
      state_simp_rules, row, width, ← BitVec.ofNat_add]

end SszArm.NatMul

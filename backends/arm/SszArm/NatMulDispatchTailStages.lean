import SszArm.NatMulDispatchCompare

namespace SszArm.NatMul

def leftSelectOps (pointer : BitVec 64) : List Op :=
  if pointer = 0#64 then [.p384] else [.p384, .p388, .p392]

theorem left_select_follows (s : ArmState) (base word : BitVec 64)
    (hp : read_pc s = base + 384#64)
    (low : if r (.GPR 1#5) s = 0#64 then r (.GPR 8#5) s = word
      else r (.GPR 8#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = word) :
    Follows base (leftSelectOps (r (.GPR 1#5) s)) s := by
  have hpc : r .PC s = base + 384#64 := hp
  by_cases small : r (.GPR 1#5) s = 0#64
  all_goals
    simp only [small, ↓reduceIte] at low
    simp only [leftSelectOps, small, ↓reduceIte, Follows, Op.row, Op.effect]
    arm_state_nf
  all_goals simp [hpc, small, low]

theorem left_select_values (s : ArmState) (base word : BitVec 64)
    (low : if r (.GPR 1#5) s = 0#64 then r (.GPR 8#5) s = word
      else r (.GPR 8#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = word) :
    let t := block base (leftSelectOps (r (.GPR 1#5) s)) s
    r (.GPR 8#5) t = word ∧ read_pc t = base + 396#64 := by
  by_cases small : r (.GPR 1#5) s = 0#64
  all_goals
    simp only [small, ↓reduceIte] at low
    simp only [leftSelectOps, small, ↓reduceIte, block,
      List.foldl_cons, List.foldl_nil, Op.effect, put, next]
    arm_state_nf
  all_goals simp [small, low, BitVec.add_assoc]

theorem left_swap_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 396#64) : Follows base [.p396, .p400, .p404, .p408] s := by
  have hpc : r .PC s = base + 396#64 := hp
  simp only [Follows, Op.row, Op.effect, put, next]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

theorem left_swap_values (s : ArmState) (base : BitVec 64) :
    let t := block base [.p396, .p400, .p404, .p408] s
    read_pc t = base + 232#64 ∧
    r (.GPR 1#5) t = r (.GPR 3#5) s ∧
    r (.GPR 2#5) t = r (.GPR 4#5) s ∧
    r (.GPR 3#5) t = r (.GPR 8#5) s := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
  arm_state_nf
  all_goals simp

theorem right_prepare_values (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 228#64) :
    let t := block base [.p228] s
    read_pc t = base + 232#64 ∧
    r (.GPR 1#5) t = r (.GPR 1#5) s ∧
    r (.GPR 2#5) t = r (.GPR 2#5) s ∧
    r (.GPR 3#5) t = r (.GPR 4#5) s := by
  have hpc : r .PC s = base + 228#64 := hp
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

end SszArm.NatMul

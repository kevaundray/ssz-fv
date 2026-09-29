import SszArm.NatMulScanRight

namespace SszArm.NatMul

open SszNative.Limbs

def smallLeftHeadOps (word : BitVec 64) : List Op :=
  if word = 0#64 then [.p28, .p104, .p148] else [.p28, .p104, .p108]

def smallLeftHeadPC (s : ArmState) (base : BitVec 64) : BitVec 64 :=
  base + (if r (.GPR 2#5) s = 0#64 then
    if r (.GPR 3#5) s = 0#64 then 264#64 else 152#64
  else if r (.GPR 3#5) s = 0#64 then 140#64 else 112#64)

theorem small_left_head_state (s : ArmState) (base : BitVec 64) :
    block base (smallLeftHeadOps (r (.GPR 2#5) s)) s = w .PC (smallLeftHeadPC s base) s := by
  by_cases zero : r (.GPR 2#5) s = 0#64
  all_goals
    simp only [smallLeftHeadOps, zero, ↓reduceIte, smallLeftHeadPC,
      block, List.foldl_cons, List.foldl_nil, Op.effect]
    arm_state_nf
  all_goals simp [apply_ite]

theorem small_left_head_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 28#64) (small : r (.GPR 1#5) s = 0#64) :
    Follows base (smallLeftHeadOps (r (.GPR 2#5) s)) s := by
  have hpc : r .PC s = base + 28#64 := hp
  by_cases zero : r (.GPR 2#5) s = 0#64
  all_goals
    simp only [smallLeftHeadOps, zero, ↓reduceIte, Follows, Op.row, Op.effect]
    arm_state_nf
  all_goals simp [small, zero, hpc]

theorem small_left_head (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64) (small : r (.GPR 1#5) s = 0#64) :
    let t := block base (smallLeftHeadOps (r (.GPR 2#5) s)) s
    run (smallLeftHeadOps (r (.GPR 2#5) s)).length s = t ∧ ScanFrame s t ∧
      read_pc t = smallLeftHeadPC s base := by
  refine ⟨block_run base (smallLeftHeadOps (r (.GPR 2#5) s)) s hc he ha
      (small_left_head_follows s base hp small),
    scan_pure_frame base (smallLeftHeadOps (r (.GPR 2#5) s)) s (by
      by_cases zero : r (.GPR 2#5) s = 0#64 <;>
        simp only [smallLeftHeadOps, zero, ↓reduceIte] <;> decide), ?_⟩
  rw [small_left_head_state]
  arm_state_nf

def smallLeftFinishOps (zero : Bool) : List Op :=
  if zero then [.p152, .p156] else [.p112, .p116, .p120]

theorem small_left_finish_follows (s : ArmState) (base : BitVec 64) (zero : Bool)
    (hp : read_pc s = base + (if zero then 152#64 else 112#64)) :
    Follows base (smallLeftFinishOps zero) s := by
  have hpc : r .PC s = base + (if zero then 152#64 else 112#64) := hp
  cases zero
  all_goals
    simp only [smallLeftFinishOps, Bool.false_eq_true, ↓reduceIte,
      Follows, Op.row, Op.effect, put, next]
    arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

theorem small_left_finish_values (s : ArmState) (base : BitVec 64) (zero : Bool)
    (hp : read_pc s = base + (if zero then 152#64 else 112#64)) :
    let t := block base (smallLeftFinishOps zero) s
    r (.GPR 21#5) t = (if zero then 0#64 else 1#64) ∧
    r (.GPR 8#5) t = (if zero then 0#64 else r (.GPR 2#5) s) ∧
    read_pc t = base + 160#64 := by
  have hpc : r .PC s = base + (if zero then 152#64 else 112#64) := hp
  cases zero
  all_goals
    simp only [smallLeftFinishOps, Bool.false_eq_true, ↓reduceIte,
      block, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
    arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

def smallRightFinishOps (word : BitVec 64) : List Op :=
  if word = 0#64 then [.p140, .p144] else [.p140]

theorem small_right_finish_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 140#64) :
    Follows base (smallRightFinishOps (r (.GPR 4#5) s)) s := by
  have hpc : r .PC s = base + 140#64 := hp
  by_cases zero : r (.GPR 4#5) s = 0#64
  all_goals
    simp only [smallRightFinishOps, zero, ↓reduceIte, Follows, Op.row, Op.effect]
    arm_state_nf
  all_goals simp [hpc, zero]

theorem small_right_finish_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base (smallRightFinishOps (r (.GPR 4#5) s)) s) =
      base + (if r (.GPR 4#5) s = 0#64 then 264#64 else 228#64) := by
  by_cases zero : r (.GPR 4#5) s = 0#64
  all_goals
    simp only [smallRightFinishOps, zero, ↓reduceIte, block,
      List.foldl_cons, List.foldl_nil, Op.effect]
    arm_state_nf
  all_goals simp [zero]

theorem small_right_finish (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 140#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      read_pc t = base + (if r (.GPR 4#5) s = 0#64 then 264#64 else 228#64) := by
  let ops := smallRightFinishOps (r (.GPR 4#5) s)
  refine ⟨ops.length, block base ops s,
    block_run base ops s hc he ha (small_right_finish_follows s base hp),
    scan_pure_frame base ops s (by
      by_cases zero : r (.GPR 4#5) s = 0#64 <;>
        simp only [ops, smallRightFinishOps, zero, ↓reduceIte] <;> decide),
    small_right_finish_pc s base⟩

theorem small_right_guard_values (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p136] s) =
      base + (if r (.GPR 9#5) s = 0#64 then 264#64 else 140#64) := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect]
  arm_state_nf
  all_goals simp [apply_ite]

end SszArm.NatMul

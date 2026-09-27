import SszArm.NatAddWidth

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def largeLeftRoute (right : BitVec 64) : List Op :=
  [.p64] ++ if right = 0#64 then [.p68, .p96, .p100, .p104] else []

/-- After a nonzero left count, a Small right word enters the immediate-width
classifier and a Large right enters its physical normalization scan. -/
theorem large_left_route (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 64#64)
    (leftNonzero : r (.GPR 9#5) s ≠ 0#64)
    (rightNonzero : r (.GPR 3#5) s = 0#64 → r (.GPR 4#5) s ≠ 0#64) :
    let ops := largeLeftRoute (r (.GPR 3#5) s)
    let t := block base ops s
    run ops.length s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      read_pc t = base + (if r (.GPR 3#5) s = 0#64 then 108#64 else 300#64) := by
  have hpc : r .PC s = base + 64#64 := hp
  have follows : Follows base (largeLeftRoute (r (.GPR 3#5) s)) s := by
    by_cases small : r (.GPR 3#5) s = 0#64 <;>
      simp_all [largeLeftRoute, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follows, ?_, ?_, ?_, ?_⟩
  · constructor
    · by_cases small : r (.GPR 3#5) s = 0#64 <;>
        simp [largeLeftRoute, small, block, Op.effect, put, next, state_simp_rules]
    · by_cases small : r (.GPR 3#5) s = 0#64 <;>
        simp [largeLeftRoute, small, block, Op.effect, put, next, state_simp_rules]
    · intro reg outside
      by_cases three : reg = 3#5
      · subst reg
        by_cases small : r (.GPR 3#5) s = 0#64 <;>
          simp [largeLeftRoute, small, block, Op.effect, put, next, state_simp_rules]
      · by_cases small : r (.GPR 3#5) s = 0#64 <;>
          simp [largeLeftRoute, small, block, Op.effect, put, next, three, state_simp_rules]
    · intro reg
      by_cases small : r (.GPR 3#5) s = 0#64 <;>
        simp [largeLeftRoute, small, block, Op.effect, put, next, state_simp_rules]
    · intro address outside
      by_cases small : r (.GPR 3#5) s = 0#64 <;>
        simp [largeLeftRoute, small, block, Op.effect, put, next, state_simp_rules]
  all_goals
    by_cases small : r (.GPR 3#5) s = 0#64 <;>
      simp_all [largeLeftRoute, block, Op.effect, put, next, state_simp_rules]

/-- Both nonzero Small operands bypass the borrowed scans and width classifier. -/
theorem immediate_start (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base)
    (leftSmall : r (.GPR 1#5) s = 0#64) (rightSmall : r (.GPR 3#5) s = 0#64)
    (leftNonzero : r (.GPR 2#5) s ≠ 0#64) (rightNonzero : r (.GPR 4#5) s ≠ 0#64) :
    let t := block base [.p0, .p72, .p76, .p540] s
    run 4 s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧ read_pc t = base + 544#64 := by
  have hpc : r .PC s = base := hp
  have follows : Follows base [.p0, .p72, .p76, .p540] s := by
    simp [Follows, Op.row, Op.effect, state_simp_rules,
      hpc, leftSmall, rightSmall, leftNonzero, rightNonzero]
  refine ⟨block_run base _ s hc he ha follows, ?_, ?_, ?_⟩
  · constructor
    · simp [block, Op.effect, state_simp_rules]
    · simp [block, Op.effect, state_simp_rules]
    · intro reg outside; simp [block, Op.effect, state_simp_rules]
    · intro reg; simp [block, Op.effect, state_simp_rules]
    · intro address outside; simp [block, Op.effect, state_simp_rules]
  · simp [block, Op.effect, state_simp_rules]
  · simp [block, Op.effect, state_simp_rules, rightNonzero]

end SszArm.NatAdd

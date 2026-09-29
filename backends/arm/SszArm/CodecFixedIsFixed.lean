import SszArm.CodecFixedBodyImmediate
import SszArm.CodecFixedVector
import SszArm.CodecFixedContainer
import SszCodecTypesProofs

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

/-- Structural induction is over checked raw descriptor nesting. Recursive
machine calls occur only for a strict field child; optimized vector traversal
also descends strictly, but retains its caller's activation. -/
theorem body_correct (desc : Desc) : BodyCorrect desc := by
  apply Desc.inductionOnChildren (motive := BodyCorrect) _ desc
  intro parent induction
  cases parent with
  | primitive shape => exact immediate_body_correct (.primitive shape) True.intro
  | vector child count =>
    exact vector_body_correct child count (induction child (by simp [Desc.children]))
  | list child count => exact immediate_body_correct (.list child count) True.intro
  | progressiveList child limit => exact immediate_body_correct (.progressiveList child limit) True.intro
  | compatibleUnion variants => exact immediate_body_correct (.compatibleUnion variants) True.intro
  | container fields =>
    apply container_body_correct false [] fields
    intro field member
    exact induction field.2 (by
      exact List.mem_map.mpr ⟨field, member, rfl⟩)
  | progressiveContainer active fields =>
    apply container_body_correct true active fields
    intro field member
    exact induction field.2 (by
      exact List.mem_map.mpr ⟨field, member, rfl⟩)

/-- Actual linked original-entry-to-RET classification for every finite raw
Codec.Desc. No fixed-size success, schema validity, metadata cap, future helper
execution, or successful branch outcome occurs in the initial contract. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (desc : Desc)
    (owned : Owned s desc) (code : Linked.IsFixed.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel final, run fuel s = final ∧ Post s final desc :=
  entry_of_body desc (body_correct desc) s base owned (linked_code s base code) error aligned pc

theorem program_refines (s : ArmState) (base : BitVec 64) (desc : Desc)
    (owned : Owned s desc) (code : Linked.IsFixed.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel final, run fuel s = final ∧ Post s final desc ∧
      r (.GPR 0#5) final = if desc.erase.fixedSize.isSome then 1#64 else 0#64 := by
  obtain ⟨fuel, final, executed, post⟩ := program_correct s base desc owned code error aligned pc
  exact ⟨fuel, final, executed, post, post.refines⟩

end SszArm.Codec.Fixed.IsFixed

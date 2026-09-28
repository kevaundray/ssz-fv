import SszArm.BitVectorEntry
import SszArm.BitVectorMemcpy
import SszArm.BitVectorStages

namespace SszArm.BitVector

/-- Live callee-saved body arguments, distinct from the caller activation saved
at SP+272. X19 is intentionally absent: the rounding status later overwrites it. -/
structure Working (s t : ArmState) (length : SszNative.NatOperand) : Prop where
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  output : r (.GPR 23#5) t = r (.GPR 0#5) s
  input : r (.GPR 24#5) t = r (.GPR 2#5) s
  size : r (.GPR 20#5) t = r (.GPR 3#5) s
  pointer : r (.GPR 21#5) t = length.pointer
  payload : r (.GPR 22#5) t = length.payload
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

theorem working_division_entry (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data)
    (error : read_err s = .None) : Working s (divisionEntry s base) length := by
  have args := division_arguments s base length data owned
  refine ⟨?_, args.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa (config := {decide := true})
      [divisionEntry, called, Entry.result, state_simp_rules] using error
  · simp (config := {decide := true}) [divisionEntry, called, Entry.result, state_simp_rules]
  · simp (config := {decide := true}) [divisionEntry, called, Entry.result, state_simp_rules]
  · simp (config := {decide := true}) [divisionEntry, called, Entry.result, state_simp_rules]
  · simpa (config := {decide := true})
      [divisionEntry, called, Entry.result, state_simp_rules] using args.pointer
  · simpa (config := {decide := true})
      [divisionEntry, called, Entry.result, state_simp_rules] using args.payload
  · intro reg low high
    simp (config := {decide := true}) [divisionEntry, called, Entry.result, state_simp_rules]

theorem Working.after_return {s c t : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (returned : Delimited.Returned c t) : Working s t length := by
  refine ⟨returned.error, returned.sp.trans current.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (returned.registers 23#5 (by decide) (by decide)).trans current.output
  · exact (returned.registers 24#5 (by decide) (by decide)).trans current.input
  · exact (returned.registers 20#5 (by decide) (by decide)).trans current.size
  · exact (returned.registers 21#5 (by decide) (by decide)).trans current.pointer
  · exact (returned.registers 22#5 (by decide) (by decide)).trans current.payload
  · intro reg low high
    exact (returned.vectors reg low high).trans (current.vectors reg low high)

theorem Working.after_memcpy {s c t : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (site : CallSite) (base : BitVec 64)
    (post : CopyPost site c t base) : Working s t length := by
  refine ⟨post.error, post.sp.trans current.sp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (post.registers 23#5 (by decide) (by decide)).trans current.output
  · exact (post.registers 24#5 (by decide) (by decide)).trans current.input
  · exact (post.registers 20#5 (by decide) (by decide)).trans current.size
  · exact (post.registers 21#5 (by decide) (by decide)).trans current.pointer
  · exact (post.registers 22#5 (by decide) (by decide)).trans current.payload
  · intro reg low high
    have preserved := post.vectors reg (by bv_omega)
    exact (congrArg (fun value : BitVec 128 => value.setWidth 64) preserved).trans
      (current.vectors reg low high)

theorem Working.aligned {s t : ArmState} {length : SszNative.NatOperand}
    (current : Working s t length) (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, current.sp] using aligned

theorem Working.after_preparation {s c : ArmState} {length : SszNative.NatOperand}
    (current : Working s c length) (phase : Stages.CallPreparation) (base : BitVec 64)
    (normal : phase = .round ∨ phase = .scope ∨ phase = .narrow) :
    Working s (phase.result c base) length := by
  rcases normal with rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.error
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.sp
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.output
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.input
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.size
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.pointer
    · simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.payload
    · intro reg low high
      simpa (config := {decide := true})
        [Stages.CallPreparation.result, state_simp_rules] using current.vectors reg low high

end SszArm.BitVector

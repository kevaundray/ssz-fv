import SszArm.MeasurePost

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

theorem allocationWrites_of_unallocated (args : Args) (measured : Outcome NatOperand)
    (unallocated : ∀ call ∈ measured.calls, call.allocation = none) :
    allocationWrites args measured = [] := by
  cases writes : allocationWrites args measured with
  | nil => rfl
  | cons span rest =>
    have member : span ∈ allocationWrites args measured := by rw [writes]; simp
    simp only [allocationWrites, List.mem_flatMap] at member
    obtain ⟨call, callMember, spanMember⟩ := member
    have impossible : False := by
      simpa only [unallocated call callMember, List.not_mem_nil] using spanMember
    exact False.elim impossible

/-- A real attempted constructor call can be Small or fail without committing a
reservation. Such calls stay in the trace; their empty allocation frame still
proves byte-exact preservation of the original arena header and cursor. -/
theorem Produced.of_unallocated {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (owned : Owned s args desc value)
    (unallocated : ∀ call ∈ (outcome s args desc value).calls, call.allocation = none)
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (pc : read_pc t = base + 4116#64) (program : t.program = s.program)
    (error : read_err t = .None) (stack : r (.GPR 31#5) t = args.bodySP)
    (result : ResultAt (widthLoad t) args.result.toNat (outcome s args desc value).result)
    (frame : MemoryFrame (bodyWrites args (outcome s args desc value)) s t)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Produced s t args desc value base := by
  have noWrites := allocationWrites_of_unallocated args (outcome s args desc value) unallocated
  have localFrame : MemoryFrame (localWrites args (outcome s args desc value)) s t := by
    apply frame.weaken
    intro span member
    simp only [bodyWrites, noWrites, List.append_nil, List.mem_append] at member
    rcases member with lowering | output
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr lowering)))
    · exact List.mem_append.mpr (Or.inr output)
  have r0 := Emit.frame_read_offset localFrame args.arena 24 0 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r8 := Emit.frame_read_offset localFrame args.arena 24 8 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r16 := Emit.frame_read_offset localFrame args.arena 24 16 8 owned.arenaBound
    owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨pc, program, error, stack, result, ?_, ⟨r0, r8⟩, ?_, frame, registers, vectors⟩
  · rw [r16, used]
    rfl
  · intro call member reservation allocated
    have impossible : False := by
      simpa only [unallocated call member, reduceCtorEq] using allocated
    exact False.elim impossible

end SszArm.Measure

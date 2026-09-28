import SszArm.MeasureBitsListCountLarge
import SszArm.MeasureBitsScratchProduced
import SszArm.MeasureScanTransition

namespace SszArm.Measure.Bits.List

open SszNative.Serialize (Packed)

theorem count_failure_executes (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.allocateEntry)
    (work : Work s args schema bits)
    (large : (bits.count >>> (64 : Nat)).setWidth 64 ≠ 0#64)
    (failure : (countCall s args bits).result = .error .scratchExhausted) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  have serialized : (SszNative.Serialize.fromWide (arenaOf s args) bits.count).result =
      .error (.arithmetic .scratchExhausted) := by
    change (countCall s args bits).result.mapError _ = _
    simp only [failure, Except.mapError]
  have unchanged := SszNative.Serialize.fromWide_failure_unchanged (arenaOf s args) bits.count
    (.arithmetic .scratchExhausted) serialized
  have allocation : (countCall s args bits).allocation = none := unchanged.2.1
  have measured : outcome s args schema.descriptor (.bits bits) =
      ⟨.error (.arithmetic .scratchExhausted), (countCall s args bits).used, [countCall s args bits]⟩ := by
    rw [list_outcome]
    simp only [SszNative.Serialize.measureList, SszNative.Serialize.bind, serialized]
    simp only [SszNative.Serialize.fromWide, countCall]
  obtain ⟨fuel, u, before, post⟩ := count_large_executes schema s args bits base owned
    code error aligned pc work large
  have memory : u.mem = s.mem := by
    funext address
    apply post.frame address
    simp only [Alloc.writesFor, work.allocator_outcome, allocation, List.not_mem_nil, false_implies,
      forall_const]
  have localFrame : Delimited.MemoryFrame (localWrites args (outcome s args schema.descriptor (.bits bits))) s u :=
    fun address _ => congrFun memory address
  have uOwned := owned.of_local_frame localFrame
  have same : outcome u args schema.descriptor (.bits bits) = outcome s args schema.descriptor (.bits bits) :=
    outcome_eq_of_arena_eq (arenaOf_eq_of_local_frame owned localFrame)
  have uWork := work.after_allocation post
  have uError : read_err u = .None := post.error.trans error
  have uAligned : CheckSPAlignment u := by
    simpa only [CheckSPAlignment, state_simp_rules, post.sp] using aligned
  have uPC : read_pc u = base + 3528#64 := by
    have branch := post.result
    rw [work.allocator_outcome, failure] at branch
    exact branch.2
  have after : run 51 u = Scratch.finalResult u base := Scratch.executes u base
    (code.congr post.program) uError uAligned uPC
  have produced : Produced u (Scratch.finalResult u base) args schema.descriptor (.bits bits) base :=
    Scratch.inline_produced base uOwned uWork.result uWork.stack
      (by simp only [same, measured])
      (by simp only [same, measured, List.length_cons, List.length_nil]; decide)
      (by
        intro call member
        simp only [same, measured, List.mem_singleton] at member
        subst call
        exact allocation)
      (by
        rw [same, measured]
        exact unchanged.1.trans (congrArg SszNative.Delimited.ArenaState.used
          (arenaOf_eq_of_local_frame owned localFrame).symm)) uError
  refine ⟨fuel + 51, Scratch.finalResult u base, by rw [run_plus, before, after], ?_⟩
  apply produced.prepend_stack owned (fun address _ => congrFun memory address) post.program
  · intro reg member
    apply post.registers reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> cases schema <;>
      simp only [Schema.site] <;> decide
  · intro reg low high
    exact congrArg (fun word : BitVec 128 => word.setWidth 64) (post.vectors reg)

end SszArm.Measure.Bits.List

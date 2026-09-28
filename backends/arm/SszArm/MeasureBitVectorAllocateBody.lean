import SszArm.MeasureBitVectorAllocatedScope
import SszArm.MeasureBitVectorFailure

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem allocate_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (arena : r (.GPR 20#5) s = args.arena) (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (mismatch : cap.value ≠ bits.count.toNat) (large : r (.GPR 9#5) s ≠ 0#64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3332#64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  obtain ⟨fuel, u, executed, post⟩ := Bits.Alloc.constructor_executes .scope s base code error aligned
    pc large (Helpers.owned_alloc_input owned arena)
  have callEq := alloc_call_eq s args bits arena low high
  have ue : read_err u = .None := post.error.trans error
  have ua : CheckSPAlignment u := by
    simpa only [CheckSPAlignment, state_simp_rules, post.sp] using aligned
  cases returned : (Bits.Alloc.outcome .scope s).result with
  | ok actual =>
    have next : read_pc u = base + 3416#64 := by
      have info := post.result
      simp only [returned, Bits.Alloc.Site.entry] at info
      exact info.1
    refine ⟨fuel + 30, Scope.result u base, ?_,
      allocated_scope_produced base args cap bits actual owned output stack arena descriptor low high
        mismatch error post returned⟩
    rw [run_plus, executed]
    exact Scope.executes u base (code.congr post.program) ue ua next
  | error reason =>
    have failed : reason = .scratchExhausted ∧ read_pc u = base + 3528#64 := by
      simpa only [returned] using post.result
    have failedNative : (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
        (arenaOf s args).used bits.count).result = .error .scratchExhausted := by
      simpa only [callEq, failed.1] using returned
    have measured := failed_outcome s args cap bits mismatch failedNative
    have calls := mismatch_calls s args cap bits mismatch
    rw [measured] at calls
    have record : SszNative.NatArithmetic.unchanged (arenaOf s args).used (.error .scratchExhausted) =
        SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
          (arenaOf s args).used bits.count := by
      injection calls
    have unallocated : (Bits.Alloc.outcome .scope s).allocation = none := by
      rw [callEq, ← record]
      rfl
    have memory : u.mem = s.mem := by
      funext address
      apply post.frame address
      simp [Bits.Alloc.writesFor, unallocated]
    have localFrame : Delimited.MemoryFrame
        (localWrites args (outcome s args (.bitVector cap) (.bits bits))) s u := by
      intro address outside
      exact congrFun memory address
    have own := owned.of_local_frame localFrame
    have sameArena := arenaOf_eq_of_local_frame owned localFrame
    obtain ⟨extra, t, after, produced⟩ := scratch_body u base args cap bits own
      ((post.registers 19#5 (by decide)).trans output) (post.sp.trans stack)
      (code.congr post.program) ue ua failed.2 mismatch
      (by simpa only [sameArena] using failedNative)
    refine ⟨fuel + extra, t, by rw [run_plus, executed, after],
      Scalar.prepend_pure produced post.program memory ?_ ?_⟩
    · intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact post.registers _ (by decide)
    · intro reg low high
      rw [post.vectors]

end SszArm.Measure.BitVector

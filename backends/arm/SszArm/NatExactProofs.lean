import SszArm.NatExactFinish
import SszArm.NatExactObserve

namespace SszArm.NatExact

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The branch-sensitive frame is stronger than the whole reserved output span. -/
theorem result_local_frame {s t : ArmState} (expected : SszNative.NatOperand)
    (frame : MemoryFrame (writesFor s expected) s t) : MemoryFrame (localWrites s) s t := by
  intro a outside
  apply frame a
  intro span member
  simp only [writesFor, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have output := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
    split <;> simp only [Prod.fst, Prod.snd] at * <;> omega
  · exact outside _ (by simp [localWrites])

/-- Recover original representation and every immutable byte from the byte frame. -/
theorem post_of_physical (s t : ArmState) (expected : SszNative.NatOperand)
    (owned : Owned s expected) (returned : Returned s t)
    (result : SszNative.NatNarrow.ExactResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      expected (r (.GPR 2#5) s)) (frame : MemoryFrame (writesFor s expected) s t) :
    Post s t expected := by
  have memory := result_local_frame expected frame
  refine ⟨returned, result, frame,
    NatDivision.operand_preserved memory expected owned.expectedAt.2.2 owned.operandOwned,
    ?_, ?_⟩
  · refine ⟨?_, ?_, NatDivision.operand_at_preserved memory expected
      owned.expectedAt.2.2 owned.operandOwned⟩
    · rw [memory.load _ 8 (by have := owned.expectedBound; omega)
        (by simpa only [Nat.add_zero] using owned.expectedOwned.subspan 0 8 (by decide))]
      exact owned.expectedAt.1
    · rw [memory.load _ 8 (by have := owned.expectedBound; omega)
        (owned.expectedOwned.subspan 8 8 (by decide))]
      exact owned.expectedAt.2.1
  · intro a low high
    exact memory.protected_byte owned.expectedOwned a low high

theorem finish_correct (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (owned : Owned s expected) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (ready : Ready s base expected) :
    ∃ fuel t, run fuel s = t ∧ Post s t expected := by
  cases accepted : SszNative.NatNarrow.runExact expected (r (.GPR 2#5) s) with
  | false =>
    have pc : read_pc s = base + 124#64 := by
      simpa only [Ready, accepted, Bool.false_eq_true, ↓reduceIte] using ready
    refine ⟨39, failureResult s base, failure_run s base owned.returnSpace hc he ha pc,
      post_of_physical s _ expected owned (failure_returned s base he)
        (failure_image s base expected owned accepted) ?_⟩
    simpa only [writesFor, accepted, Bool.false_eq_true, ↓reduceIte, localWrites]
      using failure_frame s base owned.returnSpace
  | true =>
    have selected : read_pc s = base + 272#64 ∧ r (.GPR 8#5) s = 0#64 := by
      simpa only [Ready, accepted, ↓reduceIte] using ready
    exact ⟨2, successResult s base, success_run s base hc he ha selected.1,
      post_of_physical s _ expected owned (success_returned s base he)
        (success_image s base expected owned selected.2 accepted)
        (success_frame s base expected owned accepted)⟩

theorem post_prepend {s u t : ArmState} (expected : SszNative.NatOperand)
    (owned : Owned s expected) (frame : NatNarrow.Frame s u) (post : Post u t expected) :
    Post s t expected := by
  have r0 := frame.registers 0#5 (by decide)
  have r1 := frame.registers 1#5 (by decide)
  have r2 := frame.registers 2#5 (by decide)
  have r30 := frame.registers 30#5 (by decide)
  have writes : writesFor u expected = writesFor s expected := by
    simp only [writesFor, r0, r2, frame.sp]
  have first := frame.memoryFrame (writesFor s expected)
    (by simp [writesFor]) owned.stackBound
  have second : MemoryFrame (writesFor s expected) u t := by
    simpa only [writes] using post.frame
  apply post_of_physical s t expected owned ?_ ?_ (first.trans second)
  · refine ⟨post.returned.pc.trans r30, post.returned.error,
      post.returned.sp.trans frame.sp, ?_, ?_⟩
    · intro reg low high
      apply (post.returned.registers reg low high).trans
      apply frame.registers
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      constructor
      · bv_omega
      · constructor
        · bv_omega
        · constructor
          · bv_omega
          · constructor <;> bv_omega
    · intro reg low high
      rw [post.returned.vectors reg low high, frame.vectors]
  · simpa only [r0, r2] using post.result

/-- Complete actual entry-to-RET refinement, including empty and noncanonical
Large operands. Only the code image and physical ownership are assumptions. -/
theorem exact_correct (s : ArmState) (base : BitVec 64) (expected : SszNative.NatOperand)
    (owned : Owned s expected) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t expected := by
  obtain ⟨fuel, u, execution, frame, ready⟩ := entry_ready s base expected owned hc he ha hp
  obtain ⟨fuel', t, execution', post⟩ := finish_correct u base expected
    (frame_owned owned frame) (frame_code frame hc) (frame.error.trans he) (frame.aligned ha) ready
  exact ⟨fuel + fuel', t, by rw [run_plus, execution, execution'], post_prepend expected owned frame post⟩

end SszArm.NatExact

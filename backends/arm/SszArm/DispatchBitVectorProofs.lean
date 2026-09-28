import SszArm.DispatchBitVectorOwned

namespace SszArm.Dispatch.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- The common epilogue reloads the original LR and every original saved GPR. -/
theorem returned_of_native {s t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (post : SszArm.BitVector.Returned (entered s .bitVector) t) : Returned s t := by
  have low : 368 ≤ (r (.GPR 31#5) s).toNat := by have := owned.stackLow; omega
  refine ⟨?_, post.error, ?_, ?_, ?_⟩
  · rw [post.pc, entered_sp]
    exact entered_saved s .bitVector low 30#5 280 (by decide)
  · rw [post.sp, entered_sp]
    simp only [bodySP]
    bv_omega
  · intro reg offset member
    rw [post.registers reg offset member, entered_sp]
    exact entered_saved s .bitVector low reg offset member
  · intro reg lower upper
    simpa only [entered_vector] using post.vectors reg lower upper

theorem post_of_native {s t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (post : SszArm.BitVector.Post (entered s .bitVector) t length data) : Post s t length data := by
  have bodyFrame : MemoryFrame (bodyWrites s (outcome s length data)) (entered s .bitVector) t := by
    simpa only [entered_bodyWrites owned] using post.frame
  have frame : MemoryFrame (writesFor s (outcome s length data)) s t := by
    intro address outside
    exact (bodyFrame address (fun span member => outside span (List.mem_append_left _ member))).trans
      ((entry_frame owned) address (fun span member => outside span (List.mem_append_right _ member)))
  refine {
    native := post
    returned := returned_of_native owned post.returned
    result := ?_
    written := by simpa only [entered_outcome owned] using post.written
    cursor := by simpa only [entered_arena, entered_outcome owned] using post.cursor
    arenaBase := ?_
    arenaCapacity := ?_
    frame := frame
    operand := NatDivision.operand_preserved frame length owned.descriptor.2.2 owned.operandOwned
    input := ?_
    inputBytes := ?_
    descriptorBytes := ?_ }
  · simpa (config := {decide := true}) only [entered_reg, entered_outcome owned] using post.result
  · have preserved := arena_read owned 0 (by decide)
    simp only [BitVec.add_zero] at preserved
    simpa only [entered_arena, preserved] using post.arenaBase
  · simpa only [entered_arena, arena_read owned 8 (by decide)] using post.arenaCapacity
  · simpa (config := {decide := true}) only [entered_reg] using post.input
  · intro address lower upper
    exact frame.protected_byte owned.inputOwned address lower upper
  · intro address lower upper
    exact frame.protected_byte owned.descriptorOwned address lower upper

/-- Original codec::deserialize PC0, actual save pairs and tag-4 branch tree,
accepted all-path BitVector body and helpers, then the real original-LR RET.
Both complete scratch allocations and every error/cursor/borrow observation are
retained in Post; no future ownership or successful guard is a premise. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (dispatch : Dispatch.CodeAt s base)
    (code : SszArm.BitVector.JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) length data := by
  have entryOwned := dispatch_owned owned
  have bodyPC : read_pc (entered s .bitVector) = base + 428#64 := by
    exact entered_pc s base .bitVector entryOwned pc
  obtain ⟨fuel, post⟩ := SszArm.BitVector.program_correct (entered s .bitVector) base length data
    (body_owned owned) (code.of_program (entered_program s .bitVector))
    (by simpa only [entered_error] using error) (entered_aligned s .bitVector aligned) bodyPC
  refine ⟨Kind.bitVector.steps + fuel, ?_⟩
  rw [run_plus, entry_run s base .bitVector entryOwned dispatch error aligned pc]
  exact post_of_native owned post

/-- Host resource failure remains separate from pinned SSZ decoding. All other
executions expose the exact pinned deserialize result without weakening the
native memory, arbitrary-representation, no-rollback or caller-ABI observations. -/
theorem program_refines (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (dispatch : Dispatch.CodeAt s base)
    (code : SszArm.BitVector.JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) length data ∧
      (SszNative.BitVector.Exhausted length (arenaOf s) →
        SszNative.BitVector.failureAt (widthLoad (run fuel s)) (r (.GPR 0#5) s).toNat .scratchExhausted) ∧
      (¬ SszNative.BitVector.Exhausted length (arenaOf s) →
        SszNative.BitView.ResultAt (widthLoad (run fuel s)) (r (.GPR 0#5) s).toNat
          (Ssz.deserialize (.bitVector length.value) data)) := by
  obtain ⟨fuel, post⟩ := program_correct s base length data owned dispatch code error aligned pc
  refine ⟨fuel, post, ?_⟩
  simpa (config := {decide := true}) only [entered_arenaOf owned, entered_reg] using
    SszArm.BitVector.Post.refines (body_owned owned) post.native

end SszArm.Dispatch.BitVector

import SszArm.NatToU128Entry
import SszArm.NatToU128Observe

namespace SszArm.NatToU128

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- A discriminant-only None frame is stronger than the common physical
ownership envelope; it still protects the original complete limb array. -/
theorem precise_frame_local {s t : ArmState} (operand : SszNative.NatOperand)
    (frame : MemoryFrame (writesFor s operand) s t) :
    MemoryFrame (localWrites s) s t := by
  intro a outside
  apply frame a
  intro span member
  simp only [writesFor, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have out := outside ((r (.GPR 0#5) s).toNat, 32) (by simp [localWrites])
    simp only [Prod.fst, Prod.snd] at out ⊢
    split <;> omega
  · exact outside _ (by simp [localWrites])

theorem returned_of_frame {s u t : ArmState} (frame : NatNarrow.Frame s u)
    (returned : Returned u t) : Returned s t := by
  refine ⟨returned.pc.trans (frame.registers _ (by decide)), returned.error,
    returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor
    · bv_omega
    constructor <;> bv_omega
  · intro reg low high
    rw [returned.vectors reg low high, frame.vectors]

/-- Complete refinement of the frozen ARM leaf, including empty Large and
arbitrary high-zero-padded Large inputs. None preserves all sixteen payload
bytes; every path restores SP and returns through the original link register. -/
theorem to_u128_correct (s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand := by
  obtain ⟨fuel, u, path, hu, frame, up, result⟩ := entry_ready s base operand owned hc he ha
    (by simpa only [entry, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hp)
  let t := finished path base u
  have space := owned.finishSpace.of_frame frame
  have ht : run path.ops.length u = t := finish_run path u base (frame_code frame hc)
    (frame.error.trans he) (frame.aligned ha) up
  have output := frame.registers 0#5 (by decide)
  have spans : finishWrites path u = writesFor s operand := by
    rw [writesFor, result]
    cases path <;>
      simp [finishWrites, FinishPath.bytes, FinishPath.value, output, frame.sp]
  have before : MemoryFrame (writesFor s operand) s u := frame.memoryFrame _
    (by simp [writesFor]) owned.stackBound
  have after : MemoryFrame (writesFor s operand) u t := by
    rw [← spans]
    exact finish_frame path u base space
  have precise := before.trans after
  refine ⟨fuel + path.ops.length, t, ?_, ?_⟩
  · rw [run_plus, hu, ht]
  · refine ⟨returned_of_frame frame (finish_returned path u base (frame.error.trans he)),
      ?_, precise, ?_⟩
    · rw [result, ← output]
      exact finish_result path u base space
    · exact NatDivision.operand_preserved (precise_frame_local operand precise)
        operand owned.operandAt owned.operandOwned

end SszArm.NatToU128

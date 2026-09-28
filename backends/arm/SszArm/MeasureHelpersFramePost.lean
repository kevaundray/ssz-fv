import SszArm.MeasureHelpersFrameBasics

namespace SszArm.Measure.Helpers.ConstructorFrame

open UintCodec (widthLoad)
open Delimited (MemoryFrame)
open NatFromU128

/-- Retain the full accepted constructor Post while exposing the concrete
selected final state needed for the enclosing function's additional ABI frame. -/
theorem selected_post {s u : ArmState} (body : Body) (owned : NatFromU128.Owned s)
    (reached : Checkpoint s u) (selected : Selected s u body) (error : read_err s = .None) :
    NatFromU128.Post s (body.final u) := by
  have output := reached.frame.registers 0#5 (by decide)
  have low := reached.frame.registers 2#5 (by decide)
  have high := reached.frame.registers 3#5 (by decide)
  have header := reached.frame.registers 4#5 (by decide)
  have space := reached.frame.space owned.toSpace
  have returned := checkpoint_returned reached body error
  cases body
  · have model := outcome_small s selected
    have frame : MemoryFrame (NatFromU128.successWrites s) s (Body.small.final u) := by
      apply checkpoint_frame reached
      simpa only [NatFromU128.successWrites, output, reached.frame.sp] using small_frame u space
    have localFrame := success_frame_local frame
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [SszNative.NatArithmetic.unchanged, output, low] using small_result u space
    · rw [model]
      exact congrArg BitVec.toNat (local_header owned localFrame 16 (by decide))
    · exact ⟨by simpa using local_header owned localFrame 0 (by decide),
        local_header owned localFrame 8 (by decide)⟩
    · simpa only [NatFromU128.writesFor, model, SszNative.NatArithmetic.unchanged,
        List.append_nil] using frame
    · intro reservation allocated
      simp only [model, SszNative.NatArithmetic.unchanged] at allocated
      contradiction
  · have model := outcome_failure s selected.1 selected.2
    have frame : MemoryFrame (NatFromU128.localWrites s) s (Body.failure.final u) := by
      apply checkpoint_frame reached
      simpa only [NatFromU128.localWrites, output, reached.frame.sp] using failure_frame u space
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [SszNative.NatArithmetic.unchanged, output] using failure_result u space
    · rw [model]
      exact congrArg BitVec.toNat (local_header owned frame 16 (by decide))
    · exact ⟨by simpa using local_header owned frame 0 (by decide),
        local_header owned frame 8 (by decide)⟩
    · simpa only [NatFromU128.writesFor, model, SszNative.NatArithmetic.unchanged,
        List.append_nil] using frame
    · intro reservation allocated
      simp only [model, SszNative.NatArithmetic.unchanged] at allocated
      contradiction
  · obtain ⟨geometry, pointerNat⟩ := owned.wideSpace reached selected
    rcases selected with ⟨large, checks, address, first, last⟩
    have model := outcome_wide s large checks
    have pointerWord : pointer u = BitVec.ofNat 64 ((addressWord s).toNat +
        SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat) := by
      rw [← pointerNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have result := wide_result u geometry
    have immutable := wide_header u geometry
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [output, low, high, pointerWord] using result
    · rw [model, ← header, wide_cursor u geometry]
      exact last
    · constructor
      · rw [← header, immutable.1]
        simpa only [BitVec.add_zero] using reached.header 0#64
      · rw [← header, immutable.2]
        exact reached.header 8#64
    · apply checkpoint_frame reached
      simpa only [NatFromU128.writesFor, model, wideWrites, NatFromU128.successWrites,
        output, header, reached.frame.sp, pointerNat] using wide_frame u geometry
    · intro reservation allocated
      rw [model] at allocated ⊢
      cases allocated
      simpa only [pointerWord, low, high] using result.1.2.2

/-- The original helper entry supplies the selected state. Program and x18
preservation come from its real checkpoint/body, not from an assumed callback. -/
theorem correct (s : ArmState) (base : BitVec 64)
    (code : NatFromU128.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) (owned : NatFromU128.Owned s) :
    ∃ fuel t, run fuel s = t ∧ NatFromU128.Post s t ∧
      t.program = s.program ∧ r (.GPR 18#5) t = r (.GPR 18#5) s := by
  obtain ⟨fuel, u, body, runs, reached, selected⟩ :=
    entry_runs s base code error aligned pc owned.toSpace
  refine ⟨fuel, body.final u, runs, selected_post body owned reached selected error,
    (body_program body u).trans reached.frame.program, ?_⟩
  rw [body_registers body u 18#5 (by decide), reached.frame.registers 18#5 (by decide)]

end SszArm.Measure.Helpers.ConstructorFrame

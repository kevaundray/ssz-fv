import SszArm.CodecFixedGate

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

/-- Entry/stack ownership is derived before applying structural body induction.
This composition lemma is internal to the proof; public roots discharge its
body argument using Desc.inductionOnChildren. -/
theorem entry_of_body (desc : Desc) (body : BodyCorrect desc)
    (s : ArmState) (base : BitVec 64) (owned : Owned s desc) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel final, run fuel s = final ∧ Post s final desc := by
  let p := prologue s
  let q := block gateOps p
  have low : 32 ≤ (r (.GPR 31#5) s).toNat :=
    (isFixedStack_activation desc).trans owned.stack
  have pFrame : Delimited.MemoryFrame (writes s desc) s p := by
    apply (Stack.caller_cover owned.stack (isFixedStack_activation desc)).frame
    exact prologue_frame s low
  have pCode : CodeAt p base := by simpa only [CodeAt, p, prologue_program] using code
  have pError : read_err p = .None := (prologue_error s).trans error
  have pAligned : CheckSPAlignment p := prologue_aligned s aligned
  have pPC : read_pc p = base + 12#64 := by simp only [p, prologue_pc, pc]
  have pDescriptor := Storage.desc_preserved owned.descriptor pFrame
  have pTag : read_mem_bytes 8 (r (.GPR 0#5) p) p = tagWord desc.tag := by
    rw [show r (.GPR 0#5) p = r (.GPR 0#5) s from prologue_register s 0#5 (by decide)]
    exact desc_tag p (r (.GPR 0#5) s) desc pDescriptor.at
  have qFrame : Delimited.MemoryFrame (writes s desc) p q := by
    intro address outside
    rw [show q.mem = p.mem from gate_memory p]
  have qDescriptor := Storage.desc_preserved pDescriptor qFrame
  have qOwned : BodyOwned s q desc := by
    refine ⟨owned.stack, (prologue_context s low).gate, ?_⟩
    rw [show r (.GPR 0#5) q = r (.GPR 0#5) s from
      (gate_register p 0#5 (by decide)).trans (prologue_register s 0#5 (by decide))]
    exact qDescriptor
  have qCode : CodeAt q base := by simpa only [CodeAt, q, block_program] using pCode
  have qError : read_err q = .None := (block_error _ p).trans pError
  have qAligned : CheckSPAlignment q := block_aligned _ p pAligned
  have qPC : read_pc q = base + selectedEntry desc.tag := gate_pc p base desc.tag pPC pTag
  have qTag : r (.GPR 8#5) q = tagWord desc.tag := gate_tag p desc.tag pTag
  obtain ⟨fuel, final, executed, post⟩ := body s q base qOwned qCode qError qAligned qPC qTag
  refine ⟨3 + 3 + fuel, final, ?_, ?_⟩
  · rw [run_plus, run_plus, prologue_run s base code error aligned pc,
      gate_run p base pCode pError pAligned pPC, executed]
  · apply post.to_post
    · simp only [q, block_program, p, prologue_program]
    · exact pFrame.trans qFrame

end SszArm.Codec.Fixed.IsFixed

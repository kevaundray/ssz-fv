import SszArm.CodecFixedObservations

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

/-- Original-entry-to-RET execution for every immediate classification branch.
This includes wrong/huge primitive metadata and all three variable composite
constructors; no contents are read beyond the descriptor's active tag. -/
theorem immediate_correct (s : ArmState) (base : BitVec 64) (desc : Desc)
    (immediate : Immediate desc) (owned : Owned s desc) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t desc := by
  let p := prologue s
  let d := block (dispatchOps desc.tag) p
  let result := SszNative.FixedSize.isFixed desc
  let t := finish d result
  have low : 32 ≤ (r (.GPR 31#5) s).toNat :=
    (isFixedStack_activation desc).trans owned.stack
  have pRun : run 3 s = p := prologue_run s base code error aligned pc
  have pCode : CodeAt p base := by simpa only [CodeAt, p, prologue_program] using code
  have pError : read_err p = .None := (prologue_error s).trans error
  have pAligned : CheckSPAlignment p := prologue_aligned s aligned
  have pPC : read_pc p = base + 12#64 := by simp only [p, prologue_pc, pc]
  have pFrame : Delimited.MemoryFrame (writes s desc) s p := by
    simpa only [writes, immediate_stack desc immediate] using prologue_frame s low
  have pInput := Storage.desc_preserved owned.descriptor pFrame
  have pTag : read_mem_bytes 8 (r (.GPR 0#5) p) p = tagWord desc.tag := by
    rw [show r (.GPR 0#5) p = r (.GPR 0#5) s from prologue_register s 0#5 (by decide)]
    exact desc_tag p (r (.GPR 0#5) s) desc pInput.at
  have dRun : run (dispatchOps desc.tag).length p = d :=
    dispatch_run p base desc.tag pCode pError pAligned pPC pTag
  have dPC : read_pc d = base + if result then 188#64 else 172#64 := by
    rw [show read_pc d = base + dispatchTarget desc.tag from dispatch_pc p base desc.tag pPC pTag]
    rw [immediate_target desc immediate]
  have dCode : CodeAt d base := by simpa only [CodeAt, d, block_program] using pCode
  have dError : read_err d = .None := (block_error _ p).trans pError
  have dAligned : CheckSPAlignment d := block_aligned _ p pAligned
  have tRun : run 4 d = t := finish_run d base result dCode dError dAligned dPC
  have saved := (prologue_saved s low).dispatch desc.tag
  have returned := finish_saved s d result saved
  refine ⟨3 + (dispatchOps desc.tag).length + 4, t, ?_, ?_⟩
  · rw [run_plus, run_plus, pRun, dRun, tRun]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨returned.1, ?_, returned.2.1, ?_, ?_⟩
      · exact (block_error _ d).trans dError
      · intro reg lower upper
        by_cases h19 : reg = 19#5
        · subst reg
          exact returned.2.2.2.2
        by_cases h20 : reg = 20#5
        · subst reg
          exact returned.2.2.2.1
        by_cases h30 : reg = 30#5
        · subst reg
          exact returned.2.2.1
        have h0 : reg ≠ 0#5 := by bv_omega
        have h8 : reg ≠ 8#5 := by bv_omega
        have h31 : reg ≠ 31#5 := by bv_omega
        exact (finish_register d result reg ⟨h0, h19, h20, h30, h31⟩).trans
          ((dispatch_register p desc.tag reg h8).trans (prologue_register s reg h31))
      · intro reg lower upper
        simp only [t, finish, block_vector, d, p, prologue]
        rw [block_vector]
    · exact (finish_register d result 18#5 (by decide)).trans
        ((dispatch_register p desc.tag 18#5 (by decide)).trans
          (prologue_register s 18#5 (by decide)))
    · simp only [t, finish, block_program, d, p, prologue_program]
    · exact finish_result d result
    · intro address outside
      change (finish d result).mem address = s.mem address
      rw [finish_memory, show d.mem = p.mem from dispatch_memory p desc.tag]
      exact pFrame address outside

end SszArm.Codec.Fixed.IsFixed

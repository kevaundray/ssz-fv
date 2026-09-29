import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

theorem immediate_body_correct (desc : Desc) (immediate : Immediate desc) : BodyCorrect desc := by
  intro source current base owned code error aligned pc loaded
  let d := block (selectedOps desc.tag) current
  let result := SszNative.FixedSize.isFixed desc
  let final := finish d result
  have dRun : run (selectedOps desc.tag).length current = d :=
    selected_run current base desc.tag code error aligned pc loaded
  have dPC : read_pc d = base + if result then 188#64 else 172#64 := by
    rw [show read_pc d = base + dispatchTarget desc.tag from selected_pc current base desc.tag pc loaded]
    rw [immediate_target desc immediate]
  have dCode : CodeAt d base := by simpa only [CodeAt, d, block_program] using code
  have dError : read_err d = .None := (block_error _ current).trans error
  have dAligned : CheckSPAlignment d := block_aligned _ current aligned
  have finalRun : run 4 d = final := finish_run d base result dCode dError dAligned dPC
  have context := owned.context.selected desc.tag
  have restored := finish_saved source d result context.saved
  refine ⟨(selectedOps desc.tag).length + 4, final, ?_, ?_⟩
  · rw [run_plus, dRun, finalRun]
  · refine ⟨?_, ?_, ?_, finish_result d result, ?_⟩
    · refine ⟨restored.1, ?_, restored.2.1, ?_, ?_⟩
      · simpa only [final, finish, block_error] using dError
      · intro reg lower upper
        by_cases h19 : reg = 19#5
        · subst reg
          exact restored.2.2.2.2
        by_cases h20 : reg = 20#5
        · subst reg
          exact restored.2.2.2.1
        by_cases h30 : reg = 30#5
        · subst reg
          exact restored.2.2.1
        exact (finish_register d result reg ⟨by bv_omega, h19, h20, h30, by bv_omega⟩).trans
          (context.registers reg (by omega) upper h19 h20 h30)
      · intro reg lower upper
        rw [show (r (.SFP reg) final).setWidth 64 = (r (.SFP reg) d).setWidth 64 by
          simp only [final, finish, block_vector]]
        exact context.vectors reg lower upper
    · exact (finish_register d result 18#5 (by decide)).trans
        (context.registers 18#5 (by decide) (by decide) (by decide) (by decide) (by decide))
    · simp only [final, finish, block_program, d]
    · intro address outside
      change (finish d result).mem address = current.mem address
      rw [finish_memory, show d.mem = current.mem from selected_memory current desc.tag]

end SszArm.Codec.Fixed.IsFixed

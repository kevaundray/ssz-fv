import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)

theorem finish_body (source current : ArmState) (base : BitVec 64) (desc : Desc)
    (context : BodyContext source current) (code : CodeAt current base)
    (error : read_err current = .None) (aligned : CheckSPAlignment current)
    (pc : read_pc current = base + if SszNative.FixedSize.isFixed desc then 188#64 else 172#64) :
    ∃ final, run 4 current = final ∧ BodyPost source current final desc := by
  let result := SszNative.FixedSize.isFixed desc
  let final := finish current result
  have restored := finish_saved source current result context.saved
  refine ⟨final, finish_run current base result code error aligned pc, ?_⟩
  refine ⟨?_, ?_, ?_, finish_result current result, ?_⟩
  · refine ⟨restored.1, ?_, restored.2.1, ?_, ?_⟩
    · simpa only [final, finish, block_error] using error
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
      exact (finish_register current result reg ⟨by bv_omega, h19, h20, h30, by bv_omega⟩).trans
        (context.registers reg (by omega) upper h19 h20 h30)
    · intro reg lower upper
      rw [show (r (.SFP reg) final).setWidth 64 = (r (.SFP reg) current).setWidth 64 by
        simp only [final, finish, block_vector]]
      exact context.vectors reg lower upper
  · exact (finish_register current result 18#5 (by decide)).trans
      (context.registers 18#5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp only [final, finish, block_program]
  · intro address outside
    change (finish current result).mem address = current.mem address
    rw [finish_memory]

end SszArm.Codec.Fixed.IsFixed

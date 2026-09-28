import SszArm.NatMulZeroFrame

namespace SszArm.NatMul

/-- Original main entry through its original RET when either significant count
is zero. Empty Large and arbitrarily high-zero-padded raw operands are scanned
by the real entry path; the result image comes from the executed zero stores. -/
theorem zero_run (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 entry)
    (zero : left.wordCount = 0 ∨ right.wordCount = 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  obtain ⟨fuel, u, execution, frame, exit, _, _⟩ :=
    entry_dispatch s base left right owned code.body error aligned pc
  have rawZero : SszNative.Limbs.sigWords left.words = 0 ∨
      SszNative.Limbs.sigWords right.words = 0 := zero
  simp only [DispatchExit, rawZero, ↓reduceIte] at exit
  have space : ReturnSpace u (r (.GPR 0#5) u) := by
    rw [frame.output]
    exact ReturnSpace.of_owned owned frame.saved
  obtain ⟨finish, returned, image, memory⟩ := zero_return_run s u base
    (frame.code code.body) (frame.error.trans error) (frame.aligned aligned)
    exit.1 frame.saved space
  have totalFrame := (frame.memoryFor (outcome s left right)).trans
    ((zero_return_covered owned frame zero).frame memory)
  refine ⟨fuel + 28, zeroReturned u base, ?_, ?_⟩
  · rw [run_plus, execution, finish]
  · exact zero_post s (zeroReturned u base) left right owned zero returned
      (by simpa only [frame.output] using image) totalFrame

end SszArm.NatMul

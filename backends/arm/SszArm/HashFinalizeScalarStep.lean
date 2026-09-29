import SszArm.HashFinalizeBlocks

namespace SszArm.Hash.Finalize

structure ScalarFrame (changed : List (BitVec 5)) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ changed → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

structure ScalarStep (changed : List (BitVec 5)) (s t : ArmState) : Prop where
  frame : ScalarFrame changed s t
  aligned : CheckSPAlignment t

theorem ScalarFrame.refl (changed : List (BitVec 5)) (s : ArmState) :
    ScalarFrame changed s s := ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem ScalarFrame.trans {changed : List (BitVec 5)} {s t u : ArmState}
    (first : ScalarFrame changed s t) (second : ScalarFrame changed t u) :
    ScalarFrame changed s u :=
  ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
    fun reg => (second.vectors reg).trans (first.vectors reg)⟩

theorem ScalarStep.weaken {small large : List (BitVec 5)} {s t : ArmState}
    (step : ScalarStep small s t) (contained : ∀ reg ∈ small, reg ∈ large) :
    ScalarStep large s t := by
  refine ⟨⟨step.frame.program, step.frame.error, ?_, step.frame.vectors⟩, step.aligned⟩
  intro reg outside
  exact step.frame.registers reg (fun member => outside (contained reg member))

theorem scalar_effect (ops : List Op) (changed : List (BitVec 5))
    (s : ArmState) (aligned : CheckSPAlignment s)
    (steps : ∀ op ∈ ops, ∀ t : ArmState, CheckSPAlignment t →
      ScalarStep changed t (op.effect t)) : ScalarStep changed s (effect ops s) := by
  induction ops generalizing s with
  | nil => exact ⟨ScalarFrame.refl changed s, aligned⟩
  | cons op ops ih =>
    have first := steps op List.mem_cons_self s aligned
    have rest := ih (op.effect s) first.aligned
      (fun next member => steps next (List.mem_cons_of_mem op member))
    exact ⟨first.frame.trans rest.frame, rest.aligned⟩

end SszArm.Hash.Finalize

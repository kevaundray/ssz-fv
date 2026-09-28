import SszArm.MeasureBitsReturnedErrorPost

namespace SszArm.Measure.Bits

theorem returned_error_run (n m : Nat) (s p t : ArmState)
    (before : run n s = p) (after : run m p = t) :
    run (n + m) s = t := by
  rw [run_plus, before, after]

end SszArm.Measure.Bits

import SszArm.HashCombineLeft
import SszArm.HashCombineRight
import SszArm.HashCombineFinalize

namespace SszArm.Hash

open Combine

/-- Execution refinement of the linked ARM two-slice wrapper, for arbitrary
physical slice lengths. The finalizer is a theorem dependency; the actual SHA
compression helper is the sole assumed execution boundary. -/
theorem combine_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    ∃ fuel, CombinePost s (run fuel s) left right := by
  obtain ⟨leftFuel, leftDone⟩ := left_correct s base left right code data compression pc error aligned owned
  let afterLeft := run leftFuel s
  let value := (SszNative.HashStream.update SszNative.HashStream.new left).state
  have leftActivation : Activation s afterLeft :=
    ⟨leftDone.error, leftDone.program, leftDone.aligned, leftDone.sp, leftDone.x19,
      leftDone.x24, leftDone.saved, leftDone.frame⟩
  obtain ⟨rightFuel, rightActivation, rightPC, rightState⟩ := right_correct s afterLeft base left right
    value code data compression owned leftActivation
    (by simpa only [value, leftValue] using leftDone.pc)
    (by simpa only [value, leftValue, fillLength] using leftDone.state)
    (by rw [leftDone.x20]; exact owned.rightLength)
    leftDone.x21 (by simpa only [value, leftValue] using leftDone.x22) leftDone.x25
  let afterRight := run rightFuel afterLeft
  obtain ⟨returnFuel, returned⟩ := copy_finalize_return_correct s afterRight base left right
    (SszNative.HashStream.update value right).state
    (rightActivation.code code) (rightActivation.data owned data) compression rightPC
    rightActivation.error rightActivation.aligned owned
    (by simpa only [bodySP] using rightActivation.sp) rightActivation.output rightState
    rightActivation.saved rightActivation.program rightActivation.frame rfl
  refine ⟨leftFuel + rightFuel + returnFuel, ?_⟩
  rw [run_plus, run_plus]
  exact returned

end SszArm.Hash

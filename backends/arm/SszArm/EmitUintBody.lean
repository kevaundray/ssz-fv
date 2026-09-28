import SszArm.EmitUintGuard
import SszArm.EmitUintFinish
import SszArm.EmitUintLoop

namespace SszArm.Emit.Uint

open SszNative (NatOperand)
open UintCodec (widthLoad)

/-- Actual UInt body execution, beginning at the Value.uint guard and ending
before the common success status store. Logical width and physical high-zero
padding remain arbitrary; all branch and lowering ownership facts are derived
from the original Owned observations. -/
theorem body_correct (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 60#64)
    (descriptor : r (.GPR 1#5) s = args.descriptor) (tag : r (.GPR 9#5) s = 1#64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.uint width) (.uint number) size base := by
  obtain ⟨prefixFuel, u, runPrefix, prefixFrame, exit, length⟩ :=
    width_prefix s base args width number size code owned registers error aligned pc descriptor tag
  have ownedU := prefixFrame.owned owned
  have registersU := prefixFrame.bodyRegisters registers
  have codeU := prefixFrame.code code
  have errorU := prefixFrame.error.trans error
  have alignedU := prefixFrame.aligned aligned
  by_cases zero : size = 0
  · have bytes : SszNative.ByteView.BytesAt (widthLoad u) args.output.toNat
        (SszNative.Serialize.emit (.uint width) (.uint number)) := by
      intro index within
      simp only [SszNative.Serialize.emit, SszNative.Limbs.bytes, Array.size_ofFn,
        expected_width owned, zero] at within
      omega
    obtain ⟨runFinish, produced⟩ := result_finish u base args width number size codeU ownedU
      registersU errorU alignedU (by simpa [zero] using exit) length bytes
    refine ⟨prefixFuel + 1, resultFinish u base args size, ?_, prepend_produced prefixFrame produced⟩
    rw [run_plus, runPrefix, runFinish]
  · obtain ⟨loopFuel, v, runLoop, loopFrame, exitV, lengthV, bytesV⟩ :=
      loop_to_result u base args width number size codeU ownedU registersU errorU alignedU
        (by simpa [zero] using exit) length (by omega)
    have frame := prefixFrame.trans loopFrame
    obtain ⟨runFinish, produced⟩ := result_finish v base args width number size (frame.code code)
      (frame.owned owned) (frame.bodyRegisters registers) (frame.error.trans error)
      (frame.aligned aligned) exitV lengthV bytesV
    refine ⟨prefixFuel + loopFuel + 1, resultFinish v base args size, ?_, prepend_produced frame produced⟩
    rw [run_plus, run_plus, runPrefix, runLoop, runFinish]

end SszArm.Emit.Uint

import SszX86.CodecMeasureChildHelpers
import SszX86.CodecIsFixedProofs

namespace SszX86.CodecMeasureChild

/-- The field child is classified by the actual linked recursive is_fixed body,
whose own self-calls are closed by its structural execution theorem. -/
theorem classifier_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (classifierCode : CodecIsFixed.CodeAt e (base + Int64.ofInt isFixedOffset))
    (s : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (bytes : Nat)
    (slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (owned : CodecIsFixed.Owned (callState s (base + 275).toBitVec)
      (base + Int64.ofInt isFixedOffset) readonly desc (base + 275).toBitVec bytes) :
    Eventually (step e) (CodecIsFixed.Post (callState s (base + 275).toBitVec)
      desc (base + 275).toBitVec bytes) (s, base + 270) := by
  apply classifier_call e base code s _ slot
  exact CodecIsFixed.is_fixed_correct e (base + Int64.ofInt isFixedOffset)
    classifierCode (callState s (base + 275).toBitVec) readonly desc
    (base + 275).toBitVec bytes owned

end SszX86.CodecMeasureChild

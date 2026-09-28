import SszX86.MeasureBitsListPost
import SszX86.MeasureOutput

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem first_failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (limit : Option NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (listModel : measure desc (.bits bits) (arenaState address capacity used) =
      measureList limit bits (arenaState address capacity used))
    (large : ¬ bits.count.toNat < 2^64)
    (failed : Arena.reserve address.toNat capacity.toNat used.toNat 2 = none)
    (memory : t.dmem = s.dmem) (sp : t.regs.rsp = s.regs.rsp)
    (outReg : t.regs.rbx = s.regs.rbx) (vectors : t.zmms = s.zmms) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc (.bits bits) buffer address capacity used u.1)
      (t, base + 2963) := by
  have native := NatFromU128.result_model_failure address capacity used bits.count large failed
  change countCall bits address capacity used = _ at native
  have counted : (countCall bits address capacity used).result = .error .scratchExhausted := by
    simp only [native, NatArithmetic.unchanged]
  have model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨.error (.arithmetic .scratchExhausted), used.toNat, [countCall bits address capacity used]⟩ := by
    rw [listModel, list_first_failure limit bits address capacity used .scratchExhausted counted]
    simp only [native, NatArithmetic.unchanged]
  apply scratch_cps e base hc
  · simpa only [OutputMapped, memory, outReg] using owned.resultMapped
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  apply first_scratch_post s _ desc bits buffer address capacity used owned model
  · simp only [native, NatArithmetic.unchanged]
  · simp only [memory, outReg]
  · exact sp
  · exact vectors

end SszX86.Measure.Bits

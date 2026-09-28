import SszX86.MeasureBitsConstructorBody
import SszX86.MeasureBitsArithmetic

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem CountPrefix.restate {s before after : MachineData} {bits : Packed}
    {address capacity used : BitVec 64}
    (resources : CountPrefix s bits address capacity used before)
    (memory : after.dmem = before.dmem)
    (sp : after.regs.rsp = before.regs.rsp)
    (outReg : after.regs.rbx = before.regs.rbx) (vectors : after.zmms = before.zmms) :
    CountPrefix s bits address capacity used after := by
  refine ⟨?_, ?_, ?_, ?_, sp.trans resources.stack, outReg.trans resources.output,
    vectors.trans resources.vectors⟩
  · rw [memory]; exact resources.frame
  · rw [memory]; exact resources.mapping
  · rw [memory]; exact resources.arena
  · rw [memory]; exact resources.calls

theorem list_continue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64)
    (savedLow : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 16) 8 = some ((bits.count.setWidth 64).toNat : Int))
    (savedHeader : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8) 8 = some (s.regs.rcx.toBitVec.toNat : Int)) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc (.bits bits) buffer address capacity used u.1)
      (t, base + 2079) := by
  apply list_count_reload_cps e base hc _ _ _ savedLow
  apply list_divide_cps e base hc
  intro dividedFlags
  apply list_increment_cps e base hc
  intro incrementedFlags
  apply list_constructor_prepare_cps e base hc _ s.regs.rcx.toBitVec
  · exact savedHeader
  apply constructor_body_cps e base hc helpers s _ desc bits buffer address capacity used owned
  · exact resources.restate rfl rfl rfl rfl
  · exact model
  · simp only [UInt64.ofBitVec_toBitVec]
  · change t.regs.rsp.toBitVec + 24#64 = s.regs.rsp.toBitVec + 24
    rw [resources.stack]
    with_unfolding_all rfl
  · simpa only [listIncremented, listDivided, UInt64.toBitVec_ofBitVec, high] using (encoded_words bits.count).1
  · simpa only [listIncremented, listDivided, UInt64.toBitVec_ofBitVec, high] using (encoded_words bits.count).2

theorem progressive_continue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (header : t.regs.rcx = s.regs.rcx)
    (low : t.regs.r15.toBitVec = bits.count.setWidth 64)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc (.bits bits) buffer address capacity used u.1)
      (t, base + 1621) := by
  apply progressive_divide_cps e base hc
  intro dividedFlags
  apply progressive_increment_cps e base hc
  intro incrementedFlags
  apply progressive_constructor_prepare_cps e base hc
  apply constructor_body_cps e base hc helpers s _ desc bits buffer address capacity used owned
  · exact resources.restate rfl rfl rfl rfl
  · exact model
  · exact header
  · change t.regs.rsp.toBitVec + 24#64 = s.regs.rsp.toBitVec + 24
    rw [resources.stack]
    with_unfolding_all rfl
  · simpa only [progressiveIncremented, progressiveDivided, UInt64.toBitVec_ofBitVec, low, high] using (encoded_words bits.count).1
  · simpa only [progressiveIncremented, progressiveDivided, UInt64.toBitVec_ofBitVec, low, high] using (encoded_words bits.count).2

end SszX86.Measure.Bits

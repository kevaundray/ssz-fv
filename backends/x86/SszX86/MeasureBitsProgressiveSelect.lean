import SszX86.MeasureBitsProgressiveBound
import SszX86.MeasureBitsOption

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem progressive_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (limit : Option NatOperand)
    (actual : NatOperand) (bits : Packed) (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList limit) (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (counted : (countCall bits address capacity used).result = .ok actual)
    (actualPointer : t.regs.r13.toBitVec = actual.pointer)
    (actualPayload : t.regs.rsi.toBitVec = actual.payload)
    (selected : t.regs.rax.toBitVec.setWidth 8 &&& 1#8 = if limit.isSome then 1#8 else 0#8)
    (bounded : ∀ cap, limit = some cap → t.regs.rbp.toBitVec = cap.pointer ∧ t.regs.r12.toBitVec = cap.payload)
    (header : t.regs.rcx = s.regs.rcx)
    (low : t.regs.r15.toBitVec = bits.count.setWidth 64)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s (.progressiveBitList limit) (.bits bits)
        buffer address capacity used u.1)
      (t, base + 1520) := by
  apply progressive_option_cps e base hc
  intro flags
  cases limit with
  | none =>
    simp only [selected, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    apply progressive_continue_cps e base hc helpers s {t with status := flags}
      (.progressiveBitList none) bits buffer address capacity used owned
      (resources.restate rfl rfl rfl rfl)
    · exact list_bound_pass none actual bits address capacity used counted (by
        intro cap impossible
        cases impossible)
    · exact header
    · exact low
    · exact high
  | some cap =>
    simp only [selected, Option.isSome_some, ↓reduceIte, show ¬ (1#8) = 0#8 by decide]
    exact progressive_bound_cps e base hc helpers s _ cap actual bits buffer address capacity used
      owned (resources.restate rfl rfl rfl rfl) counted actualPointer actualPayload
      (bounded cap rfl).1 (bounded cap rfl).2 header low high

end SszX86.Measure.Bits

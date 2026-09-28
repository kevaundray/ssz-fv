import SszX86.MeasureBitsEntry
import SszX86.MeasureFinish

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize

private theorem wrong_tag (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (mismatch : valueTag value ≠ 3) : s.regs.rax.toBitVec.setWidth 8 ≠ 3#8 := by
  rw [owned.tag]
  cases value <;> simp_all [valueTag, Emit.valueTag]

private theorem vector_wrong_model (length : NatOperand) (value : Value)
    (arena : Delimited.ArenaState) (mismatch : valueTag value ≠ 3) :
    measure (.bitVector length) value arena = unchanged arena.used (.error .wrongType) := by
  cases value <;> simp_all [valueTag, Emit.valueTag, Serialize.measure]

private theorem list_wrong_model (limit : NatOperand) (value : Value)
    (arena : Delimited.ArenaState) (mismatch : valueTag value ≠ 3) :
    measure (.bitList limit) value arena = unchanged arena.used (.error .wrongType) := by
  cases value <;> simp_all [valueTag, Emit.valueTag, Serialize.measure]

private theorem progressive_wrong_model (limit : Option NatOperand) (value : Value)
    (arena : Delimited.ArenaState) (mismatch : valueTag value ≠ 3) :
    measure (.progressiveBitList limit) value arena = unchanged arena.used (.error .wrongType) := by
  cases value <;> simp_all [valueTag, Emit.valueTag, Serialize.measure]

theorem vector_wrong_type (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector length) value buffer address capacity used)
    (mismatch : valueTag value ≠ 3) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.bitVector length) value buffer address capacity used t.1)
      (s, base + 82) := by
  apply vector_tag_cps e base hc
  intro flags
  rw [ite_eq_right (wrong_tag s _ value buffer address capacity used owned mismatch)]
  exact wrong_type_body_cps e base hc s _ _ value buffer address capacity used owned
    (vector_wrong_model length value _ mismatch) rfl rfl rfl rfl

theorem list_wrong_type (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limit : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitList limit) value buffer address capacity used)
    (mismatch : valueTag value ≠ 3) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.bitList limit) value buffer address capacity used t.1)
      (s, base + 879) := by
  apply list_tag_cps e base hc
  intro flags
  rw [ite_eq_right (wrong_tag s _ value buffer address capacity used owned mismatch)]
  exact wrong_type_body_cps e base hc s _ _ value buffer address capacity used owned
    (list_wrong_model limit value _ mismatch) rfl rfl rfl rfl

theorem progressive_wrong_type (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limit : Option NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList limit) value buffer address capacity used)
    (mismatch : valueTag value ≠ 3) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.progressiveBitList limit) value buffer address capacity used t.1)
      (s, base + 929) := by
  apply progressive_tag_cps e base hc
  intro flags
  rw [ite_eq_right (wrong_tag s _ value buffer address capacity used owned mismatch)]
  exact wrong_type_body_cps e base hc s _ _ value buffer address capacity used owned
    (progressive_wrong_model limit value _ mismatch) rfl rfl rfl rfl

end SszX86.Measure.Bits

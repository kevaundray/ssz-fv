import SszX86.CodecMeasureFixedArithmeticCall
import SszX86.NatAddProofs

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Field accumulation executes the complete linked checked addition. -/
theorem add196_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt (-64672)))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatAdd.Owned (arithmeticCallState s (base + 201).toBitVec)
      left right address capacity used (base + 201).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatAdd.Post (arithmeticCallState s (base + 201).toBitVec)
      left right address capacity used (base + 201).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 196) := by
  apply call196 e base hc s P hmap
  exact eventually_trans (step e)
    (NatAdd.Post (arithmeticCallState s (base + 201).toBitVec)
      left right address capacity used (base + 201).toBitVec) P _
    (NatAdd.add_correct e (base + Int64.ofInt (-64672)) addCode
      (arithmeticCallState s (base + 201).toBitVec) left right address capacity used
      (base + 201).toBitVec owned) next

/-- Bit-vector rounding executes the same helper at its distinct return site. -/
theorem add555_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt (-64672)))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatAdd.Owned (arithmeticCallState s (base + 560).toBitVec)
      left right address capacity used (base + 560).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatAdd.Post (arithmeticCallState s (base + 560).toBitVec)
      left right address capacity used (base + 560).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 555) := by
  apply call555 e base hc s P hmap
  exact eventually_trans (step e)
    (NatAdd.Post (arithmeticCallState s (base + 560).toBitVec)
      left right address capacity used (base + 560).toBitVec) P _
    (NatAdd.add_correct e (base + Int64.ofInt (-64672)) addCode
      (arithmeticCallState s (base + 560).toBitVec) left right address capacity used
      (base + 560).toBitVec owned) next

end SszX86.CodecMeasureFixed

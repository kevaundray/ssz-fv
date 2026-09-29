import SszX86.CodecMeasureFixedArithmeticAdd
import SszX86.CodecMeasureFixedArithmeticDivide
import SszX86.CodecMeasureFixedArithmeticMul
import SszX86.BitVectorMappingClosure

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Mapping closure is obtained from the actual proved execution, not added to
any helper's initial ownership or assumed as a stronger provider postcondition. -/
theorem arithmetic_mapped_cps (e : Executable) (s : MachineState)
    (post P : MachineState → Prop) (execution : Eventually (step e) post s)
    (next : ∀ t, post t → BitVector.Mapping.Extends s.1.dmem t.1.dmem →
      Eventually (step e) P t) : Eventually (step e) P s := by
  exact eventually_trans (step e)
    (fun t => post t ∧ BitVector.Mapping.Extends s.1.dmem t.1.dmem) P s
    (BitVector.Mapping.retains_mapping e post s execution)
    (fun t h => next t h.1 h.2)

theorem add196_mapped_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt (-64672)))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatAdd.Owned (arithmeticCallState s (base + 201).toBitVec)
      left right address capacity used (base + 201).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatAdd.Post (arithmeticCallState s (base + 201).toBitVec)
      left right address capacity used (base + 201).toBitVec t →
      BitVector.Mapping.Extends s.dmem t.1.dmem → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 196) := by
  apply arithmetic_mapped_cps e (s, base + 196) _ P _ next
  exact add196_cps e base hc addCode s left right address capacity used hmap owned _
    (fun t post => .done t post)

theorem add555_mapped_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (addCode : NatAdd.CodeAt e (base + Int64.ofInt (-64672)))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatAdd.Owned (arithmeticCallState s (base + 560).toBitVec)
      left right address capacity used (base + 560).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatAdd.Post (arithmeticCallState s (base + 560).toBitVec)
      left right address capacity used (base + 560).toBitVec t →
      BitVector.Mapping.Extends s.dmem t.1.dmem → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 555) := by
  apply arithmetic_mapped_cps e (s, base + 555) _ P _ next
  exact add555_cps e base hc addCode s left right address capacity used hmap owned _
    (fun t post => .done t post)

theorem divide313_mapped_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (divisionCode : NatDivision.CodeAt e (base + Int64.ofInt (-72976)))
    (udivCode : Udivti3.Embedded.CodeAt e
      ((base + Int64.ofInt (-72976)) + Int64.ofNat NatDivision.udivOffset))
    (s : MachineData) (operand : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatDivision.Owned (arithmeticCallState s (base + 318).toBitVec)
      operand 8 address capacity used (base + 318).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatDivision.Post (arithmeticCallState s (base + 318).toBitVec)
      operand 8 address capacity used (base + 318).toBitVec t →
      BitVector.Mapping.Extends s.dmem t.1.dmem → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 313) := by
  apply arithmetic_mapped_cps e (s, base + 313) _ P _ next
  exact divide313_cps e base hc divisionCode udivCode s operand address capacity used hmap owned _
    (fun t post => .done t post)

theorem mul581_mapped_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (mulCode : NatMul.CodeAt e (base + Int64.ofInt (-61792)))
    (wordCode : NatMulWord.CodeAt e ((base + Int64.ofInt (-61792)) + 832))
    (memsetCode : MemsetCall.MemsetCodeAt e ((base + Int64.ofInt (-61792)) + 148928))
    (s : MachineData) (left right : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatMul.Owned (arithmeticCallState s (base + 586).toBitVec)
      left right address capacity used (base + 586).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatMul.Post (arithmeticCallState s (base + 586).toBitVec)
      left right address capacity used (base + 586).toBitVec t →
      BitVector.Mapping.Extends s.dmem t.1.dmem → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 581) := by
  apply arithmetic_mapped_cps e (s, base + 581) _ P _ next
  exact mul581_cps e base hc mulCode wordCode memsetCode s left right address capacity used hmap owned _
    (fun t post => .done t post)

end SszX86.CodecMeasureFixed

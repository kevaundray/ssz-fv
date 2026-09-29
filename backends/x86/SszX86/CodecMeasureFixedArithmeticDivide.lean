import SszX86.CodecMeasureFixedArithmeticCall
import SszX86.NatDivisionProofs

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Division enters at the real CALL and includes the linked __udivti3 lowering.
The physical provider contract retains raw Large representations and error frames. -/
theorem divide313_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (divisionCode : NatDivision.CodeAt e (base + Int64.ofInt (-72976)))
    (udivCode : Udivti3.Embedded.CodeAt e
      ((base + Int64.ofInt (-72976)) + Int64.ofNat NatDivision.udivOffset))
    (s : MachineData) (operand : NatOperand) (address capacity used : BitVec 64)
    (hmap : ArithmeticCallSlot s)
    (owned : NatDivision.Owned (arithmeticCallState s (base + 318).toBitVec)
      operand 8 address capacity used (base + 318).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatDivision.Post (arithmeticCallState s (base + 318).toBitVec)
      operand 8 address capacity used (base + 318).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 313) := by
  apply call313 e base hc s P hmap
  apply eventually_trans (step e)
    (NatDivision.Post (arithmeticCallState s (base + 318).toBitVec)
      operand 8 address capacity used (base + 318).toBitVec) P _
  · simpa only [show Int64.ofNat NatDivision.entry = 0 by decide, Int64.add_zero] using
      NatDivision.divide_correct e (base + Int64.ofInt (-72976)) divisionCode udivCode
        (arithmeticCallState s (base + 318).toBitVec) operand 8 address capacity used
        (base + 318).toBitVec owned
  · exact next

end SszX86.CodecMeasureFixed

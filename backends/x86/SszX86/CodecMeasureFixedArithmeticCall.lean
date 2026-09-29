import SszX86.CodecMeasureFixedDecode
import SszX86.NatDivisionCall

namespace SszX86.CodecMeasureFixed

/-- The actual CALL push, before execution of any helper instruction. -/
abbrev arithmeticCallState := NatDivision.callState

def ArithmeticCallSlot (s : MachineData) : Prop :=
  ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old

theorem arithmetic_call_slot_load (s : MachineData) (ra : BitVec 64) :
    Mem.loadInt (arithmeticCallState s ra).dmem
      (arithmeticCallState s ra).regs.rsp.toBitVec 8 =
        some (Int.ofBytes (wordBytes ra)) :=
  NatDivision.call_slot_load s.dmem (s.regs.rsp.toBitVec - 8) ra

theorem call196 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmap : ArithmeticCallSlot s)
    (next : Eventually (step e) P
      (arithmeticCallState s (base + 201).toBitVec, base + Int64.ofInt (-64672))) :
    Eventually (step e) P (s, base + 196) := by
  codec_measure_fixed_step 51 using hc
  apply Delimited.store_cps
  · exact hmap
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

theorem call313 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmap : ArithmeticCallSlot s)
    (next : Eventually (step e) P
      (arithmeticCallState s (base + 318).toBitVec, base + Int64.ofInt (-72976))) :
    Eventually (step e) P (s, base + 313) := by
  codec_measure_fixed_step 80 using hc
  apply Delimited.store_cps
  · exact hmap
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

theorem call555 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmap : ArithmeticCallSlot s)
    (next : Eventually (step e) P
      (arithmeticCallState s (base + 560).toBitVec, base + Int64.ofInt (-64672))) :
    Eventually (step e) P (s, base + 555) := by
  codec_measure_fixed_step 140 using hc
  apply Delimited.store_cps
  · exact hmap
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

theorem call581 (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmap : ArithmeticCallSlot s)
    (next : Eventually (step e) P
      (arithmeticCallState s (base + 586).toBitVec, base + Int64.ofInt (-61792))) :
    Eventually (step e) P (s, base + 581) := by
  codec_measure_fixed_step 148 using hc
  apply Delimited.store_cps
  · exact hmap
  · simpa [arithmeticCallState, NatDivision.callState, Effects.All, Int64.add_assoc] using next

end SszX86.CodecMeasureFixed

import SszX86.MeasureOwned
import SszX86.DelimitedCompare

namespace SszX86.Measure.Bits
open SszNative UintCodec

/-- The caller's only helper activation is its real eight-byte return slot. -/
def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

theorem list_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 1358).toBitVec, base + Int64.ofInt compareOffset)) :
    Eventually (step e) P (s, base + 1353) := by
  measure_step 152 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, compareOffset, Effects.All, Int64.add_assoc] using next

theorem progressive_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 1548).toBitVec, base + Int64.ofInt compareOffset)) :
    Eventually (step e) P (s, base + 1543) := by
  measure_step 194 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, compareOffset, Effects.All, Int64.add_assoc] using next

theorem from_u128_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 2119).toBitVec, base + Int64.ofInt fromU128Offset)) :
    Eventually (step e) P (s, base + 2114) := by
  measure_step 296 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, fromU128Offset, Effects.All, Int64.add_assoc] using next

/-- Complete linked comparison after its concrete CALL; only represented Pair
observations are used, with no value or padding normalization assumption. -/
theorem list_compare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (lhs rhs : Nat)
    (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hl : NatMemory.Pair (widthLoad (callState s (base + 1358).toBitVec).dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (hr : NatMemory.Pair (widthLoad (callState s (base + 1358).toBitVec).dmem)
      s.regs.rdx.toBitVec s.regs.rcx.toBitVec rhs)
    (next : ∀ t, NatCompare.Returned (callState s (base + 1358).toBitVec)
      (base + 1358).toBitVec (compare lhs rhs) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 1353) := by
  apply list_call_cps e base hc s P hm
  apply eventually_trans (step e)
    (NatCompare.Returned (callState s (base + 1358).toBitVec)
      (base + 1358).toBitVec (compare lhs rhs)) P _
  · apply NatCompare.program_correct e (base + Int64.ofInt compareOffset) helpers.compare
      (callState s (base + 1358).toBitVec) lhs rhs (base + 1358).toBitVec hl hr
    exact Delimited.stored_return_load s.dmem (s.regs.rsp.toBitVec - 8) (base + 1358).toBitVec
  · exact next

theorem progressive_compare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s : MachineData) (lhs rhs : Nat)
    (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hl : NatMemory.Pair (widthLoad (callState s (base + 1548).toBitVec).dmem)
      s.regs.rdi.toBitVec s.regs.rsi.toBitVec lhs)
    (hr : NatMemory.Pair (widthLoad (callState s (base + 1548).toBitVec).dmem)
      s.regs.rdx.toBitVec s.regs.rcx.toBitVec rhs)
    (next : ∀ t, NatCompare.Returned (callState s (base + 1548).toBitVec)
      (base + 1548).toBitVec (compare lhs rhs) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 1543) := by
  apply progressive_call_cps e base hc s P hm
  apply eventually_trans (step e)
    (NatCompare.Returned (callState s (base + 1548).toBitVec)
      (base + 1548).toBitVec (compare lhs rhs)) P _
  · apply NatCompare.program_correct e (base + Int64.ofInt compareOffset) helpers.compare
      (callState s (base + 1548).toBitVec) lhs rhs (base + 1548).toBitVec hl hr
    exact Delimited.stored_return_load s.dmem (s.regs.rsp.toBitVec - 8) (base + 1548).toBitVec
  · exact next

end SszX86.Measure.Bits

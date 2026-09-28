import SszX86.BitVectorCore

namespace SszX86.BitVector
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The real CALL at 152 stores 157 before entering the linked divider. -/
theorem division_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmapped : CallSlot s)
    (next : Eventually (step e) P
      (callState s (base + 157).toBitVec, base + Int64.ofInt divisionOffset)) :
    Eventually (step e) P (s, base + 152) := by
  bitvector_step 9 using hc
  apply Delimited.store_cps
  · exact hmapped
  · simpa [callState, NatDivision.callState, divisionOffset, Effects.All, Int64.add_assoc] using next

/-- The real CALL at 1759 stores 1764 before entering the linked addition. -/
theorem add_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmapped : CallSlot s)
    (next : Eventually (step e) P
      (callState s (base + 1764).toBitVec, base + Int64.ofInt addOffset)) :
    Eventually (step e) P (s, base + 1759) := by
  bitvector_step 51 using hc
  apply Delimited.store_cps
  · exact hmapped
  · simpa [callState, NatDivision.callState, addOffset, Effects.All, Int64.add_assoc] using next

/-- The exact helper receives its output in RDI, never in an implicit sret slot. -/
theorem exact_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmapped : CallSlot s)
    (next : Eventually (step e) P
      (callState s (base + 4639).toBitVec, base + Int64.ofInt exactOffset)) :
    Eventually (step e) P (s, base + 4634) := by
  bitvector_step 93 using hc
  apply Delimited.store_cps
  · exact hmapped
  · simpa [callState, NatDivision.callState, exactOffset, Effects.All, Int64.add_assoc] using next

/-- Conversion runs on the original descriptor pair, not on the rounded length. -/
theorem to_u128_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (hmapped : CallSlot s)
    (next : Eventually (step e) P
      (callState s (base + 5249).toBitVec, base + Int64.ofInt toU128Offset)) :
    Eventually (step e) P (s, base + 5244) := by
  bitvector_step 171 using hc
  apply Delimited.store_cps
  · exact hmapped
  · simpa [callState, NatDivision.callState, toU128Offset, Effects.All, Int64.add_assoc] using next

/-- Composition includes the divider's actual nested __udivti3 calls and RET. -/
theorem divide_cps (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (length : NatOperand) (address capacity used : BitVec 64)
    (hmapped : CallSlot s)
    (owned : NatDivision.Owned (callState s (base + 157).toBitVec) length 8
      address capacity used (base + 157).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatDivision.Post (callState s (base + 157).toBitVec) length 8
      address capacity used (base + 157).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 152) := by
  apply division_call_cps e base hc.body s P hmapped
  apply eventually_trans (step e)
    (NatDivision.Post (callState s (base + 157).toBitVec) length 8
      address capacity used (base + 157).toBitVec) P _
  · simpa only [show Int64.ofNat NatDivision.entry = 0 by decide, Int64.add_zero] using
      NatDivision.divide_correct e (base + Int64.ofInt divisionOffset) hc.division hc.udiv
        (callState s (base + 157).toBitVec) length 8 address capacity used
        (base + 157).toBitVec owned
  · exact next

/-- Addition's allocator failure is retained by its complete Post contract. -/
theorem add_cps (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (quotient : NatOperand) (address capacity used : BitVec 64)
    (hmapped : CallSlot s)
    (owned : NatAdd.Owned (callState s (base + 1764).toBitVec) quotient (.small 1)
      address capacity used (base + 1764).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatAdd.Post (callState s (base + 1764).toBitVec) quotient (.small 1)
      address capacity used (base + 1764).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 1759) := by
  apply add_call_cps e base hc.body s P hmapped
  exact eventually_trans (step e)
    (NatAdd.Post (callState s (base + 1764).toBitVec) quotient (.small 1)
      address capacity used (base + 1764).toBitVec) P _
    (NatAdd.add_correct e (base + Int64.ofInt addOffset) hc.add
      (callState s (base + 1764).toBitVec) quotient (.small 1) address capacity used
      (base + 1764).toBitVec owned) next

/-- Exact comparison runs to the real return site on both success and failure. -/
theorem exact_cps (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (expected : NatOperand) (actual : BitVec 64)
    (hmapped : CallSlot s)
    (owned : NatExact.Owned (callState s (base + 4639).toBitVec) expected actual
      (base + 4639).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatExact.Post (callState s (base + 4639).toBitVec) expected actual
      (base + 4639).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 4634) := by
  apply exact_call_cps e base hc.body s P hmapped
  apply eventually_trans (step e)
    (NatExact.Post (callState s (base + 4639).toBitVec) expected actual
      (base + 4639).toBitVec) P _
  · simpa only [show Int64.ofNat NatExact.entry = 0 by decide, Int64.add_zero] using
      NatExact.exact_correct e (base + Int64.ofInt exactOffset) hc.exact
        (callState s (base + 4639).toBitVec) expected actual (base + 4639).toBitVec owned
  · exact next

/-- The linked narrowing proof observes the full Option representation. -/
theorem to_u128_cps (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s : MachineData) (length : NatOperand) (hmapped : CallSlot s)
    (owned : NatToU128.Owned (callState s (base + 5249).toBitVec) length
      (base + 5249).toBitVec)
    (P : MachineState → Prop)
    (next : ∀ t, NatToU128.Post (callState s (base + 5249).toBitVec) length
      (base + 5249).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 5244) := by
  apply to_u128_call_cps e base hc.body s P hmapped
  apply eventually_trans (step e)
    (NatToU128.Post (callState s (base + 5249).toBitVec) length
      (base + 5249).toBitVec) P _
  · simpa only [show Int64.ofNat NatToU128.entry = 0 by decide, Int64.add_zero] using
      NatToU128.to_u128_correct e (base + Int64.ofInt toU128Offset) hc.toU128
        (callState s (base + 5249).toBitVec) length (base + 5249).toBitVec owned
  · exact next

end SszX86.BitVector

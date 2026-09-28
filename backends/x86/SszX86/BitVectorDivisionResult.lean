import SszX86.BitVectorCore

namespace SszX86.BitVector
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def divisionResultMem (m : DataMem) (sp pointer payload : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m (sp + 120#64) 8 pointer.toInt) (sp + 128#64) 8 payload.toInt

def divisionResultState (s : MachineData) (pointer payload remainder : BitVec 64)
    (statusWord : BitVec 32) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (statusWord.setWidth 64)
      rcx := UInt64.ofBitVec pointer
      rdx := UInt64.ofBitVec payload
      r13 := UInt64.ofBitVec remainder}
    dmem := divisionResultMem s.dmem s.regs.rsp.toBitVec pointer payload
    status := flags}

macro "bitvector_stack_output " row:num " at " off:num
    " using " hc:term " mapped " hm:term : tactic => `(tactic|
  (bitvector_step $row using $hc
   try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
   apply Delimited.store_cps
   · apply UintCodec.Large.mapped_load (capacity := 224) («offset» := $off) («width» := 8)
     · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
     · decide
   simp only [Effects.All]))

/-- Read the real private result, retain its exact Nat pair in caller locals,
and branch on its four-byte status before any optional rounding or input read. -/
theorem division_result_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload remainder : BitVec 64) (statusWord : BitVec 32)
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 224)
    (hstatus : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 4 = some (statusWord.toNat : Int))
    (hpointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (payload.toNat : Int))
    (hremainder : Mem.loadInt (divisionResultMem s.dmem s.regs.rsp.toBitVec pointer payload)
      (s.regs.rsp.toBitVec + 32#64) 8 = some (remainder.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (divisionResultState s pointer payload remainder statusWord flags,
        if statusWord = 0#32 then base + 1689 else base + 197)) :
    Eventually (step e) P (s, base + 157) := by
  have target := hc.targets ("bitVector_u1689", 1689) (by decide)
  simp only [divisionResultMem] at hremainder
  bitvector_step 10 using hc
  bitvector_load hstatus
  bitvector_step 11 using hc
  bitvector_load hpointer
  bitvector_step 12 using hc
  bitvector_load hpayload
  bitvector_stack_output 13 at 120 using hc mapped hm
  bitvector_stack_output 14 at 128 using hc mapped hm
  bitvector_step 15 using hc
  bitvector_load hremainder
  bitvector_step 16 using hc
  constructor <;> bitvector_step 17 using hc
  all_goals
    by_cases zero : statusWord = 0#32
    · simpa [zero, target, divisionResultState, divisionResultMem,
        StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, divisionResultState, divisionResultMem,
        StatusFlags.from_result, Effects.All] using next _

end SszX86.BitVector

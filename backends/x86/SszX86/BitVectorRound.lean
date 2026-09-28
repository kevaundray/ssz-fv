import SszX86.BitVectorDivisionResult

namespace SszX86.BitVector
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def expectedPairMem (m : DataMem) (sp pointer payload : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m (sp + 208#64) 8 pointer.toInt) (sp + 216#64) 8 payload.toInt

def roundBranchState (s : MachineData) (pointer payload : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec pointer, rcx := UInt64.ofBitVec payload}
    dmem := expectedPairMem s.dmem s.regs.rsp.toBitVec pointer payload
    status := flags}

theorem round_branch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 224)
    (hpointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 120#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 128#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (roundBranchState s pointer payload flags,
        if s.regs.r13.toBitVec = 0#64 then base + 4618 else base + 1727)) :
    Eventually (step e) P (s, base + 1689) := by
  have target := hc.targets ("bitVector_u4618", 4618) (by decide)
  bitvector_step 39 using hc
  bitvector_load hpointer
  bitvector_step 40 using hc
  bitvector_load hpayload
  bitvector_stack_output 41 at 208 using hc mapped hm
  bitvector_stack_output 42 at 216 using hc mapped hm
  bitvector_step 43 using hc
  constructor <;> bitvector_step 44 using hc
  all_goals
    by_cases zero : s.regs.r13.toBitVec = 0#64
    · simpa [zero, target, roundBranchState, expectedPairMem,
        StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, roundBranchState, expectedPairMem,
        StatusFlags.from_result, Effects.All] using next _

def roundSetupState (s : MachineData) (pointer payload : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec pointer
      rdx := UInt64.ofBitVec payload
      rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
      r8 := UInt64.ofBitVec 1#64
      rcx := UInt64.ofBitVec 0#64
      r9 := s.regs.rbx}
    status := flags}

/-- Actual Nat::add arguments: the division quotient, Small1, and the same arena. -/
theorem round_setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hpointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 208#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 216#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (roundSetupState s pointer payload flags, base + 1759)) :
    Eventually (step e) P (s, base + 1727) := by
  bitvector_step 45 using hc
  bitvector_load hpointer
  bitvector_step 46 using hc
  bitvector_load hpayload
  bitvector_step 47 using hc
  bitvector_step 48 using hc
  bitvector_step 49 using hc
  constructor <;> bitvector_step 50 using hc
  all_goals simpa [roundSetupState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next _

/-- A successful addition replaces the expected pair with the exact returned
representation, including an allocated Large pointer or a normalized Small. -/
theorem round_success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 224)
    (hpointer : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (roundBranchState s pointer payload s.status, base + 4618)) :
    Eventually (step e) P (s, base + 4592) := by
  bitvector_step 86 using hc
  bitvector_load hpointer
  bitvector_step 87 using hc
  bitvector_load hpayload
  bitvector_stack_output 88 at 208 using hc mapped hm
  bitvector_stack_output 89 at 216 using hc mapped hm
  simpa [roundBranchState, expectedPairMem] using next

def exactSetupState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
    rsi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 208#64)
    rdx := s.regs.r14}}

theorem exact_setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (exactSetupState s, base + 4634)) :
    Eventually (step e) P (s, base + 4618) := by
  bitvector_step 90 using hc
  bitvector_step 91 using hc
  bitvector_step 92 using hc
  simpa [exactSetupState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

def toU128SetupState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
    rsi := s.regs.r15
    rdx := s.regs.r12}}

theorem to_u128_setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (toU128SetupState s, base + 5244)) :
    Eventually (step e) P (s, base + 5233) := by
  bitvector_step 168 using hc
  bitvector_step 169 using hc
  bitvector_step 170 using hc
  simpa [toU128SetupState, BitVec.ofInt_add, BitVec.ofInt_toInt] using next

end SszX86.BitVector

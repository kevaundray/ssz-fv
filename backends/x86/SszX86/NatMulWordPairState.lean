import SszX86.NatMulWordLoopStep
import SszX86.NatMulWordLoopFetch

namespace SszX86.NatMulWord
open SszNative

def firstStep (s : MachineData) (limb : BitVec 64) : BitVec 64 × Nat :=
  LimbMul.step s.regs.rcx.toBitVec limb 0 s.regs.r10.toNat

def secondStep (s : MachineData) (first second : BitVec 64) : BitVec 64 × Nat :=
  LimbMul.step s.regs.rcx.toBitVec second 0 (firstStep s first).2

def firstAddress (s : MachineData) : BitVec 64 :=
  s.regs.rbp.toBitVec + s.regs.rax.toBitVec * 8#64 - 8#64

def secondAddress (s : MachineData) : BitVec 64 :=
  s.regs.rbp.toBitVec + s.regs.rax.toBitVec * 8#64

def pairMemory (s : MachineData) (first second : BitVec 64) : DataMem :=
  let m := Mem.storeInt s.dmem (firstAddress s) 8 (firstStep s first).1.toInt
  Mem.storeInt m (secondAddress s) 8 (secondStep s first second).1.toInt

def firstProducedState (s : MachineData) (first : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (firstStep s first).1
      rdx := UInt64.ofBitVec (productHigh first s.regs.rcx.toBitVec)
      r8 := s.regs.rax
      r11 := UInt64.ofNat (firstStep s first).2}
    status := flags}

def pairFirstStoredState (s : MachineData) (first : BitVec 64) (flags : StatusFlags) : MachineData :=
  {firstProducedState s first flags with
    regs := {(firstProducedState s first flags).regs with
      r13 := UInt64.ofBitVec (s.regs.rax.toBitVec + 1)}
    dmem := Mem.storeInt s.dmem (firstAddress s) 8 (firstStep s first).1.toInt}

def secondProducedState (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (secondStep s first second).1
      rdx := UInt64.ofBitVec (productHigh second s.regs.rcx.toBitVec)
      r8 := s.regs.rax
      r10 := UInt64.ofNat (secondStep s first second).2
      r11 := UInt64.ofNat (firstStep s first).2
      r13 := UInt64.ofBitVec (s.regs.rax.toBitVec + 1)}
    dmem := Mem.storeInt s.dmem (firstAddress s) 8 (firstStep s first).1.toInt
    status := flags}

def unrolledState (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) : MachineData :=
  {secondProducedState s first second flags with
    regs := {(secondProducedState s first second flags).regs with
      rax := UInt64.ofBitVec (s.regs.rax.toBitVec + 2)}
    dmem := pairMemory s first second}

private theorem product_comm (factor limb : BitVec 64) :
    productHigh factor limb = productHigh limb factor := by
  simp only [productHigh, Int.mul_comm]

private theorem step_comm (factor limb : BitVec 64) (carry : Nat) :
    LimbMul.step factor limb 0 carry = LimbMul.step limb factor 0 carry := by
  simp only [LimbMul.step, Nat.mul_comm]

theorem first_product_bridge (s : MachineData) (first : BitVec 64)
    (fetchFlags mulFlags flags : StatusFlags) :
    firstCarriedState (loopProductState (firstFetchedState s first fetchFlags) mulFlags) flags =
      firstProducedState s first flags := by
  have arithmetic := word_carry_step first s.regs.rcx.toBitVec s.regs.r10.toNat s.regs.r10.toBitVec.isLt
  rw [step_comm] at arithmetic
  have low : first * s.regs.rcx.toBitVec + s.regs.r10.toBitVec = (firstStep s first).1 := by
    simpa only [firstStep, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using arithmetic.1
  have high : productHigh first s.regs.rcx.toBitVec +
      BitVec.ofNat 64 (Udivti3.addFlags (first * s.regs.rcx.toBitVec) s.regs.r10.toBitVec).cf.toNat =
      BitVec.ofNat 64 (firstStep s first).2 := by
    simpa only [firstStep, ← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using arithmetic.2
  simp only [firstCarriedState, loopProductState, firstFetchedState, firstProducedState,
    WordNormalize.ofNat, UInt64.toBitVec_ofBitVec, low, high]

theorem first_store_bridge (s : MachineData) (first : BitVec 64) (flags : StatusFlags) :
    firstStoredState (firstProducedState s first flags) = pairFirstStoredState s first flags := by
  simp only [firstStoredState, firstProducedState, pairFirstStoredState, firstAddress,
    UInt64.toBitVec_ofBitVec]

theorem second_product_bridge (s : MachineData) (first second : BitVec 64)
    (firstFlags fetchFlags mulFlags flags : StatusFlags) :
    secondCarriedState (loopProductState
      (secondFetchedState (pairFirstStoredState s first firstFlags) second fetchFlags) mulFlags) flags =
      secondProducedState s first second flags := by
  have bound := LimbMul.step_carry_lt s.regs.rcx.toBitVec first 0 s.regs.r10.toNat s.regs.r10.toBitVec.isLt
  have arithmetic := word_carry_step second s.regs.rcx.toBitVec (firstStep s first).2 bound
  rw [step_comm] at arithmetic
  simp only [secondCarriedState, loopProductState, secondFetchedState, pairFirstStoredState,
    firstProducedState, secondProducedState, secondStep, WordNormalize.ofNat,
    UInt64.toBitVec_ofBitVec, arithmetic.1, arithmetic.2]

theorem second_store_bridge (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) :
    secondStoredState (secondProducedState s first second flags) = unrolledState s first second flags := by
  have advance : s.regs.rax.toBitVec + 1 + 1 = s.regs.rax.toBitVec + 2 := by bv_omega
  simp only [secondStoredState, secondProducedState, unrolledState, pairMemory,
    secondAddress, UInt64.toBitVec_ofBitVec, advance]

end SszX86.NatMulWord

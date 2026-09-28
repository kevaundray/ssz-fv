import SszX86.NatMulWordPairCps
import SszX86.NatMulWordLoopMath
import SszX86.NatMulMemoryBuffer

namespace SszX86.NatMulWord
open SszNative UintCodec

structure PairStable (s t : MachineData) : Prop where
  rbx : t.regs.rbx = s.regs.rbx
  rcx : t.regs.rcx = s.regs.rcx
  rbp : t.regs.rbp = s.regs.rbp
  rsi : t.regs.rsi = s.regs.rsi
  rdi : t.regs.rdi = s.regs.rdi
  rsp : t.regs.rsp = s.regs.rsp
  r9 : t.regs.r9 = s.regs.r9
  r12 : t.regs.r12 = s.regs.r12
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15
  zmms : t.zmms = s.zmms

theorem PairStable.trans {s t u : MachineData} (front : PairStable s t) (back : PairStable t u) :
    PairStable s u :=
  ⟨back.rbx.trans front.rbx, back.rcx.trans front.rcx, back.rbp.trans front.rbp,
    back.rsi.trans front.rsi, back.rdi.trans front.rdi, back.rsp.trans front.rsp,
    back.r9.trans front.r9, back.r12.trans front.r12, back.r14.trans front.r14,
    back.r15.trans front.r15, back.zmms.trans front.zmms⟩

theorem pair_stable (s : MachineData) (first second : BitVec 64) (flags : StatusFlags) :
    PairStable s (unrolledState s first second flags) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem source_word (m : DataMem) (pointer : BitVec 64) (words : List (BitVec 64))
    (index : Nat) (stored : (NatOperand.large pointer words).At (widthLoad m)) :
    (index < words.length → Mem.loadInt m (pointer + BitVec.ofNat 64 index * 8#64) 8 =
      some ((words[index]?.getD 0).toNat : Int)) ∧
    (words.length ≤ index → words[index]?.getD 0 = 0#64) := by
  constructor
  · intro inside
    have loaded := widthLoad_eq m _ _ _ (stored.2.2.2 ⟨index, inside⟩)
    simpa [width_address, List.getElem?_eq_getElem inside,
      BitVec.ofNat_mul, Nat.mul_comm] using loaded
  · intro outside
    simp [List.getElem?_eq_none (by omega)]

theorem pair_addresses (s : MachineData) (dst : BitVec 64) (index : Nat)
    (pointer : s.regs.rbp.toBitVec = dst+8#64)
    (counter : s.regs.rax.toBitVec = BitVec.ofNat 64 index) :
    firstAddress s = dst+BitVec.ofNat 64 (8*index) ∧
    secondAddress s = dst+BitVec.ofNat 64 (8*(index+1)) := by
  simp only [firstAddress, secondAddress, pointer, counter, BitVec.ofNat_mul,
    BitVec.ofNat_add]
  constructor <;> bv_omega

theorem pair_memory (s : MachineData) (dst factor : BitVec 64) (index carry : Nat)
    (first second : BitVec 64)
    (pointer : s.regs.rbp.toBitVec = dst+8#64)
    (counter : s.regs.rax.toBitVec = BitVec.ofNat 64 index)
    (multiplier : s.regs.rcx.toBitVec = factor)
    (carryReg : s.regs.r10.toBitVec = BitVec.ofNat 64 carry) (carryBound : carry < 2^64) :
    pairMemory s first second = Large.fillMem s.dmem dst index
      [(LimbMul.step factor first 0 carry).1,
        (LimbMul.step factor second 0 (LimbMul.step factor first 0 carry).2).1] := by
  have carryNat : s.regs.r10.toNat = carry := by
    change s.regs.r10.toBitVec.toNat = carry
    rw [carryReg]
    exact Nat.mod_eq_of_lt carryBound
  have addresses := pair_addresses s dst index pointer counter
  simp only [pairMemory, firstStep, secondStep, multiplier, carryNat,
    addresses.1, addresses.2, Large.fillMem]

end SszX86.NatMulWord

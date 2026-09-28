import SszX86.BitVectorEntryMemory
import SszX86.BitVectorRebase

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem workspace_output_mapped (s t : MachineData) (count : Nat) (inside : 88 + count ≤ workSize)
    (hm : Large.Mapped t.dmem (s.regs.rsp.toBitVec - 72#64) workSize)
    (output : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64) :
    Large.Mapped t.dmem t.regs.rdi.toBitVec count := by
  have part := mapped_subrange t.dmem (s.regs.rsp.toBitVec - 72#64) workSize 88 count hm inside
  have location : s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 88 = s.regs.rsp.toBitVec + 16#64 := by
    bv_omega
  rw [location, ← output] at part
  exact part

theorem operand_borrowed_work (s : MachineData) (address capacity used : BitVec 64)
    (operand : NatOperand) (count : Nat) (inside : count ≤ 208)
    (lower : 72 ≤ s.regs.rsp.toNat) (owned : OperandProtected s address capacity used operand) :
    NatToU128.BorrowedApart (s.regs.rsp.toNat + 16) count operand := by
  cases operand with
  | small limb => trivial
  | large pointer words =>
    have apart := owned.work
    change Body.Apart pointer.toNat (8 * words.length) (s.regs.rsp.toNat + 16) count
    unfold Body.Apart at apart ⊢
    unfold workStart workSize at apart
    omega

/-- Exact's private output and expected metadata are disjoint subregions of the
real body work area; the expected limb buffer follows its proven provenance. -/
theorem exact_owned (s t : MachineData) (saved : Saved) (length expected : NatOperand)
    (data : Ssz.Bytes) (address capacity used actual ra : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (output : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64)
    (stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64)
    (metadata : t.regs.rsi.toBitVec = s.regs.rsp.toBitVec + 208#64)
    (actualRegister : t.regs.rdx.toBitVec = actual)
    (hm : Large.Mapped t.dmem (s.regs.rsp.toBitVec - 72#64) workSize)
    (stored : NatArithmetic.operandAt (widthLoad t.dmem) (s.regs.rsp.toNat + 208) expected)
    (protectedOperand : OperandProtected s address capacity used expected)
    (ret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    NatExact.Owned t expected actual ra := by
  have low := owned.stack_low
  have high := owned.stack_bound
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have outNat : t.regs.rdi.toNat = s.regs.rsp.toNat + 16 := by
    change t.regs.rdi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [output]
    bv_omega
  have spNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
    change t.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [stack]
    bv_omega
  have metaNat : t.regs.rsi.toNat = s.regs.rsp.toNat + 208 := by
    change t.regs.rsi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 208
    rw [metadata]
    bv_omega
  refine ⟨actualRegister, ?_, ?_, ?_, ?_, ?_,
    workspace_output_mapped s t 68 (by decide) hm output, ?_, ret, ?_⟩
  · simpa only [metaNat] using stored
  · omega
  · unfold Body.Apart
    omega
  · rw [outNat]
    exact operand_borrowed_work s address capacity used expected 68 (by decide) low protectedOperand
  · omega
  · omega
  · unfold Body.Apart
    omega

/-- Original Nat narrowing reads only the physically preserved descriptor limbs
and writes its private 32-byte output inside the same caller-owned work area. -/
theorem to_u128_owned (s t : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (output : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64)
    (stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64)
    (pointer : t.regs.rsi.toBitVec = length.pointer)
    (payload : t.regs.rdx.toBitVec = length.payload)
    (hm : Large.Mapped t.dmem (s.regs.rsp.toBitVec - 72#64) workSize)
    (stored : length.At (widthLoad t.dmem))
    (ret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    NatToU128.Owned t length ra := by
  have low := owned.stack_low
  have high := owned.stack_bound
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have outNat : t.regs.rdi.toNat = s.regs.rsp.toNat + 16 := by
    change t.regs.rdi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [output]
    bv_omega
  have spNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
    change t.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [stack]
    bv_omega
  refine ⟨pointer, payload, stored, ?_, ?_,
    workspace_output_mapped s t 32 (by decide) hm output, ?_, ret, ?_⟩
  · rw [outNat]
    exact operand_borrowed_work s address capacity used length 32 (by decide) low owned.operand_owned
  · omega
  · omega
  · unfold Body.Apart
    omega

end SszX86.BitVector

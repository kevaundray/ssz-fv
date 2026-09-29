import SszX86.CodecMeasureFixedCore
import SszX86.CodecMeasureFixedArithmeticCall
import SszX86.CodecStoragePlan
import SszX86.NatMulOwnership

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Bounded interval exclusion is recovered from physical byte footprints. -/
theorem arithmetic_apart_of_disjoint (p n q k : Nat)
    (pBound : p + n ≤ 2 ^ 64) (qBound : q + k ≤ 2 ^ 64)
    (disjoint : ∀ a, Codec.InSpan a (BitVec.ofNat 64 p) n →
      ¬ Codec.InSpan a (BitVec.ofNat 64 q) k) : Body.Apart p n q k := by
  by_contra overlap
  have positive : 0 < n ∧ 0 < k ∧ q < p + n ∧ p < q + k := by
    unfold Body.Apart at overlap
    omega
  let a := max p q
  have left : Codec.InSpan (BitVec.ofNat 64 a) (BitVec.ofNat 64 p) n := by
    refine ⟨a - p, by dsimp [a]; omega, ?_⟩
    rw [← BitVec.ofNat_add]
    congr 1
    dsimp [a]
    omega
  have right : Codec.InSpan (BitVec.ofNat 64 a) (BitVec.ofNat 64 q) k := by
    refine ⟨a - q, by dsimp [a]; omega, ?_⟩
    rw [← BitVec.ofNat_add]
    congr 1
    dsimp [a]
    omega
  exact disjoint _ left right

theorem arithmetic_apart_subspan {p n q k start count : Nat}
    (apart : Body.Apart p n q k) (lower : q ≤ start) (upper : start + count ≤ q + k) :
    Body.Apart p n start count := by
  unfold Body.Apart at *
  omega

theorem arithmetic_call_frame (original caller : MachineData) (ra : BitVec 64) (bytes : Nat)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 ≤ bytes) :
    Codec.MemoryFrame original.dmem (arithmeticCallState caller ra).dmem
      (Codec.StackWrites original.regs.rsp.toBitVec bytes) := by
  intro a outside
  change (Mem.storeInt caller.dmem (caller.regs.rsp.toBitVec - 8) 8 ra.toInt).get? a = _
  rw [memory]
  apply memmove_store_lookup_outside
  intro i index same
  have hi : i < 8 := by simpa only [Int.toBytes_length] using index
  apply outside
  apply Codec.stack_subspan original.regs.rsp.toBitVec 136 8 bytes (by omega) a
  change Codec.InSpan a (original.regs.rsp.toBitVec - 136 - 8) 8
  exact ⟨i, hi, by simpa only [stack] using same⟩

/-- Operand safety protects original caller scratch, arena cursor and free suffix.
It does not prohibit aliasing with other read-only data or committed arena bytes. -/
def ArithmeticOperandSafe (original : MachineData) (bytes : Nat)
    (address capacity used : BitVec 64) (operand : NatOperand) : Prop :=
  ∀ a, Emit.NatBorrowed operand a →
    ¬ (Codec.StackWrites original.regs.rsp.toBitVec bytes a ∨
      Codec.InSpan a (original.regs.rdx.toBitVec + 16) 8 ∨
      Codec.InSpan a (address + used) (capacity.toNat - used.toNat))

theorem arithmetic_operand_after_call (original caller : MachineData) (ra : BitVec 64)
    (bytes : Nat) (address capacity used : BitVec 64) (operand : NatOperand)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 ≤ bytes) (stored : operand.At (widthLoad original.dmem))
    (safe : ArithmeticOperandSafe original bytes address capacity used operand) :
    operand.At (widthLoad (arithmeticCallState caller ra).dmem) := by
  apply Codec.operand_frame operand stored (arithmetic_call_frame original caller ra bytes memory stack enough)
  intro a borrowed writes
  exact safe a borrowed (Or.inl writes)

end SszX86.CodecMeasureFixed

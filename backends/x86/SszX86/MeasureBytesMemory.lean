import SszX86.MeasureBytesExec
import SszX86.MeasureBytesSemantics
import SszX86.MeasureOutputMemory
import SszX86.MeasureFrame

namespace SszX86.Measure.Bytes
open SszNative SszNative.Serialize UintCodec

/-- Scope/Limit retain ownership of every original padding limb after publication. -/
theorem error_operand (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64) (desc : Desc)
    (owned : BodyOwned s desc value buffer address capacity used)
    (stored : operand.At (widthLoad s.dmem))
    (borrowed : ∀ a, Emit.NatBorrowed operand a → DescBorrowed desc a)
    (code : Nat) (actual : BitVec 64) :
    operand.At (widthLoad (scalarErrorMem s.dmem s.regs.rbx.toBitVec code
      operand.pointer operand.payload actual)) := by
  apply operand_frame _ _ _ (scalar_error_frame _ _ _ _ _ _) operand
  · intro a inside written
    have readonly := owned.readonly a (Or.inr (Or.inr (Or.inl (borrowed a inside))))
    apply readonly
    apply Or.inl
    obtain ⟨i, hi, equal⟩ := written
    exact ⟨i, by omega, equal⟩
  · exact stored

theorem vector_observed (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteVector operand) value buffer address capacity used) :
    ResultAt (widthLoad (vectorMemory s operand value)) s.regs.rbx.toNat
      (measure (.byteVector operand) value (arenaState address capacity used)).result := by
  cases value with
  | bytes data =>
    by_cases he : operand.value = data.size
    · simp only [vectorMemory, vector_measure, he, ↓reduceIte, unchanged, ResultAt]
      exact plan_reads s.dmem s.regs.rbx.toBitVec (count data.size) trivial
    · simp only [vectorMemory, vector_measure, he, ↓reduceIte, unchanged, ResultAt, ErrorAt]
      apply scalar_error_reads _ _ 3 operand (BitVec.ofNat 64 data.size) (Or.inr rfl)
      exact error_operand s operand (.bytes data) buffer address capacity used
        (.byteVector operand) owned owned.descriptor.2.2.2 (fun _ h => h) 3 _
  | _ =>
    simpa only [vectorMemory, SszNative.Serialize.measure, unchanged, ResultAt, UInt64.toNat_toBitVec] using
      wrong_type_reads s.dmem s.regs.rbx.toBitVec

theorem list_observed (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteList operand) value buffer address capacity used) :
    ResultAt (widthLoad (listMemory s operand value)) s.regs.rbx.toNat
      (measure (.byteList operand) value (arenaState address capacity used)).result := by
  cases value with
  | bytes data =>
    rw [list_measure operand data owned.physical]
    by_cases he : data.size ≤ operand.value
    · simp only [listMemory, he, ↓reduceIte, unchanged, ResultAt]
      exact plan_reads s.dmem s.regs.rbx.toBitVec (count data.size) trivial
    · simp only [listMemory, he, ↓reduceIte, unchanged, ResultAt, ErrorAt]
      apply scalar_error_reads _ _ 2 operand (BitVec.ofNat 64 data.size) (Or.inl rfl)
      exact error_operand s operand (.bytes data) buffer address capacity used
        (.byteList operand) owned owned.descriptor.2.2.2 (fun _ h => h) 2 _
  | _ =>
    simpa only [listMemory, SszNative.Serialize.measure, unchanged, ResultAt, UInt64.toNat_toBitVec] using
      wrong_type_reads s.dmem s.regs.rbx.toBitVec

theorem vector_memory_frame (s : MachineData) (operand : NatOperand) (value : Value)
    (address capacity used : BitVec 64) :
    MemoryFrame s.dmem (vectorMemory s operand value)
      (ResultWrites s.regs.rbx.toBitVec
        (measure (.byteVector operand) value (arenaState address capacity used))) := by
  cases value with
  | bytes data =>
    by_cases he : operand.value = data.size
    · simpa [MemoryFrame, Emit.MemoryFrame, vectorMemory, vector_measure, he, ResultWrites, unchanged] using
        plan_frame s.dmem s.regs.rbx.toBitVec 0 (BitVec.ofNat 64 data.size)
    · simpa [MemoryFrame, Emit.MemoryFrame, vectorMemory, vector_measure, he, ResultWrites, unchanged] using
        scalar_error_frame s.dmem s.regs.rbx.toBitVec 3 operand.pointer operand.payload
          (BitVec.ofNat 64 data.size)
  | _ =>
    simpa [MemoryFrame, Emit.MemoryFrame, vectorMemory, SszNative.Serialize.measure, ResultWrites, unchanged] using
      wrong_type_frame s.dmem s.regs.rbx.toBitVec

theorem list_memory_frame (s : MachineData) (operand : NatOperand) (value : Value)
    (address capacity used : BitVec 64) (physical : value.Physical) :
    MemoryFrame s.dmem (listMemory s operand value)
      (ResultWrites s.regs.rbx.toBitVec
        (measure (.byteList operand) value (arenaState address capacity used))) := by
  cases value with
  | bytes data =>
    rw [list_measure operand data physical]
    by_cases he : data.size ≤ operand.value
    · simpa [MemoryFrame, Emit.MemoryFrame, listMemory, he, ResultWrites, unchanged] using
        plan_frame s.dmem s.regs.rbx.toBitVec 0 (BitVec.ofNat 64 data.size)
    · simpa [MemoryFrame, Emit.MemoryFrame, listMemory, he, ResultWrites, unchanged] using
        scalar_error_frame s.dmem s.regs.rbx.toBitVec 2 operand.pointer operand.payload
          (BitVec.ofNat 64 data.size)
  | _ =>
    simpa [MemoryFrame, Emit.MemoryFrame, listMemory, SszNative.Serialize.measure, ResultWrites, unchanged] using
      wrong_type_frame s.dmem s.regs.rbx.toBitVec

end SszX86.Measure.Bytes

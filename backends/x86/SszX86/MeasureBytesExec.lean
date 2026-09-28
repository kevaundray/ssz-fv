import SszX86.MeasureBytesCompare
import SszX86.MeasureOutput

namespace SszX86.Measure.Bytes
open Kraken.X64.Parser UintCodec SszNative SszNative.Serialize

/-- These memory terms are the actual ordered stores, not semantic outcomes. -/
def vectorMemory (s : MachineData) (operand : NatOperand) : Value → DataMem
  | .bytes data =>
      if operand.value = data.size then
        planMem s.dmem s.regs.rbx.toBitVec 0 (BitVec.ofNat 64 data.size)
      else scalarErrorMem s.dmem s.regs.rbx.toBitVec 3 operand.pointer operand.payload
        (BitVec.ofNat 64 data.size)
  | _ => wrongTypeMem s.dmem s.regs.rbx.toBitVec

def listMemory (s : MachineData) (operand : NatOperand) : Value → DataMem
  | .bytes data =>
      if data.size ≤ operand.value then
        planMem s.dmem s.regs.rbx.toBitVec 0 (BitVec.ofNat 64 data.size)
      else scalarErrorMem s.dmem s.regs.rbx.toBitVec 2 operand.pointer operand.payload
        (BitVec.ofNat 64 data.size)
  | _ => wrongTypeMem s.dmem s.regs.rbx.toBitVec

/-- Branch publication has neither an allocation nor an arena-header write. -/
def Published (s : MachineData) (base : Int64) (memory : DataMem) (t : MachineState) : Prop :=
  t.2 = base + 3335 ∧ t.1.dmem = memory ∧ t.1.regs.rsp = s.regs.rsp ∧ t.1.zmms = s.zmms

theorem vector_type_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : Value)
    (tag : s.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value))
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      ({s with status := fl}, if valueTag value = 2 then base + 537 else base + 3265)) :
    Eventually (step e) P (s, base + 529) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  measure_bytes_step 38 using hc
  measure_bytes_step 39 using hc
  cases value <;>
    simpa [valueTag, Emit.valueTag, StatusFlags.from_result, tag, Effects.All, target] using hp _

theorem list_type_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : Value)
    (tag : s.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value))
    (P : MachineState → Prop)
    (hp : ∀ fl, Eventually (step e) P
      ({s with status := fl}, if valueTag value = 2 then base + 624 else base + 3265)) :
    Eventually (step e) P (s, base + 616) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  measure_bytes_step 57 using hc
  measure_bytes_step 58 using hc
  cases value <;>
    simpa [valueTag, Emit.valueTag, StatusFlags.from_result, tag, Effects.All, target] using hp _

/-- Full actual vector branch, including every wrong-type Value and Scope. -/
theorem vector_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteVector operand) value buffer address capacity used) :
    Eventually (step e) (Published s base (vectorMemory s operand value)) (s, base + 529) := by
  apply vector_type_guard e base hc s value owned.tag
  intro fl
  cases value with
  | bytes data =>
    simp only [valueTag, Emit.valueTag, ↓reduceIte]
    have hn : (BitVec.ofNat 64 data.size).toNat = data.size := Nat.mod_eq_of_lt owned.physical
    have hload : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 =
        some ((BitVec.ofNat 64 data.size).toNat : Int) := by
      simpa only [hn] using owned.valueStored.2.2.1
    apply vector_header e base hc {s with status := fl} operand
      (BitVec.ofNat 64 data.size) owned.descriptor.2 hload
    apply vector_compare e base hc (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
      operand _ _ _ _ owned.descriptor.2.2.2
    intro si x fl'
    by_cases he : operand.value = data.size
    · simp only [lengthState, UInt64.toNat_ofBitVec, hn, he, ↓reduceIte]
      apply small_success_cps e base hc
        (state (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
          operand.pointer operand.payload si x s.regs.r8.toBitVec fl') owned.resultMapped
      intro fl''
      apply Eventually.done
      exact ⟨rfl, by simp [vectorMemory, he, state, lengthState], rfl, rfl⟩
    · simp only [lengthState, UInt64.toNat_ofBitVec, hn, he, ↓reduceIte]
      apply bytes_scope_cps e base hc
        (state (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
          operand.pointer operand.payload si x s.regs.r8.toBitVec fl') owned.resultMapped
      apply Eventually.done
      exact ⟨rfl, by simp [vectorMemory, he, state, lengthState], rfl, rfl⟩
  | bool flag | uint number | bits bits | seq values | union selector child =>
    simp [valueTag, Emit.valueTag]
    apply wrong_type_cps e base hc {s with status := fl} owned.resultMapped
    apply Eventually.done
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Full actual list branch, with padded/huge logical caps and exact Limit payload. -/
theorem list_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.byteList operand) value buffer address capacity used) :
    Eventually (step e) (Published s base (listMemory s operand value)) (s, base + 616) := by
  apply list_type_guard e base hc s value owned.tag
  intro fl
  cases value with
  | bytes data =>
    simp only [valueTag, Emit.valueTag, ↓reduceIte]
    have hn : (BitVec.ofNat 64 data.size).toNat = data.size := Nat.mod_eq_of_lt owned.physical
    have hload : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16) 8 =
        some ((BitVec.ofNat 64 data.size).toNat : Int) := by
      simpa only [hn] using owned.valueStored.2.2.1
    apply list_header e base hc {s with status := fl} operand
      (BitVec.ofNat 64 data.size) owned.descriptor.2 hload
    apply list_compare e base hc (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
      operand _ _ _ _ owned.descriptor.2.2.2
    intro si x y fl'
    by_cases he : data.size ≤ operand.value
    · simp only [lengthState, UInt64.toNat_ofBitVec, hn, he, ↓reduceIte]
      apply small_success_cps e base hc
        (state (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
          operand.pointer operand.payload si x y fl') owned.resultMapped
      intro fl''
      apply Eventually.done
      exact ⟨rfl, by simp [listMemory, he, state, lengthState], rfl, rfl⟩
    · simp only [lengthState, UInt64.toNat_ofBitVec, hn, he, ↓reduceIte]
      apply bytes_limit_cps e base hc
        (state (lengthState {s with status := fl} (BitVec.ofNat 64 data.size))
          operand.pointer operand.payload si x y fl') owned.resultMapped
      apply Eventually.done
      exact ⟨rfl, by simp [listMemory, he, state, lengthState], rfl, rfl⟩
  | bool flag | uint number | bits bits | seq values | union selector child =>
    simp [valueTag, Emit.valueTag]
    apply wrong_type_cps e base hc {s with status := fl} owned.resultMapped
    apply Eventually.done
    exact ⟨rfl, rfl, rfl, rfl⟩

end SszX86.Measure.Bytes

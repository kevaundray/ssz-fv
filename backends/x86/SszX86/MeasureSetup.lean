import SszX86.MeasurePush
import SszX86.DispatchMemory

namespace SszX86.Measure
open BoolCodec UintCodec

def stackState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 216)}
    status := memcpySubFlags s.regs.rsp.toBitVec 216}

def abiState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with r14 := s.regs.rdx, rbx := s.regs.rdi}}

def tagsState (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) : MachineData :=
  {s with regs := {s.regs with
    rdx := UInt64.ofBitVec descriptor, rax := UInt64.ofBitVec (value.setWidth 64)}}

def prepared (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) : MachineData :=
  tagsState (abiState (stackState (savedState s))) descriptor value

theorem stack_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (stackState s, base + 17)) :
    Eventually (step e) P (s, base + 10) := by
  measure_step 6 using hc
  simpa [stackState, memcpySubFlags, BitVec.take, BitVec.signed] using next

theorem abi_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (abiState s, base + 23)) :
    Eventually (step e) P (s, base + 17) := by
  measure_step 7 using hc
  measure_step 8 using hc
  simpa [abiState] using next

theorem tags_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8)
    (P : MachineState → Prop)
    (descLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (descriptor.toNat : Int))
    (valueLoad : Mem.loadInt s.dmem s.regs.r14.toBitVec 1 = some (value.toNat : Int))
    (next : Eventually (step e) P (tagsState s descriptor value, base + 30)) :
    Eventually (step e) P (s, base + 23) := by
  have cast64 : BitVec.ofInt 64 (descriptor.toNat : Int) = descriptor := by bv_omega
  have cast8 : BitVec.ofInt 8 (value.toNat : Int) = value := by bv_omega
  measure_step 9 using hc
  simp only [MachineData.load, Effects.All, descLoad, cast64]
  measure_step 10 using hc
  simp only [MachineData.load, Effects.All, valueLoad, cast8]
  simpa [tagsState] using next

/-- Original entry through both observed enum-tag loads; all six PUSH stores are
proved before using the saved-memory observations. -/
theorem setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8)
    (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (descLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (descriptor.toNat : Int))
    (valueLoad : Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (value.toNat : Int))
    (descApart : ∀ i < 8, ∀ j < 48,
      s.regs.rsi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (valueApart : ∀ i < 1, ∀ j < 48,
      s.regs.rdx.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (next : Eventually (step e) P (prepared s descriptor value, base + 30)) :
    Eventually (step e) P (s, base) := by
  apply pushes_runs e base hc s P hm
  apply stack_runs e base hc
  apply abi_runs e base hc
  apply tags_runs e base hc _ descriptor value
  · change Mem.loadInt (savedMem s) s.regs.rsi.toBitVec 8 = _
    rw [Dispatch.saved_load s _ 8 descApart, descLoad]
  · change Mem.loadInt (savedMem s) s.regs.rdx.toBitVec 1 = _
    rw [Dispatch.saved_load s _ 1 valueApart, valueLoad]
  · exact next

@[simp] theorem prepared_memory (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) :
    (prepared s descriptor value).dmem = savedMem s := rfl

@[simp] theorem prepared_sp (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) :
    (prepared s descriptor value).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 264 := by
  simp only [prepared, tagsState, abiState, stackState, Dispatch.savedState,
    UInt64.toBitVec_ofBitVec]
  bv_omega

end SszX86.Measure

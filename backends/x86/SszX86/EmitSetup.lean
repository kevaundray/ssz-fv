import SszX86.EmitPush
import SszX86.DispatchMemory

namespace SszX86.Emit
open BoolCodec UintCodec

def stackState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 104)}
    status := memcpySubFlags s.regs.rsp.toBitVec 104}

def abiState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    r14 := s.regs.r8, r8 := s.regs.rcx, r12 := s.regs.rdx, rbx := s.regs.rdi}}

def tagsState (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec descriptor, rcx := UInt64.ofBitVec (value.setWidth 64)}}

def prepared (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) : MachineData :=
  tagsState (abiState (stackState (savedState s))) descriptor value

theorem stack_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (stackState s, base + 14)) :
    Eventually (step e) P (s, base + 10) := by
  emit_step 6 using hc
  simpa [stackState, memcpySubFlags, BitVec.take, BitVec.signed] using next

theorem abi_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (abiState s, base + 26)) :
    Eventually (step e) P (s, base + 14) := by
  emit_step 7 using hc
  emit_step 8 using hc
  emit_step 9 using hc
  emit_step 10 using hc
  simpa [abiState] using next

theorem tags_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8)
    (P : MachineState → Prop)
    (descLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (descriptor.toNat : Int))
    (valueLoad : Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (value.toNat : Int))
    (next : Eventually (step e) P (tagsState s descriptor value, base + 32)) :
    Eventually (step e) P (s, base + 26) := by
  have cast64 : BitVec.ofInt 64 (descriptor.toNat : Int) = descriptor := by bv_omega
  have cast8 : BitVec.ofInt 8 (value.toNat : Int) = value := by bv_omega
  emit_step 11 using hc
  simp only [MachineData.load, Effects.All, descLoad, cast64]
  emit_step 12 using hc
  simp only [MachineData.load, Effects.All, valueLoad, cast8]
  simpa [tagsState] using next

/-- The descriptor and value observations survive the six writes because only
actual writable saved-stack bytes must be disjoint from these reads. -/
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
    (next : Eventually (step e) P (prepared s descriptor value, base + 32)) :
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
    (prepared s descriptor value).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 152 := by
  simp only [prepared, tagsState, abiState, stackState, Dispatch.savedState,
    UInt64.toBitVec_ofBitVec]
  bv_omega

end SszX86.Emit

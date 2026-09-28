import SszX86.DispatchMemory

namespace SszX86.Dispatch
open BoolCodec UintCodec

def stackState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 312)}
    status := memcpySubFlags s.regs.rsp.toBitVec 312}

def abiState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rbx := s.regs.r8, r14 := s.regs.rcx, rbp := s.regs.rsi}}

def tagState (s : MachineData) (kind : Kind) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat kind.tag}}

def prepared (s : MachineData) (kind : Kind) : MachineData :=
  tagState (abiState (stackState (savedState s))) kind

theorem stack_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (stackState s, base + 17)) :
    Eventually (step e) P (s, base + 10) := by
  dispatch_step 6 using hc
  simpa [stackState, memcpySubFlags, BitVec.take, BitVec.signed] using next

theorem abi_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (abiState s, base + 26)) :
    Eventually (step e) P (s, base + 17) := by
  dispatch_step 7 using hc
  dispatch_step 8 using hc
  dispatch_step 9 using hc
  simpa [abiState] using next

theorem tag_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : Kind) (P : MachineState → Prop)
    (tag : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (kind.tag : Int))
    (next : Eventually (step e) P (tagState s kind, base + 29)) :
    Eventually (step e) P (s, base + 26) := by
  dispatch_step 10 using hc
  cases kind <;> simpa [MachineData.load, Effects.All, tag, tagState, Kind.tag] using next

theorem setup_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : Kind) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (tag : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (kind.tag : Int))
    (apart : ∀ i < 8, ∀ j < 48,
      s.regs.rsi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (next : Eventually (step e) P (prepared s kind, base + 29)) :
    Eventually (step e) P (s, base) := by
  apply pushes_runs e base hc s P hm
  apply stack_runs e base hc
  apply abi_runs e base hc
  apply tag_runs e base hc _ kind
  · change Mem.loadInt (savedMem s) s.regs.rsi.toBitVec 8 = _
    rw [saved_load s _ 8 apart, tag]
  · exact next

@[simp] theorem prepared_memory (s : MachineData) (kind : Kind) :
    (prepared s kind).dmem = savedMem s := rfl

@[simp] theorem prepared_sp (s : MachineData) (kind : Kind) :
    (prepared s kind).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 360 := by
  simp only [prepared, tagState, abiState, stackState, savedState, UInt64.toBitVec_ofBitVec]
  bv_omega

end SszX86.Dispatch

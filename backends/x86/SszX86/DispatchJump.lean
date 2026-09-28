import SszX86.DispatchSetup

namespace SszX86.Dispatch
open BoolCodec UintCodec

def tableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (tableAddress base)}}

def offsetState (s : MachineData) (kind : Kind) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat (106520 + kind.entry)}}

def addState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rax.toBitVec)}
    status := Udivti3.addFlags s.regs.rcx.toBitVec s.regs.rax.toBitVec}

def bodyState (s : MachineData) (base : Int64) (kind : Kind) : MachineData :=
  addState (offsetState (tableState (prepared s kind) base) kind)

theorem lea_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (tableState s base, base + 36)) :
    Eventually (step e) P (s, base + 29) := by
  have address : BitVec.ofInt 64 ((base + 36).toInt + (-106556)) = tableAddress base := by
    rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
    change (base.toBitVec + 36#64) + BitVec.ofInt 64 (-106556) = base.toBitVec - 106520#64
    bv_omega
  have normalized : BitVec.ofInt 64
      ((base.toInt + 36).bmod 18446744073709551616 + (-106556)) = tableAddress base := by
    simpa only [Int64.toInt_add, show (36 : Int64).toInt = 36 by decide] using address
  dispatch_step 11 using hc
  simpa [tableState, normalized] using next

theorem offset_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : Kind) (P : MachineState → Prop)
    (tag : s.regs.rax = UInt64.ofNat kind.tag)
    (address : s.regs.rcx.toBitVec = tableAddress base)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (offsetState s kind, base + 40)) :
    Eventually (step e) P (s, base + 36) := by
  have loaded := table_load s.dmem base table kind
  have indexed : BitVec.ofInt 64 (s.regs.rcx.toBitVec.toInt + s.regs.rax.toBitVec.toInt * 4) =
      tableAddress base + BitVec.ofNat 64 (4 * kind.tag) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
      address, tag, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    change BitVec.ofNat 64 kind.tag * 4#64 = 4#64 * BitVec.ofNat 64 kind.tag
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  dispatch_step 12 using hc
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed,
    offsetState, UInt64.toBitVec_ofNat', register] using next

theorem add_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (addState s, base + 43)) :
    Eventually (step e) P (s, base + 40) := by
  dispatch_step 13 using hc
  simpa [addState, Udivti3.addFlags, BitVec.take, BitVec.signed] using next

theorem indirect_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, Int64.ofBitVec s.regs.rax.toBitVec)) :
    Eventually (step e) P (s, base + 43) := by
  dispatch_step 14 using hc
  exact next

/-- Actual LEA, signed table load, ADD and indirect JMP. The selected target is
a conclusion from physical bytes and descriptor tag, never an entry premise. -/
theorem jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : Kind) (P : MachineState → Prop)
    (table : TableAt (savedMem s) base)
    (next : Eventually (step e) P (bodyState s base kind, base + Int64.ofNat kind.entry)) :
    Eventually (step e) P (prepared s kind, base + 29) := by
  apply lea_runs e base hc
  apply offset_runs e base hc _ kind _ rfl rfl table
  apply add_runs e base hc
  apply indirect_runs e base hc
  simpa only [bodyState, addState, offsetState, tableState, UInt64.toBitVec_ofBitVec,
    UInt64.toBitVec_ofNat', table_target, Int64.ofBitVec_toBitVec] using next

@[simp] theorem body_memory (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).dmem = savedMem s := rfl

@[simp] theorem body_sp (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 360 :=
  prepared_sp s kind

end SszX86.Dispatch

import SszX86.EmitTable
import SszX86.Udivti3Math

namespace SszX86.Emit
open BoolCodec

def tableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofBitVec (tableAddress base)}}

def offsetState (s : MachineData) (kind : TableKind) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofNat (92800 + kind.entry)}}

def addState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rcx := UInt64.ofBitVec (s.regs.rdx.toBitVec + s.regs.rcx.toBitVec)}
    status := Udivti3.addFlags s.regs.rdx.toBitVec s.regs.rcx.toBitVec}

def jumped (s : MachineData) (base : Int64) (kind : TableKind) : MachineData :=
  addState (offsetState (tableState s base) kind)

theorem lea_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (tableState s base, base + 247)) :
    Eventually (step e) P (s, base + 240) := by
  have address : BitVec.ofInt 64 ((base + 247).toInt + (-93047)) = tableAddress base := by
    rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
    change (base.toBitVec + 247#64) + BitVec.ofInt 64 (-93047) = base.toBitVec - 92800#64
    bv_omega
  have normalized : BitVec.ofInt 64
      ((base.toInt + 247).bmod 18446744073709551616 + (-93047)) = tableAddress base := by
    simpa only [Int64.toInt_add, show (247 : Int64).toInt = 247 by decide] using address
  have normalizedAdd : BitVec.ofInt 64 ((base.toInt + 247).bmod 18446744073709551616) +
      BitVec.ofInt 64 (-93047) = tableAddress base := by
    rw [← BitVec.ofInt_add]
    exact normalized
  emit_step 53 using hc
  let computed := BitVec.ofInt 64 ((base.toInt + 247).bmod 18446744073709551616) +
    BitVec.ofInt 64 (-93047)
  change Eventually (step e) P
    (({s with regs := {s.regs with rdx := UInt64.ofBitVec computed}} : MachineData), base + 247)
  rw [show computed = tableAddress base from normalizedAdd]
  exact next

theorem offset_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : TableKind) (P : MachineState → Prop)
    (tag : s.regs.rcx = UInt64.ofNat kind.index)
    (address : s.regs.rdx.toBitVec = tableAddress base)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (offsetState s kind, base + 251)) :
    Eventually (step e) P (s, base + 247) := by
  have loaded := table_load s.dmem base table kind
  have indexed : s.regs.rdx.toBitVec + s.regs.rcx.toBitVec * 4#64 =
      tableAddress base + BitVec.ofNat 64 (4 * kind.index) := by
    rw [address, tag, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    change BitVec.ofNat 64 kind.index * 4#64 = 4#64 * BitVec.ofNat 64 kind.index
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  emit_step 54 using hc
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl,
    offsetState, UInt64.toBitVec_ofNat', register] using next

theorem add_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (addState s, base + 254)) :
    Eventually (step e) P (s, base + 251) := by
  emit_step 55 using hc
  simpa [addState, Udivti3.addFlags, BitVec.take, BitVec.signed] using next

theorem indirect_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, Int64.ofBitVec s.regs.rcx.toBitVec)) :
    Eventually (step e) P (s, base + 254) := by
  emit_step 56 using hc
  exact next

/-- Linked bytes determine the target of the actual indirect JMP at254. -/
theorem jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (kind : TableKind) (P : MachineState → Prop)
    (tag : s.regs.rcx = UInt64.ofNat kind.index)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (jumped s base kind, base + Int64.ofNat kind.entry)) :
    Eventually (step e) P (s, base + 240) := by
  apply lea_runs e base hc
  apply offset_runs e base hc (tableState s base) kind _ tag rfl table
  apply add_runs e base hc
  apply indirect_runs e base hc
  simpa only [jumped, addState, offsetState, tableState, UInt64.toBitVec_ofBitVec,
    UInt64.toBitVec_ofNat', table_target, Int64.ofBitVec_toBitVec] using next

end SszX86.Emit

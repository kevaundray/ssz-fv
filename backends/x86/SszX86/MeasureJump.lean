import SszX86.MeasureTable
import SszX86.Udivti3Math

namespace SszX86.Measure
open SszNative.Serialize BoolCodec

def tableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rdi := UInt64.ofBitVec (tableAddress base)}}

def offsetState (s : MachineData) (desc : Desc) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofNat (89316 + bodyEntry desc)}}

def addState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rdx := UInt64.ofBitVec (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec)}
    status := Udivti3.addFlags s.regs.rdi.toBitVec s.regs.rdx.toBitVec}

def jumped (s : MachineData) (base : Int64) (desc : Desc) : MachineData :=
  addState (offsetState (tableState s base) desc)

theorem lea_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (tableState s base, base + 37)) :
    Eventually (step e) P (s, base + 30) := by
  have address : BitVec.ofInt 64 ((base + 37).toInt + (-89353)) = tableAddress base := by
    rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
    change (base.toBitVec + 37#64) + BitVec.ofInt 64 (-89353) = base.toBitVec - 89316#64
    bv_omega
  have normalized : BitVec.ofInt 64
      ((base.toInt + 37).bmod 18446744073709551616 + (-89353)) = tableAddress base := by
    simpa only [Int64.toInt_add, show (37 : Int64).toInt = 37 by decide] using address
  have normalizedAdd : BitVec.ofInt 64 ((base.toInt + 37).bmod 18446744073709551616) +
      BitVec.ofInt 64 (-89353) = tableAddress base := by
    rw [← BitVec.ofInt_add]
    exact normalized
  measure_step 11 using hc
  let computed := BitVec.ofInt 64 ((base.toInt + 37).bmod 18446744073709551616) +
    BitVec.ofInt 64 (-89353)
  change Eventually (step e) P
    (({s with regs := {s.regs with rdi := UInt64.ofBitVec computed}} : MachineData), base + 37)
  rw [show computed = tableAddress base from normalizedAdd]
  exact next

theorem offset_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (P : MachineState → Prop)
    (tag : s.regs.rdx = UInt64.ofNat (descTag desc))
    (address : s.regs.rdi.toBitVec = tableAddress base)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (offsetState s desc, base + 41)) :
    Eventually (step e) P (s, base + 37) := by
  have loaded := table_load s.dmem base table desc
  have indexed : s.regs.rdi.toBitVec + s.regs.rdx.toBitVec * 4#64 =
      tableAddress base + BitVec.ofNat 64 (4 * descTag desc) := by
    rw [address, tag, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    change BitVec.ofNat 64 (descTag desc) * 4#64 = 4#64 * BitVec.ofNat 64 (descTag desc)
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  measure_step 12 using hc
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl,
    offsetState, UInt64.toBitVec_ofNat', register] using next

theorem add_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (addState s, base + 44)) :
    Eventually (step e) P (s, base + 41) := by
  measure_step 13 using hc
  simpa [addState, Udivti3.addFlags, BitVec.take, BitVec.signed] using next

theorem indirect_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, Int64.ofBitVec s.regs.rdx.toBitVec)) :
    Eventually (step e) P (s, base + 44) := by
  measure_step 14 using hc
  exact next

/-- The actual indirect JMP excludes every composite-table destination by the
original represented primitive Desc, without a body-entry execution premise. -/
theorem jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (P : MachineState → Prop)
    (tag : s.regs.rdx = UInt64.ofNat (descTag desc))
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (jumped s base desc, base + Int64.ofNat (bodyEntry desc))) :
    Eventually (step e) P (s, base + 30) := by
  apply lea_runs e base hc
  apply offset_runs e base hc (tableState s base) desc _ tag rfl table
  apply add_runs e base hc
  apply indirect_runs e base hc
  simpa only [jumped, addState, offsetState, tableState, UInt64.toBitVec_ofBitVec,
    UInt64.toBitVec_ofNat', table_target, Int64.ofBitVec_toBitVec] using next

end SszX86.Measure

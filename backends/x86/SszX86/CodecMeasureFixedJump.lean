import SszX86.CodecMeasureFixedDecode
import SszX86.CodecMeasureFixedTable
import SszX86.Udivti3Math

namespace SszX86.CodecMeasureFixed
open BoolCodec

def tableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (tableAddress base)}}

def offsetState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat (116208 + tableEntry tag)}}

def addState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rax.toBitVec)}
    status := Udivti3.addFlags s.regs.rcx.toBitVec s.regs.rax.toBitVec}

def jumped (s : MachineData) (base : Int64) (tag : Nat) : MachineData :=
  addState (offsetState (tableState s base) tag)

theorem lea_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (tableState s base, base + 40)) :
    Eventually (step e) P (s, base + 33) := by
  have address : BitVec.ofInt 64 ((base + 40).toInt + (-116248)) = tableAddress base := by
    rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
    change (base.toBitVec + 40#64) + BitVec.ofInt 64 (-116248) =
      base.toBitVec + BitVec.ofInt 64 (-116208)
    bv_omega
  have normalized : BitVec.ofInt 64
      ((base.toInt + 40).bmod 18446744073709551616 + (-116248)) = tableAddress base := by
    simpa only [Int64.toInt_add, show (40 : Int64).toInt = 40 by decide] using address
  have normalizedAdd : BitVec.ofInt 64 ((base.toInt + 40).bmod 18446744073709551616) +
      BitVec.ofInt 64 (-116248) = tableAddress base := by
    rw [← BitVec.ofInt_add]
    exact normalized
  codec_measure_fixed_step 12 using hc
  let computed := BitVec.ofInt 64 ((base.toInt + 40).bmod 18446744073709551616) +
    BitVec.ofInt 64 (-116248)
  change Eventually (step e) P
    (({s with regs := {s.regs with rcx := UInt64.ofBitVec computed}} : MachineData), base + 40)
  rw [show computed = tableAddress base from normalizedAdd]
  exact next

theorem offset_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (P : MachineState → Prop)
    (bound : tag < 12) (index : s.regs.rax = UInt64.ofNat tag)
    (address : s.regs.rcx.toBitVec = tableAddress base)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (offsetState s tag, base + 44)) :
    Eventually (step e) P (s, base + 40) := by
  have loaded := table_load s.dmem base table tag bound
  have indexed : s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 4#64 =
      tableAddress base + BitVec.ofNat 64 (4 * tag) := by
    rw [address, index, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  codec_measure_fixed_step 13 using hc
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed tag bound,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl,
    offsetState, UInt64.toBitVec_ofNat', register] using next

theorem add_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (addState s, base + 47)) :
    Eventually (step e) P (s, base + 44) := by
  codec_measure_fixed_step 14 using hc
  simpa [addState, Udivti3.addFlags, BitVec.take, BitVec.signed] using next

theorem indirect_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (s, Int64.ofBitVec s.regs.rax.toBitVec)) :
    Eventually (step e) P (s, base + 47) := by
  codec_measure_fixed_step 15 using hc
  exact next

/-- The actual LEA/MOVSLQ/ADD/JMP sequence resolves all twelve guarded slots. -/
theorem jump_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (P : MachineState → Prop)
    (bound : tag < 12) (index : s.regs.rax = UInt64.ofNat tag)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (jumped s base tag, base + Int64.ofNat (tableEntry tag))) :
    Eventually (step e) P (s, base + 33) := by
  apply lea_runs e base hc
  have preparedIndex : (tableState s base).regs.rax = UInt64.ofNat tag := by
    simpa only [tableState] using index
  have preparedAddress : (tableState s base).regs.rcx.toBitVec = tableAddress base := by
    simp only [tableState, UInt64.toBitVec_ofBitVec]
  have preparedTable : TableAt (tableState s base).dmem base := by
    simpa only [tableState] using table
  apply offset_runs e base hc (tableState s base) tag _ bound
    preparedIndex preparedAddress preparedTable
  apply add_runs e base hc
  apply indirect_runs e base hc
  simpa only [jumped, addState, offsetState, tableState, UInt64.toBitVec_ofBitVec,
    UInt64.toBitVec_ofNat', table_target, Int64.ofBitVec_toBitVec] using next

end SszX86.CodecMeasureFixed

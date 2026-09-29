import SszX86.CodecEmitSteps
import SszX86.CodecEmitTable
import SszX86.Udivti3Math

namespace SszX86.CodecEmit
open BoolCodec

def partsIndexed (s : MachineData) (kind : PartsKind) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat kind.index},
    status := Memcmp.subFlags (BitVec.ofNat 64 kind.index) 4#64}

theorem parts_index_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (kind : PartsKind) (P : MachineState → Prop)
    (tag : s.regs.rax = UInt64.ofNat (kind.index + 7))
    (next : Eventually (step e) P (partsIndexed s kind, base + 321)) :
    Eventually (step e) P (s, base + 307) := by
  cases kind <;>
    codec_emit_step 69 using code <;>
    simp only [tag, PartsKind.index] <;>
    codec_emit_step 70 using code <;>
    codec_emit_step 71 using code <;>
    simp_all [partsIndexed, PartsKind.index, Memcmp.subFlags,
      StatusFlags.from_result, BitVec.take, BitVec.signed, Effects.All]

def partsTableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (table1Address base)}}

def partsOffsetState (s : MachineData) (kind : PartsKind) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat (92784 + kind.entry)}}

def partsAddState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rax.toBitVec)}
    status := Udivti3.addFlags s.regs.rcx.toBitVec s.regs.rax.toBitVec}

def partsJumped (s : MachineData) (base : Int64) (kind : PartsKind) : MachineData :=
  partsAddState (partsOffsetState (partsTableState s base) kind)

theorem parts_lea_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (partsTableState s base, base + 328)) :
    Eventually (step e) P (s, base + 321) := by
  have address : BitVec.ofInt 64 ((base + 328).toInt + (-93112)) = table1Address base := by
    rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
    change (base.toBitVec + 328#64) + BitVec.ofInt 64 (-93112) =
      base.toBitVec + BitVec.ofInt 64 (-92784)
    bv_omega
  have normalized : BitVec.ofInt 64
      ((base.toInt + 328).bmod 18446744073709551616 + (-93112)) = table1Address base := by
    simpa only [Int64.toInt_add, show (328 : Int64).toInt = 328 by decide] using address
  have normalizedAdd : BitVec.ofInt 64 ((base.toInt + 328).bmod 18446744073709551616) +
      BitVec.ofInt 64 (-93112) = table1Address base := by
    rw [← BitVec.ofInt_add]
    exact normalized
  codec_emit_step 72 using code
  let computed := BitVec.ofInt 64 ((base.toInt + 328).bmod 18446744073709551616) +
    BitVec.ofInt 64 (-93112)
  change Eventually (step e) P
    (({s with regs := {s.regs with rcx := UInt64.ofBitVec computed}} : MachineData), base + 328)
  rw [show computed = table1Address base from normalizedAdd]
  exact next

theorem parts_offset_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (kind : PartsKind) (P : MachineState → Prop)
    (tag : s.regs.rax = UInt64.ofNat kind.index)
    (address : s.regs.rcx.toBitVec = table1Address base)
    (table : Table1At s.dmem base)
    (next : Eventually (step e) P (partsOffsetState s kind, base + 332)) :
    Eventually (step e) P (s, base + 328) := by
  have loaded := parts_table_load s.dmem base table kind
  have indexed : s.regs.rcx.toBitVec + s.regs.rax.toBitVec * 4#64 =
      table1Address base + BitVec.ofNat 64 (4 * kind.index) := by
    rw [address, tag, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    change BitVec.ofNat 64 kind.index * 4#64 = 4#64 * BitVec.ofNat 64 kind.index
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  codec_emit_step 73 using code
  simpa only [MachineData.load, Effects.All, indexed, loaded, parts_table_signed,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl,
    partsOffsetState, UInt64.toBitVec_ofNat', register] using next

theorem parts_add_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (partsAddState s, base + 335)) :
    Eventually (step e) P (s, base + 332) := by
  codec_emit_step 74 using code
  simpa [partsAddState, Udivti3.addFlags, BitVec.take, BitVec.signed] using next

/-- The real signed table entries determine every one of the five Seq shape
destinations, including distinct descriptor payload offsets for both containers. -/
theorem parts_jump_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (kind : PartsKind) (P : MachineState → Prop)
    (tag : s.regs.rax = UInt64.ofNat kind.index) (table : Table1At s.dmem base)
    (next : Eventually (step e) P
      (partsJumped s base kind, base + Int64.ofNat kind.entry)) :
    Eventually (step e) P (s, base + 321) := by
  apply parts_lea_runs e base code
  apply parts_offset_runs e base code (partsTableState s base) kind _ tag rfl table
  apply parts_add_runs e base code
  codec_emit_step 75 using code
  simpa only [partsJumped, partsAddState, partsOffsetState, partsTableState,
    UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', parts_table_target,
    Int64.ofBitVec_toBitVec] using next

end SszX86.CodecEmit

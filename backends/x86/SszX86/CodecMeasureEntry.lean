import SszX86.CodecMeasurePrimitiveBinding
import SszX86.CodecMeasureTable
import SszX86.MeasureEntryState

namespace SszX86.CodecMeasure
open BoolCodec UintCodec

def offsetState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofNat (89316 + tableEntry tag)}}

def jumped (s : MachineData) (base : Int64) (tag : Nat) : MachineData :=
  Measure.addState (offsetState (Measure.tableState s base) tag)

def entryState (s : MachineData) (base : Int64) (tag : Nat) (valueTag : BitVec 8) : MachineData :=
  jumped (Measure.prepared s (BitVec.ofNat 64 tag) valueTag) base tag

/-- The real MOVSLQ through every slot, not only the seven leaf destinations. -/
theorem offset_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Nat) (bound : tag < 13) (P : MachineState → Prop)
    (index : s.regs.rdx = UInt64.ofNat tag)
    (address : s.regs.rdi.toBitVec = tableAddress base)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (offsetState s tag, base + 41)) :
    Eventually (step e) P (s, base + 37) := by
  have loaded := table_load s.dmem base table tag bound
  have indexed : s.regs.rdi.toBitVec + s.regs.rdx.toBitVec * 4#64 =
      tableAddress base + BitVec.ofNat 64 (4 * tag) := by
    rw [address, index, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  measure_step 12 using code.primitive
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed tag bound,
    show Width.W32.bytes = 4 by rfl, show Width.W32.bits = 32 by rfl,
    offsetState, UInt64.toBitVec_ofNat', register] using next

/-- Linked table load, displacement addition and the actual indirect JMP. -/
theorem jump_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Nat) (bound : tag < 13) (P : MachineState → Prop)
    (index : s.regs.rdx = UInt64.ofNat tag)
    (table : TableAt s.dmem base)
    (next : Eventually (step e) P (jumped s base tag, base + Int64.ofNat (tableEntry tag))) :
    Eventually (step e) P (s, base + 30) := by
  apply Measure.lea_runs e base code.primitive
  apply offset_runs e base code (Measure.tableState s base) tag bound _ index rfl table
  apply Measure.add_runs e base code.primitive
  apply Measure.indirect_runs e base code.primitive
  simpa only [jumped, Measure.addState, offsetState, Measure.tableState,
    UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', table_target,
    Int64.ofBitVec_toBitVec] using next

/-- Original-state observations used by the common prologue. This is independent
of schema validity and of any branch, helper, or recursive execution result. -/
structure EntryOwned (s : MachineData) (base : Int64) (tag : Nat) (valueTag : BitVec 8) : Prop where
  tagBound : tag < 13
  «mapped» : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48
  descriptor : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (tag : Int)
  value : Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (valueTag.toNat : Int)
  descriptorApart : ∀ i < 8, ∀ j < 48,
    s.regs.rsi.toBitVec + BitVec.ofNat 64 i ≠ s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j
  valueApart : ∀ i < 1, ∀ j < 48,
    s.regs.rdx.toBitVec + BitVec.ofNat 64 i ≠ s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j
  table : TableAt s.dmem base
  tableApart : ∀ i < 52, ∀ j < 48,
    tableAddress base + BitVec.ofNat 64 i ≠ s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j

theorem EntryOwned.saved_table {s : MachineData} {base : Int64} {tag : Nat}
    {valueTag : BitVec 8} (owned : EntryOwned s base tag valueTag) :
    TableAt (Measure.savedMem s) base := by
  intro i hi
  have hi52 : i < 52 := by simpa only [tableBytes, List.length_cons, List.length_nil] using hi
  rw [Dispatch.saved_lookup s _ (fun j hj => owned.tableApart i hi52 j hj)]
  exact owned.table i hi

/-- Entry-to-dispatch for all thirteen physical tags. The caller continuation is
used only as CPS composition; `entry_runs` below has no future-state hypothesis. -/
theorem entry_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Nat) (valueTag : BitVec 8)
    (owned : EntryOwned s base tag valueTag) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (entryState s base tag valueTag, base + Int64.ofNat (tableEntry tag))) :
    Eventually (step e) P (s, base) := by
  apply Measure.setup_runs e base code.primitive s (BitVec.ofNat 64 tag) valueTag P owned.mapped
  · have bound : tag < 2 ^ 64 := by have := owned.tagBound; omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using owned.descriptor
  · exact owned.value
  · exact owned.descriptorApart
  · exact owned.valueApart
  · exact jump_runs e base code _ tag owned.tagBound P rfl owned.saved_table next

theorem entry_atBody (s : MachineData) (base : Int64) (tag : Nat) (valueTag : BitVec 8) :
    Measure.AtBody s (entryState s base tag valueTag) :=
  ⟨rfl, Measure.prepared_sp s (BitVec.ofNat 64 tag) valueTag, rfl, rfl, rfl, rfl, rfl⟩

theorem entry_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Nat) (valueTag : BitVec 8)
    (owned : EntryOwned s base tag valueTag) :
    Eventually (step e) (fun t =>
      t.2 = base + Int64.ofNat (tableEntry tag) ∧ Measure.AtBody s t.1 ∧
      t.1.regs.rax.toBitVec.setWidth 8 = valueTag) (s, base) := by
  apply entry_cps e base code s tag valueTag owned
  exact Eventually.done _ ⟨rfl, entry_atBody s base tag valueTag, by
    change (valueTag.setWidth 64).setWidth 8 = valueTag
    bv_omega⟩

end SszX86.CodecMeasure

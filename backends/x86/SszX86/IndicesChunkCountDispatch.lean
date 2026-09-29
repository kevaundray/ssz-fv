import SszX86.IndicesChunkCountExec

namespace SszX86.IndicesChunkCount
open Kraken.X64.Parser
open SszNative UintCodec

/-- Original .LJTI58_0 entries, indexed by the physical Desc discriminant. -/
def tableTarget (tag : Nat) : Nat :=
  match tag with
  | 0 | 1 | 12 => 35
  | 2 | 3 => 76
  | 4 | 5 => 55
  | 7 | 8 => 97
  | 10 => 219
  | _ => 141

def tableAddress (base : Int64) : BitVec 64 := base.toBitVec - 67524#64

/-- Signed i32 observations of the linked table, not an assumed chosen target. -/
def TableAt (m : DataMem) (base : Int64) : Prop :=
  ∀ tag : Fin 13,
    Mem.loadInt m (tableAddress base + BitVec.ofNat 64 (4 * tag.val)) 4 =
      some ((67524 + tableTarget tag.val : Nat) : Int)

private theorem table_signed (tag : Fin 13) :
    (BitVec.ofInt 32 ((67524 + tableTarget tag.val : Nat) : Int)).signExtend 64 =
      BitVec.ofNat 64 (67524 + tableTarget tag.val) := by
  have all : ∀ tag : Fin 13,
      (BitVec.ofInt 32 ((67524 + tableTarget tag.val : Nat) : Int)).signExtend 64 =
        BitVec.ofNat 64 (67524 + tableTarget tag.val) := by decide
  exact all tag

theorem table_target (base : Int64) (tag : Nat) :
    tableAddress base + BitVec.ofNat 64 (67524 + tableTarget tag) =
      (base + Int64.ofNat (tableTarget tag)).toBitVec := by
  change (base.toBitVec - 67524#64) + BitVec.ofNat 64 (67524 + tableTarget tag) =
    base.toBitVec + BitVec.ofNat 64 (tableTarget tag)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

def tableState (s : MachineData) (base : Int64) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (tableAddress base)}}

def offsetState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat (67524 + tableTarget tag)}}

def jumped (s : MachineData) (base : Int64) (tag : Nat)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (base + Int64.ofNat (tableTarget tag)).toBitVec,
    rcx := UInt64.ofBitVec (tableAddress base)}, status := flags}

theorem table_lea_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (tableState s base, base + 26)) :
    Eventually (step e) P (s, base + 19) := by
  have normalized : BitVec.ofInt 64
      ((base.toInt + 26).bmod 18446744073709551616 + (-67550)) =
      tableAddress base := by
    have address : BitVec.ofInt 64 ((base + 26).toInt + (-67550)) =
        tableAddress base := by
      rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
      change (base.toBitVec + 26#64) + BitVec.ofInt 64 (-67550) =
        base.toBitVec - 67524#64
      simp only [BitVec.add_assoc, BitVec.sub_eq_add_neg]
      rfl
    simpa only [Int64.toInt_add, show (26 : Int64).toInt = 26 by decide] using address
  indices_count_step 7 using code
  simpa [tableState, normalized] using next

theorem table_load_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Fin 13)
    (index : s.regs.rax = UInt64.ofNat tag.val)
    (address : s.regs.rcx.toBitVec = tableAddress base)
    (table : TableAt s.dmem base) (P : MachineState → Prop)
    (next : Eventually (step e) P (offsetState s tag.val, base + 30)) :
    Eventually (step e) P (s, base + 26) := by
  have indexed : BitVec.ofInt 64
      (s.regs.rcx.toBitVec.toInt + s.regs.rax.toBitVec.toInt * 4) =
      tableAddress base + BitVec.ofNat 64 (4 * tag.val) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
      address, index, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  indices_count_step 8 using code
  simpa only [MachineData.load, Effects.All, indexed, table tag,
    table_signed tag, offsetState, UInt64.toBitVec_ofNat', register] using next

/-- All four linked dispatch instructions execute; the indirect branch is not
replaced by a semantic dispatch assumption. -/
theorem table_jump_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (tag : Fin 13) (index : s.regs.rax = UInt64.ofNat tag.val)
    (table : TableAt s.dmem base) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (jumped s base tag.val flags, base + Int64.ofNat (tableTarget tag.val))) :
    Eventually (step e) P (s, base + 19) := by
  apply table_lea_cps e base code s P
  apply table_load_cps e base code _ tag index rfl table P
  indices_count_step 9 using code
  indices_count_step 10 using code
  simpa only [jumped, tableState, offsetState, UInt64.toBitVec_ofNat',
    UInt64.toBitVec_ofBitVec, table_target, Int64.ofBitVec_toBitVec,
    BitVec.add_comm] using next _

end SszX86.IndicesChunkCount

import SszX86.IndicesElementTypeExec

namespace SszX86.IndicesElementType
open Kraken.X64.Parser
open SszNative UintCodec

/-- Entry order in the linked .LJTI61_0 and .LJTI61_1 tables. The final two
entries exist only for Position and select ordinary/progressive Field slices. -/
def tableTarget (index : Nat) : Nat :=
  match index with
  | 0 | 1 => 90
  | 2 | 3 | 4 => 61
  | 5 | 6 => 76
  | 7 => 121
  | 8 => 213
  | _ => 206

def tableDistance (position : Bool) : Nat := if position then 69104 else 69136

def tableAddress (base : Int64) (position : Bool) : BitVec 64 :=
  base.toBitVec - BitVec.ofNat 64 (tableDistance position)

/-- The actual original little-endian signed-i32 observations. No code-pointer
or chosen-target premise replaces MOVSLQ: that instruction is executed below. -/
def TableAt (m : DataMem) (base : Int64) : Prop :=
  ∀ position : Bool, ∀ index : Fin (if position then 10 else 8),
    Mem.loadInt m (tableAddress base position + BitVec.ofNat 64 (4 * index.val)) 4 =
      some ((tableDistance position + tableTarget index.val : Nat) : Int)

private theorem signed_table_entries : ∀ position : Bool,
    ∀ index : Fin (if position then 10 else 8),
    (BitVec.ofInt 32 ((tableDistance position + tableTarget index.val : Nat) : Int)).signExtend 64 =
      BitVec.ofNat 64 (tableDistance position + tableTarget index.val) := by decide

theorem table_target (base : Int64) (position : Bool) (index : Nat) :
    tableAddress base position + BitVec.ofNat 64 (tableDistance position + tableTarget index) =
      (base + Int64.ofNat (tableTarget index)).toBitVec := by
  change (base.toBitVec - BitVec.ofNat 64 (tableDistance position)) +
      BitVec.ofNat 64 (tableDistance position + tableTarget index) =
      base.toBitVec + BitVec.ofNat 64 (tableTarget index)
  rw [BitVec.ofNat_add]
  bv_omega

def tableState (s : MachineData) (base : Int64) (position : Bool) : MachineData :=
  {s with regs := {s.regs with rcx := UInt64.ofBitVec (tableAddress base position)}}

def offsetState (s : MachineData) (position : Bool) (index : Nat) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofNat (tableDistance position + tableTarget index)}}

def jumped (s : MachineData) (base : Int64) (position : Bool) (index : Nat)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (base + Int64.ofNat (tableTarget index)).toBitVec,
    rcx := UInt64.ofBitVec (tableAddress base position)}, status := flags}

theorem table_lea_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (position : Bool) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (tableState s base position, base + if position then 52 else 26)) :
    Eventually (step e) P (s, base + if position then 45 else 19) := by
  cases position with
  | false =>
    have normalized : BitVec.ofInt 64
        ((base.toInt + 26).bmod 18446744073709551616 + (-69162)) =
        tableAddress base false := by
      have address : BitVec.ofInt 64 ((base + 26).toInt + (-69162)) =
          tableAddress base false := by
        rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
        change (base.toBitVec + 26#64) + BitVec.ofInt 64 (-69162) =
          base.toBitVec - 69136#64
        bv_omega
      simpa only [Int64.toInt_add, show (26 : Int64).toInt = 26 by decide] using address
    indices_element_step 6 using hc
    simpa [tableState, normalized] using next
  | true =>
    have normalized : BitVec.ofInt 64
        ((base.toInt + 52).bmod 18446744073709551616 + (-69156)) =
        tableAddress base true := by
      have address : BitVec.ofInt 64 ((base + 52).toInt + (-69156)) =
          tableAddress base true := by
        rw [BitVec.ofInt_add, BitVec.ofInt_int64ToInt]
        change (base.toBitVec + 52#64) + BitVec.ofInt 64 (-69156) =
          base.toBitVec - 69104#64
        bv_omega
      simpa only [Int64.toInt_add, show (52 : Int64).toInt = 52 by decide] using address
    indices_element_step 13 using hc
    simpa [tableState, normalized] using next

theorem table_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (position : Bool) (index : Fin (if position then 10 else 8))
    (tag : s.regs.rax = UInt64.ofNat index.val)
    (address : s.regs.rcx.toBitVec = tableAddress base position)
    (table : TableAt s.dmem base) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (offsetState s position index.val, base + if position then 56 else 30)) :
    Eventually (step e) P (s, base + if position then 52 else 26) := by
  have loaded := table position index
  have indexed : BitVec.ofInt 64 (s.regs.rcx.toBitVec.toInt + s.regs.rax.toBitVec.toInt * 4) =
      tableAddress base position + BitVec.ofNat 64 (4 * index.val) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
      address, tag, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  cases position with
  | false =>
    indices_element_step 7 using hc
    simpa only [MachineData.load, Effects.All, indexed, loaded,
      signed_table_entries false index, offsetState, UInt64.toBitVec_ofNat', register] using next
  | true =>
    indices_element_step 14 using hc
    simpa only [MachineData.load, Effects.All, indexed, loaded,
      signed_table_entries true index, offsetState, UInt64.toBitVec_ofNat', register] using next

/-- Executes the complete LEA/MOVSLQ/ADD/JMP sequence from either real table. -/
theorem table_jump_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (position : Bool) (index : Fin (if position then 10 else 8))
    (tag : s.regs.rax = UInt64.ofNat index.val) (table : TableAt s.dmem base)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (jumped s base position index.val flags, base + Int64.ofNat (tableTarget index.val))) :
    Eventually (step e) P (s, base + if position then 45 else 19) := by
  apply table_lea_cps e base hc s position P
  apply table_load_cps e base hc _ position index tag rfl table P
  cases position with
  | false =>
    indices_element_step 8 using hc
    indices_element_step 9 using hc
    simpa only [jumped, tableState, offsetState, UInt64.toBitVec_ofNat',
      UInt64.toBitVec_ofBitVec, table_target, Int64.ofBitVec_toBitVec,
      BitVec.add_comm] using next _
  | true =>
    indices_element_step 15 using hc
    indices_element_step 16 using hc
    simpa only [jumped, tableState, offsetState, UInt64.toBitVec_ofNat',
      UInt64.toBitVec_ofBitVec, table_target, Int64.ofBitVec_toBitVec,
      BitVec.add_comm] using next _

def indexed (s : MachineData) (tag : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (BitVec.ofNat 64 tag - 2)},
    status := flags}

/-- Both actual ADD -2/CMP/JA guards are proved on all thirteen physical Desc
tags. Inactive PathStep payload is never inspected on a rejected descriptor. -/
theorem index_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Fin 13) (position : Bool)
    (tagged : s.regs.rax = UInt64.ofNat tag.val) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (indexed s tag.val flags,
      if 2 ≤ tag.val ∧ tag.val < (if position then 12 else 10)
      then base + if position then 45 else 19 else base + 135)) :
    Eventually (step e) P (s, base + if position then 35 else 9) := by
  have target := hc.targets ("indices_element_type_u135", 135) (by decide)
  have choices : tag.val = 0 ∨ tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨
      tag.val = 4 ∨ tag.val = 5 ∨ tag.val = 6 ∨ tag.val = 7 ∨ tag.val = 8 ∨
      tag.val = 9 ∨ tag.val = 10 ∨ tag.val = 11 ∨ tag.val = 12 := by
    have := tag.isLt
    omega
  cases position with
  | false =>
    indices_element_step 3 using hc
    simp only [tagged]
    indices_element_step 4 using hc
    indices_element_step 5 using hc
    rcases choices with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simpa [indexed, h, StatusFlags.from_result, NatCompare.cf_sub,
        Effects.All, target] using next _
  | true =>
    indices_element_step 10 using hc
    simp only [tagged]
    indices_element_step 11 using hc
    indices_element_step 12 using hc
    rcases choices with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simpa [indexed, h, StatusFlags.from_result, NatCompare.cf_sub,
        Effects.All, target] using next _

def dispatchPc (tag : Nat) (position : Bool) : Nat :=
  if 2 ≤ tag ∧ tag < (if position then 12 else 10) then tableTarget (tag - 2) else 135

def dispatched (s : MachineData) (a c : UInt64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := a, rcx := c}, status := flags}

/-- The original tag loads, range guard, signed table load and indirect jump,
with no supplied future target or assumed initialized dispatch state. -/
theorem dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Fin 13) (pathTag : BitVec 64)
    (desc : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (tag.val : Int))
    (path : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 = some (pathTag.toNat : Int))
    (table : TableAt s.dmem base) (P : MachineState → Prop)
    (next : ∀ a c flags, Eventually (step e) P
      (dispatched s a c flags, base + Int64.ofNat (dispatchPc tag.val (pathTag == 0)))) :
    Eventually (step e) P (s, base) := by
  have tagBound : tag.val < 2^64 := by have := tag.isLt; omega
  have descWord : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 =
      some ((BitVec.ofNat 64 tag.val).toNat : Int) := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tagBound] using desc
  apply entry_cps e base hc s pathTag (BitVec.ofNat 64 tag.val) path descWord P
  intro flags
  let position := pathTag == 0
  have pc : (if pathTag = 0 then base + 35 else base + 9) =
      base + if position then 35 else 9 := by
    simp only [position, beq_iff_eq]
    split <;> rfl
  rw [pc]
  apply index_cps e base hc _ tag position rfl P
  intro fl
  by_cases valid : 2 ≤ tag.val ∧ tag.val < (if position then 12 else 10)
  · simp only [valid, ↓reduceIte]
    let index : Fin (if position then 10 else 8) := ⟨tag.val - 2, by
      cases h : position <;> simp_all <;> omega⟩
    have indexedTag : (indexed
        {s with regs := {s.regs with rax := UInt64.ofBitVec (BitVec.ofNat 64 tag.val)},
          status := flags} tag.val fl).regs.rax = UInt64.ofNat index.val := by
      apply UInt64.toBitVec_inj.1
      change BitVec.ofNat 64 tag.val - 2 = BitVec.ofNat 64 (tag.val - 2)
      bv_omega
    apply table_jump_cps e base hc _ position index indexedTag table P
    intro fl'
    simpa [jumped, indexed, dispatched, dispatchPc, valid, index, position] using next
      (UInt64.ofBitVec (base + Int64.ofNat (tableTarget (tag.val - 2))).toBitVec)
      (UInt64.ofBitVec (tableAddress base position)) fl'
  · simp only [valid, ↓reduceIte]
    simpa [indexed, dispatched, dispatchPc, valid, position] using next
      (UInt64.ofBitVec (BitVec.ofNat 64 tag.val - 2)) s.regs.rcx fl

end SszX86.IndicesElementType

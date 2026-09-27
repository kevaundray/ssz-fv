import SszX86.MemmoveImpl
import SszX86.MemcpyExec

namespace SszX86

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev memmoveStep (base : Int64) := @step1 (memmoveLayout base) (memmoveExecutable base)

macro "memmove_fetch" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [memmoveExecutable, memmoveLayout, memmoveProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses, Int64.add_assoc]))

macro "memmove_label" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [Executable.labels, memmoveExecutable, memmoveLayout, memmoveProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.withAddresses, Int64.add_assoc]))

private theorem sub_address (x : BitVec 64) (n : Int) :
    BitVec.ofInt 64 ((x.toInt - n).bmod 18446744073709551616) =
      x - BitVec.ofInt 64 n := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_sub]

private theorem fetch0 (base : Int64) : (memmoveExecutable base).directivesAtAddress base =
    (parse("movq %rdi, %rax")).zip [3] := by memmove_fetch
private theorem fetch3 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 3) =
    (parse("testq %rdx, %rdx")).zip [3] := by memmove_fetch
private theorem fetch6 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 6) =
    (parse("jz move_forward_done")).zip [2] := by memmove_fetch
private theorem fetch8 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 8) =
    (parse("cmpq %rsi, %rdi")).zip [3] := by memmove_fetch
private theorem fetch11 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 11) =
    (parse("je move_forward_done")).zip [2] := by memmove_fetch
private theorem fetch13 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 13) =
    (parse("ja move_backward")).zip [2] := by memmove_fetch
private theorem fetch15 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 15) =
    (parse("cmpq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch19 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 19) =
    (parse("jb move_forward_tail")).zip [2] := by memmove_fetch
private theorem fetch21 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 21) =
    (parse("move_forward_bulk: movq (%rsi), %r8")).zip [0,3] := by memmove_fetch
private theorem fetch24 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 24) =
    (parse("movq %r8, (%rdi)")).zip [3] := by memmove_fetch
private theorem fetch27 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 27) =
    (parse("addq $8, %rsi")).zip [4] := by memmove_fetch
private theorem fetch31 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 31) =
    (parse("addq $8, %rdi")).zip [4] := by memmove_fetch
private theorem fetch35 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 35) =
    (parse("subq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch39 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 39) =
    (parse("cmpq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch43 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 43) =
    (parse("jae move_forward_bulk")).zip [2] := by memmove_fetch
private theorem fetch45 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 45) =
    (parse("move_forward_tail: testq %rdx, %rdx")).zip [0,3] := by memmove_fetch
private theorem fetch48 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 48) =
    (parse("jz move_forward_done")).zip [2] := by memmove_fetch
private theorem fetch50 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 50) =
    (parse("move_forward_byte: movb (%rsi), %cl")).zip [0,2] := by memmove_fetch
private theorem fetch52 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 52) =
    (parse("movb %cl, (%rdi)")).zip [2] := by memmove_fetch
private theorem fetch54 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 54) =
    (parse("addq $1, %rsi")).zip [4] := by memmove_fetch
private theorem fetch58 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 58) =
    (parse("addq $1, %rdi")).zip [4] := by memmove_fetch
private theorem fetch62 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 62) =
    (parse("subq $1, %rdx")).zip [4] := by memmove_fetch
private theorem fetch66 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 66) =
    (parse("jnz move_forward_byte")).zip [2] := by memmove_fetch
private theorem fetch68 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 68) =
    (parse("move_forward_done: ret")).zip [0,1] := by memmove_fetch
private theorem fetch69 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 69) =
    (parse("move_backward: addq %rdx, %rsi")).zip [0,3] := by memmove_fetch
private theorem fetch72 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 72) =
    (parse("addq %rdx, %rdi")).zip [3] := by memmove_fetch
private theorem fetch75 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 75) =
    (parse("cmpq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch79 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 79) =
    (parse("jb move_backward_tail")).zip [2] := by memmove_fetch
private theorem fetch81 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 81) =
    (parse("move_backward_bulk: subq $8, %rsi")).zip [0,4] := by memmove_fetch
private theorem fetch85 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 85) =
    (parse("subq $8, %rdi")).zip [4] := by memmove_fetch
private theorem fetch89 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 89) =
    (parse("movq (%rsi), %r8")).zip [3] := by memmove_fetch
private theorem fetch92 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 92) =
    (parse("movq %r8, (%rdi)")).zip [3] := by memmove_fetch
private theorem fetch95 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 95) =
    (parse("subq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch99 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 99) =
    (parse("cmpq $8, %rdx")).zip [4] := by memmove_fetch
private theorem fetch103 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 103) =
    (parse("jae move_backward_bulk")).zip [2] := by memmove_fetch
private theorem fetch105 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 105) =
    (parse("move_backward_tail: testq %rdx, %rdx")).zip [0,3] := by memmove_fetch
private theorem fetch108 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 108) =
    (parse("jz move_backward_done")).zip [2] := by memmove_fetch
private theorem fetch110 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 110) =
    (parse("move_backward_byte: subq $1, %rsi")).zip [0,4] := by memmove_fetch
private theorem fetch114 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 114) =
    (parse("subq $1, %rdi")).zip [4] := by memmove_fetch
private theorem fetch118 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 118) =
    (parse("movb (%rsi), %cl")).zip [2] := by memmove_fetch
private theorem fetch120 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 120) =
    (parse("movb %cl, (%rdi)")).zip [2] := by memmove_fetch
private theorem fetch122 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 122) =
    (parse("subq $1, %rdx")).zip [4] := by memmove_fetch
private theorem fetch126 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 126) =
    (parse("jnz move_backward_byte")).zip [2] := by memmove_fetch
private theorem fetch128 (base : Int64) : (memmoveExecutable base).directivesAtAddress (base + 128) =
    (parse("move_backward_done: ret")).zip [0,1] := by memmove_fetch
private theorem label_move_forward_bulk (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_forward_bulk" = base + 21 := by memmove_label
private theorem label_move_forward_tail (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_forward_tail" = base + 45 := by memmove_label
private theorem label_move_forward_byte (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_forward_byte" = base + 50 := by memmove_label
private theorem label_move_forward_done (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_forward_done" = base + 68 := by memmove_label
private theorem label_move_backward (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_backward" = base + 69 := by memmove_label
private theorem label_move_backward_bulk (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_backward_bulk" = base + 81 := by memmove_label
private theorem label_move_backward_tail (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_backward_tail" = base + 105 := by memmove_label
private theorem label_move_backward_byte (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_backward_byte" = base + 110 := by memmove_label
private theorem label_move_backward_done (base : Int64) : (Executable.labels (memmoveExecutable base)).label "move_backward_done" = base + 128 := by memmove_label

/-- Endpoint registers may wrap; the memory invariant only permits nonwrapping
actual byte accesses. Backward loads use the decremented endpoint. -/
def memmoveAddr (back : Bool) (p : BitVec 64) (k : Nat) : BitVec 64 :=
  if back then p - BitVec.ofNat 64 k else p

def memmoveAdvance (back : Bool) (p : BitVec 64) (k : Nat) : BitVec 64 :=
  if back then p - BitVec.ofNat 64 k else p + BitVec.ofNat 64 k

def memmoveBulkState (back : Bool) (s : MachineData) (v : Int) : MachineData :=
  { s with
    regs := { s.regs with
      r8 := UInt64.ofBitVec (BitVec.ofInt 64 v)
      rsi := UInt64.ofBitVec (memmoveAdvance back s.regs.rsi.toBitVec 8)
      rdi := UInt64.ofBitVec (memmoveAdvance back s.regs.rdi.toBitVec 8)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 8) }
    status := memcpySubFlags (s.regs.rdx.toBitVec - 8) 8
    dmem := Mem.storeInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 8)
      8 (BitVec.ofInt 64 v).toInt }

def memmoveByteState (back : Bool) (s : MachineData) (v : Int) : MachineData :=
  { s with
    regs := { s.regs with
      rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec.replaceLow (BitVec.ofInt 8 v))
      rsi := UInt64.ofBitVec (memmoveAdvance back s.regs.rsi.toBitVec 1)
      rdi := UInt64.ofBitVec (memmoveAdvance back s.regs.rdi.toBitVec 1)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 1) }
    status := memcpySubFlags s.regs.rdx.toBitVec 1
    dmem := Mem.storeInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 1)
      1 (BitVec.ofInt 8 v).toInt }

def memmoveBulkPc (base : Int64) (back : Bool) : Int64 :=
  if back then base + 81 else base + 21

def memmoveTailPc (base : Int64) (back : Bool) : Int64 :=
  if back then base + 105 else base + 45

def memmoveBytePc (base : Int64) (back : Bool) : Int64 :=
  if back then base + 110 else base + 50

def memmoveRetPc (base : Int64) (back : Bool) : Int64 :=
  if back then base + 128 else base + 68

/-- Memmove has exactly the same register clobber set as the checked memcpy. -/
theorem memmoveBulk_frame (back : Bool) (s : MachineData) (v : Int) :
    MemcpyFrame s (memmoveBulkState back s v) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [memmoveBulkState, Reg64s.get64]

theorem memmoveByte_frame (back : Bool) (s : MachineData) (v : Int) :
    MemcpyFrame s (memmoveByteState back s v) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [memmoveByteState, Reg64s.get64]

macro "memmove_step" : tactic => `(tactic|
  (apply step_cps
   simp (config := {instances := true}) [memmoveStep, step1, Executable.step,
     fetch0, fetch3, fetch6, fetch8, fetch11, fetch13, fetch15, fetch19, fetch21, fetch24, fetch27, fetch31, fetch35, fetch39, fetch43, fetch45, fetch48, fetch50, fetch52, fetch54, fetch58, fetch62, fetch66, fetch68, fetch69, fetch72, fetch75, fetch79, fetch81, fetch85, fetch89, fetch92, fetch95, fetch99, fetch103, fetch105, fetch108, fetch110, fetch114, fetch118, fetch120, fetch122, fetch126, fetch128,
     List.zip, Directives.interp, Directive.interp, Instr.interp,
     Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
     AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
     MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
     Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
     BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
     BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
     label_move_forward_bulk, label_move_forward_tail, label_move_forward_byte, label_move_forward_done, label_move_backward, label_move_backward_bulk, label_move_backward_tail, label_move_backward_byte, label_move_backward_done, Int64.add_assoc]))

/-- A complete chunk is loaded before its first store, in either direction. -/
theorem memmove_bulk_runs (base : Int64) (back : Bool) (s : MachineData)
    (v old : Int) (P : MachineState → Prop)
    (hs : Mem.loadInt s.dmem (memmoveAddr back s.regs.rsi.toBitVec 8) 8 = some v)
    (hd : Mem.loadInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 8) 8 = some old)
    (hp : Eventually (memmoveStep base) P
      (memmoveBulkState back s v,
        if (memmoveBulkState back s v).status.cf then memmoveTailPc base back
        else memmoveBulkPc base back)) :
    Eventually (memmoveStep base) P (s, memmoveBulkPc base back) := by
  cases back
  · change Eventually (memmoveStep base) P (s, base + 21)
    simp only [memmoveAddr, Bool.false_eq_true, ite_false] at hs hd
    memmove_step
    simp only [MachineData.load, Effects.All, hs]
    memmove_step
    simp only [MachineData.store, Effects.All, hd]
    memmove_step
    memmove_step
    memmove_step
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmoveBulkState, memmoveAddr, memmoveAdvance, memmoveTailPc,
        memmoveBulkPc, memcpySubFlags, StatusFlags.from_result,
        BitVec.take, BitVec.signed, UInt64.add_comm, Effects.All]
  · change Eventually (memmoveStep base) P (s, base + 81)
    simp only [memmoveAddr, ite_true] at hs hd
    memmove_step
    memmove_step
    memmove_step
    simp [MachineData.load, sub_address, hs, Effects.All]
    memmove_step
    simp [MachineData.store, sub_address, hd, Effects.All]
    memmove_step
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmoveBulkState, memmoveAddr, memmoveAdvance, memmoveTailPc,
        memmoveBulkPc, memcpySubFlags, StatusFlags.from_result,
        BitVec.take, BitVec.signed, Effects.All]

private theorem low_byte {w : Nat} (hi : BitVec w) (v : Int) :
    ((hi ++ BitVec.ofInt 8 v).toNat : Int).bmod 256 = v.bmod 256 := by
  have h := congrArg BitVec.toInt
    (BitVec.setWidth_append_eq_right (a := hi) (b := BitVec.ofInt 8 v))
  simpa using h

theorem memmove_byte_runs (base : Int64) (back : Bool) (s : MachineData)
    (v old : Int) (P : MachineState → Prop)
    (hs : Mem.loadInt s.dmem (memmoveAddr back s.regs.rsi.toBitVec 1) 1 = some v)
    (hd : Mem.loadInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 1) 1 = some old)
    (hp : Eventually (memmoveStep base) P
      (memmoveByteState back s v,
        if (memmoveByteState back s v).status.zf then memmoveRetPc base back
        else memmoveBytePc base back)) :
    Eventually (memmoveStep base) P (s, memmoveBytePc base back) := by
  cases back
  · change Eventually (memmoveStep base) P (s, base + 50)
    simp only [memmoveAddr, Bool.false_eq_true, ite_false] at hs hd
    memmove_step
    simp only [MachineData.load, Effects.All, hs]
    memmove_step
    simp only [MachineData.store, Effects.All, hd]
    memmove_step
    memmove_step
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmoveByteState, memmoveAddr, memmoveAdvance, memmoveRetPc,
        memmoveBytePc, memcpySubFlags, StatusFlags.from_result,
        BitVec.replaceLow, BitVec.drop, BitVec.take, BitVec.signed,
        UInt64.add_comm, Effects.All, low_byte]
  · change Eventually (memmoveStep base) P (s, base + 110)
    simp only [memmoveAddr, ite_true] at hs hd
    memmove_step
    memmove_step
    memmove_step
    simp [MachineData.load, sub_address, hs, Effects.All]
    memmove_step
    simp [MachineData.store, sub_address, hd, Effects.All]
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmoveByteState, memmoveAddr, memmoveAdvance, memmoveRetPc,
        memmoveBytePc, memcpySubFlags, StatusFlags.from_result,
        BitVec.replaceLow, BitVec.drop, BitVec.take, BitVec.signed,
        Effects.All, low_byte]

/-- TEST's undefined AF is quantified, never fixed by the refinement. -/
theorem memmove_tail_runs (base : Int64) (back : Bool) (s : MachineData)
    (P : MachineState → Prop)
    (hp : ∀ af, Eventually (memmoveStep base) P
      (memcpyTestState s af, if s.regs.rdx.toBitVec == 0 then memmoveRetPc base back
        else memmoveBytePc base back)) :
    Eventually (memmoveStep base) P (s, memmoveTailPc base back) := by
  cases back
  · have next (af : Bool) : Eventually (memmoveStep base) P
        (memcpyTestState s af, base + 48) := by
      unfold memcpyTestState
      have hnext := hp af
      memmove_step
      split <;> rename_i hbranch
      all_goals simp_all (config := {instances := true})
        [memcpyTestState, memmoveRetPc, memmoveBytePc, StatusFlags.from_result, Effects.All]
    change Eventually (memmoveStep base) P (s, base + 45)
    memmove_step
    exact ⟨next false, next true⟩
  · have next (af : Bool) : Eventually (memmoveStep base) P
        (memcpyTestState s af, base + 108) := by
      unfold memcpyTestState
      have hnext := hp af
      memmove_step
      split <;> rename_i hbranch
      all_goals simp_all (config := {instances := true})
        [memcpyTestState, memmoveRetPc, memmoveBytePc, StatusFlags.from_result, Effects.All]
    change Eventually (memmoveStep base) P (s, base + 105)
    memmove_step
    exact ⟨next false, next true⟩

def memmoveEntryState (s : MachineData) (af : Bool) : MachineData :=
  memcpyTestState { s with regs := { s.regs with rax := s.regs.rdi } } af

theorem memmove_entry_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ af, Eventually (memmoveStep base) P
      (memmoveEntryState s af, if s.regs.rdx.toBitVec == 0 then base + 68 else base + 8)) :
    Eventually (memmoveStep base) P (s, base) := by
  have next (af : Bool) : Eventually (memmoveStep base) P
      (memmoveEntryState s af, base + 6) := by
    unfold memmoveEntryState memcpyTestState
    have hnext := hp af
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmoveEntryState, memcpyTestState, StatusFlags.from_result, Effects.All]
  memmove_step
  memmove_step
  exact ⟨next false, next true⟩

def memmoveCompareState (s : MachineData) : MachineData :=
  { s with status := memcpySubFlags s.regs.rdi.toBitVec s.regs.rsi.toBitVec }

theorem memmove_compare_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (memmoveStep base) P
      (memmoveCompareState s,
        if (memmoveCompareState s).status.zf then base + 68
        else if (memmoveCompareState s).status.cf then base + 15 else base + 69)) :
    Eventually (memmoveStep base) P (s, base + 8) := by
  memmove_step
  memmove_step
  split <;> rename_i hz
  · simp_all (config := {instances := true})
      [memmoveCompareState, memcpySubFlags, StatusFlags.from_result,
        BitVec.take, BitVec.signed, Effects.All]
  · memmove_step
    split <;> rename_i hc
    all_goals simp_all (config := {instances := true})
      [memmoveCompareState, memcpySubFlags, StatusFlags.from_result,
        BitVec.take, BitVec.signed, Effects.All]

/-- Only the backward path forms one-past endpoints. These are modular register
values, not a claim that the one-past address itself is mapped. -/
def memmovePrepareState (back : Bool) (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with
      rsi := if back then UInt64.ofBitVec (s.regs.rsi.toBitVec + s.regs.rdx.toBitVec)
        else s.regs.rsi
      rdi := if back then UInt64.ofBitVec (s.regs.rdi.toBitVec + s.regs.rdx.toBitVec)
        else s.regs.rdi }
    status := memcpySubFlags s.regs.rdx.toBitVec 8 }

theorem memmove_prepare_runs (base : Int64) (back : Bool) (s : MachineData)
    (P : MachineState → Prop)
    (hp : Eventually (memmoveStep base) P
      (memmovePrepareState back s,
        if (memmovePrepareState back s).status.cf then memmoveTailPc base back
        else memmoveBulkPc base back)) :
    Eventually (memmoveStep base) P (s, if back then base + 69 else base + 15) := by
  cases back
  · simp only [Bool.false_eq_true, ite_false]
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmovePrepareState, memmoveTailPc, memmoveBulkPc, memcpySubFlags,
        StatusFlags.from_result, BitVec.take, BitVec.signed, Effects.All]
  · simp only [ite_true]
    memmove_step
    memmove_step
    memmove_step
    memmove_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memmovePrepareState, memmoveTailPc, memmoveBulkPc, memcpySubFlags,
        StatusFlags.from_result, BitVec.take, BitVec.signed, UInt64.add_comm, Effects.All]

theorem memmove_prepare_frame (back : Bool) (s : MachineData) :
    MemcpyFrame s (memmovePrepareState back s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [memmovePrepareState, Reg64s.get64]

/-- Both physical RET instructions pop the real mapped stack slot. -/
theorem memmove_ret_runs (base : Int64) (back : Bool) (s : MachineData)
    (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({ s with regs := { s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra)) :
    Eventually (memmoveStep base) P (s, memmoveRetPc base back) := by
  cases back <;> unfold memmoveRetPc <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    memmove_step
    simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
    exact Eventually.done _ hp

/-- The unsigned direction flag is proved arithmetically, with no bitvector oracle. -/
theorem memmove_cf_compare (a b : BitVec 64) :
    (memcpySubFlags a b).cf = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memcpySubFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned]
  by_cases h : a < b
  · rw [BitVec.toNat_sub_of_lt h]
    have ha := a.isLt
    have hb := b.isLt
    change a.toNat < b.toNat at h
    omega
  · have hle : b ≤ a := by change b.toNat ≤ a.toNat; change ¬ a.toNat < b.toNat at h; omega
    rw [BitVec.toNat_sub_of_le hle]
    change b.toNat ≤ a.toNat at hle
    omega

theorem memmove_zf_compare (a b : BitVec 64) :
    (memcpySubFlags a b).zf = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memcpySubFlags, StatusFlags.from_result, beq_iff_eq, decide_eq_true_eq]
  change a - b = 0#64 ↔ a = b
  constructor
  · intro h
    have ha := congrArg (fun v : BitVec 64 => v + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using ha
  · rintro rfl
    exact BitVec.sub_self _

end SszX86

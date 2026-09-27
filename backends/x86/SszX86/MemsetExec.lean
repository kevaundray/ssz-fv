import SszX86.MemsetMemory
import SszX86.MemcpyExec

namespace SszX86

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev memsetStep (base : Int64) := @step1 (memsetLayout base) (memsetExecutable base)

macro "memset_fetch" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [memsetExecutable, memsetLayout, memsetProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses, Int64.add_assoc]))

macro "memset_label" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [Executable.labels, memsetExecutable, memsetLayout, memsetProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.withAddresses, Int64.add_assoc]))

private theorem fetch0 (base : Int64) : (memsetExecutable base).directivesAtAddress base =
    (parse("movq %rdi, %rax")).zip [3] := by memset_fetch
private theorem fetch3 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 3) =
    (parse("cmpq $8, %rdx")).zip [4] := by memset_fetch
private theorem fetch7 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 7) =
    (parse("jb tail44")).zip [2] := by memset_fetch
private theorem fetch9 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 9) =
    (parse("movzbl %sil, %r8d")).zip [4] := by memset_fetch
private theorem fetch13 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 13) =
    (parse("movabsq $0x0101010101010101, %r9")).zip [10] := by memset_fetch
private theorem fetch23 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 23) =
    (parse("imulq %r8, %r9")).zip [4] := by memset_fetch
private theorem fetch27 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 27) =
    (parse("bulk27: movq %r9, (%rdi)")).zip [0,3] := by memset_fetch
private theorem fetch30 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 30) =
    (parse("addq $8, %rdi")).zip [4] := by memset_fetch
private theorem fetch34 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 34) =
    (parse("subq $8, %rdx")).zip [4] := by memset_fetch
private theorem fetch38 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 38) =
    (parse("cmpq $8, %rdx")).zip [4] := by memset_fetch
private theorem fetch42 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 42) =
    (parse("jae bulk27")).zip [2] := by memset_fetch
private theorem fetch44 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 44) =
    (parse("tail44: testq %rdx, %rdx")).zip [0,3] := by memset_fetch
private theorem fetch47 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 47) =
    (parse("jz done62")).zip [2] := by memset_fetch
private theorem fetch49 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 49) =
    (parse("byte49: movb %sil, (%rdi)")).zip [0,3] := by memset_fetch
private theorem fetch52 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 52) =
    (parse("addq $1, %rdi")).zip [4] := by memset_fetch
private theorem fetch56 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 56) =
    (parse("subq $1, %rdx")).zip [4] := by memset_fetch
private theorem fetch60 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 60) =
    (parse("jnz byte49")).zip [2] := by memset_fetch
private theorem fetch62 (base : Int64) : (memsetExecutable base).directivesAtAddress (base + 62) =
    (parse("done62: ret")).zip [0,1] := by memset_fetch

private theorem labelBulk (base : Int64) : (Executable.labels (memsetExecutable base)).label "bulk27" = base + 27 := by memset_label
private theorem labelTail (base : Int64) : (Executable.labels (memsetExecutable base)).label "tail44" = base + 44 := by memset_label
private theorem labelByte (base : Int64) : (Executable.labels (memsetExecutable base)).label "byte49" = base + 49 := by memset_label
private theorem labelDone (base : Int64) : (Executable.labels (memsetExecutable base)).label "done62" = base + 62 := by memset_label

/-- All registers not used by this implementation, including every SysV
callee-saved register, are preserved. RSP is unchanged until RET itself. -/
def MemsetFrame (s t : MachineData) : Prop :=
  t.regs.rax = s.regs.rax ∧ t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms ∧
  (∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 →
    t.regs.get64 r = s.regs.get64 r)

theorem memsetFrame_refl (s : MachineData) : MemsetFrame s s := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem memsetFrame_trans {s t u : MachineData}
    (h : MemsetFrame s t) (h' : MemsetFrame t u) : MemsetFrame s u := by
  refine ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, ?_⟩
  intro r h1 h2 h3 h4
  exact (h'.2.2.2 r h1 h2 h3 h4).trans (h.2.2.2 r h1 h2 h3 h4)

def memsetByte (s : MachineData) : UInt8 :=
  UInt8.ofBitVec (s.regs.rsi.toBitVec.setWidth 8)

/-- Broadcast setup is reached only for a full word. Its outgoing flags are
irrelevant to the next store, so continuations cover every possible flag state. -/
def memsetSetupState (s : MachineData) (status : StatusFlags) : MachineData :=
  let low := (s.regs.rsi.toBitVec.setWidth 8).setWidth 64
  { s with
    regs := { s.regs with
      r8 := UInt64.ofBitVec low
      r9 := UInt64.ofBitVec (0x0101010101010101#64 * low) }
    status }

/-- State after the eight-byte loop body, including its final comparison. -/
def memsetBulkState (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 8)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 8) }
    status := memcpySubFlags (s.regs.rdx.toBitVec - 8) 8
    dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 8 s.regs.r9.toBitVec.toInt }

/-- State after the byte loop; RSI, including the fill byte, is unchanged. -/
def memsetByteState (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 1)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 1) }
    status := memcpySubFlags s.regs.rdx.toBitVec 1
    dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 1
      (s.regs.rsi.toBitVec.setWidth 8).toInt }

/-- TEST's undefined AF is universally quantified by Kraken's Effects.All. -/
def memsetTestState (s : MachineData) (af : Bool) : MachineData :=
  { s with status := .from_result s.regs.rdx.toBitVec { cf := false, af, of := false } }

theorem memsetBulk_frame (s : MachineData) :
    MemsetFrame s (memsetBulkState s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp_all [memsetBulkState, Reg64s.get64]

theorem memsetByte_frame (s : MachineData) :
    MemsetFrame s (memsetByteState s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp_all [memsetByteState, Reg64s.get64]

theorem memsetTest_frame (s : MachineData) (af : Bool) :
    MemsetFrame s (memsetTestState s af) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4
  cases r <;> simp [memsetTestState, Reg64s.get64]

macro "memset_step" : tactic => `(tactic|
  (apply step_cps
   simp (config := {instances := true}) [memsetStep, step1, Executable.step,
     fetch0, fetch3, fetch7, fetch9, fetch13, fetch23, fetch27, fetch30,
     fetch34, fetch38, fetch42, fetch44, fetch47, fetch49, fetch52, fetch56,
     fetch60, fetch62,
     List.zip, Directives.interp, Directive.interp, Instr.interp,
     Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
     AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
     MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
     Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
     BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
     BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
     labelBulk, labelTail, labelByte, labelDone, Int64.add_assoc]))

/-- Five real ISA instructions execute a complete bulk iteration. The next PC is
determined by the actual comparison carry flag, not a surrogate branch. -/
theorem memset_bulk_runs (base : Int64) (s : MachineData) (old : Int)
    (P : MachineState → Prop)
    (hd : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some old)
    (hp : Eventually (memsetStep base) P
      (memsetBulkState s, if (memsetBulkState s).status.cf then base + 44 else base + 27)) :
    Eventually (memsetStep base) P (s, base + 27) := by
  memset_step
  simp only [MachineData.store, Effects.All, hd]
  memset_step
  memset_step
  memset_step
  memset_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memsetBulkState, memcpySubFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed, UInt64.add_comm, Effects.All]

/-- Four real ISA instructions execute a complete byte iteration. -/
theorem memset_byte_runs (base : Int64) (s : MachineData) (old : Int)
    (P : MachineState → Prop)
    (hd : Mem.loadInt s.dmem s.regs.rdi.toBitVec 1 = some old)
    (hp : Eventually (memsetStep base) P
      (memsetByteState s, if (memsetByteState s).status.zf then base + 62 else base + 49)) :
    Eventually (memsetStep base) P (s, base + 49) := by
  memset_step
  simp only [MachineData.store, Effects.All, hd]
  memset_step
  memset_step
  memset_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memsetByteState, memcpySubFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed,
      UInt64.add_comm, Effects.All]

/-- TEST's undefined AF is universally quantified by Kraken's Effects.All. -/
theorem memset_tail_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ af, Eventually (memsetStep base) P
      (memsetTestState s af, if s.regs.rdx.toBitVec == 0 then base + 62 else base + 49)) :
    Eventually (memsetStep base) P (s, base + 44) := by
  have next (af : Bool) :
      Eventually (memsetStep base) P (memsetTestState s af, base + 47) := by
    unfold memsetTestState
    have hnext := hp af
    memset_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memsetTestState, StatusFlags.from_result, Effects.All]
  memset_step
  exact ⟨next false, next true⟩
/-- RET reads the mapped return slot, pops precisely eight bytes, and jumps
to the loaded return address. The slot itself is not written. -/
theorem memset_ret_runs (base : Int64) (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({ s with regs := { s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra)) :
    Eventually (memsetStep base) P (s, base + 62) := by
  memset_step
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact Eventually.done _ hp



/-- The first three instructions skip broadcast work for sub-word fills. -/
theorem memset_entry_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (memsetStep base) P
      (memcpyEntryState s, if (memcpyEntryState s).status.cf then base + 44 else base + 9)) :
    Eventually (memsetStep base) P (s, base) := by
  memset_step
  memset_step
  memset_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memcpyEntryState, memcpySubFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed, Effects.All]

/-- All undefined IMUL flags remain universally quantified. The loop does not
rely on them: its own arithmetic establishes the branch flags. -/
theorem memset_setup_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ status, Eventually (memsetStep base) P
      (memsetSetupState s status, base + 27)) :
    Eventually (memsetStep base) P (s, base + 9) := by
  memset_step
  memset_step
  memset_step
  simp_all (config := {instances := true})
    [memsetSetupState, memsetStep, BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]

end SszX86

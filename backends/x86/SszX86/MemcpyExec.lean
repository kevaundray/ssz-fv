import SszX86.MemcpyMemory

namespace SszX86

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev memcpyStep (base : Int64) := @step1 (memcpyLayout base) (memcpyExecutable base)

macro "memcpy_fetch" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [memcpyExecutable, memcpyLayout, memcpyProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses, Int64.add_assoc]))

macro "memcpy_label" : tactic => `(tactic|
  (dsimp (config := {instances := true})
     [Executable.labels, memcpyExecutable, memcpyLayout, memcpyProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.withAddresses, Int64.add_assoc]))

private theorem fetch0 (base : Int64) : (memcpyExecutable base).directivesAtAddress base =
    (parse("movq %rdi, %rax")).zip [3] := by memcpy_fetch
private theorem fetch3 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 3) =
    (parse("cmpq $8, %rdx")).zip [4] := by memcpy_fetch
private theorem fetch7 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 7) =
    (parse("jb copy_tail")).zip [2] := by memcpy_fetch
private theorem fetch9 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 9) =
    (parse("copy_bulk: movq (%rsi), %r8")).zip [0,3] := by memcpy_fetch
private theorem fetch12 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 12) =
    (parse("movq %r8, (%rdi)")).zip [3] := by memcpy_fetch
private theorem fetch15 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 15) =
    (parse("addq $8, %rsi")).zip [4] := by memcpy_fetch
private theorem fetch19 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 19) =
    (parse("addq $8, %rdi")).zip [4] := by memcpy_fetch
private theorem fetch23 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 23) =
    (parse("subq $8, %rdx")).zip [4] := by memcpy_fetch
private theorem fetch27 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 27) =
    (parse("cmpq $8, %rdx")).zip [4] := by memcpy_fetch
private theorem fetch31 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 31) =
    (parse("jae copy_bulk")).zip [2] := by memcpy_fetch
private theorem fetch33 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 33) =
    (parse("copy_tail: testq %rdx, %rdx")).zip [0,3] := by memcpy_fetch
private theorem fetch36 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 36) =
    (parse("jz copy_done")).zip [2] := by memcpy_fetch
private theorem fetch38 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 38) =
    (parse("copy_byte: movb (%rsi), %cl")).zip [0,2] := by memcpy_fetch
private theorem fetch40 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 40) =
    (parse("movb %cl, (%rdi)")).zip [2] := by memcpy_fetch
private theorem fetch42 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 42) =
    (parse("addq $1, %rsi")).zip [4] := by memcpy_fetch
private theorem fetch46 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 46) =
    (parse("addq $1, %rdi")).zip [4] := by memcpy_fetch
private theorem fetch50 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 50) =
    (parse("subq $1, %rdx")).zip [4] := by memcpy_fetch
private theorem fetch54 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 54) =
    (parse("jnz copy_byte")).zip [2] := by memcpy_fetch
private theorem fetch56 (base : Int64) : (memcpyExecutable base).directivesAtAddress (base + 56) =
    (parse("copy_done: ret")).zip [0,1] := by memcpy_fetch
private theorem labelBulk (base : Int64) : (Executable.labels (memcpyExecutable base)).label "copy_bulk" = base + 9 := by memcpy_label
private theorem labelTail (base : Int64) : (Executable.labels (memcpyExecutable base)).label "copy_tail" = base + 33 := by memcpy_label
private theorem labelByte (base : Int64) : (Executable.labels (memcpyExecutable base)).label "copy_byte" = base + 38 := by memcpy_label
private theorem labelDone (base : Int64) : (Executable.labels (memcpyExecutable base)).label "copy_done" = base + 56 := by memcpy_label
 
/-- Deterministic arithmetic flags; parity and auxiliary-carry flags are kept
as the ISA defines them, even though only carry and zero drive these loops. -/
def memcpySubFlags (a b : BitVec 64) : StatusFlags :=
  let v := a - b
  .from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }

/-- State after the eight-byte loop body, including its final comparison. -/
def memcpyBulkState (s : MachineData) (v : Int) : MachineData :=
  { s with
    regs := { s.regs with
      r8 := UInt64.ofBitVec (BitVec.ofInt 64 v)
      rsi := UInt64.ofBitVec (s.regs.rsi.toBitVec + 8)
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 8)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 8) }
    status := memcpySubFlags (s.regs.rdx.toBitVec - 8) 8
    dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 8 (BitVec.ofInt 64 v).toInt }

/-- State after the byte loop body. A write to CL preserves the high RCX bits. -/
def memcpyByteState (s : MachineData) (v : Int) : MachineData :=
  { s with
    regs := { s.regs with
      rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec.replaceLow (BitVec.ofInt 8 v))
      rsi := UInt64.ofBitVec (s.regs.rsi.toBitVec + 1)
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 1)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 1) }
    status := memcpySubFlags s.regs.rdx.toBitVec 1
    dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 1 (BitVec.ofInt 8 v).toInt }

/-- All registers not used by this implementation, including every SysV
callee-saved register, are preserved. RSP is unchanged until RET itself. -/
def MemcpyFrame (s t : MachineData) : Prop :=
  t.regs.rax = s.regs.rax ∧ t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms ∧
  (∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 →
    t.regs.get64 r = s.regs.get64 r)

theorem memcpyFrame_refl (s : MachineData) : MemcpyFrame s s := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩

theorem memcpyFrame_trans {s t u : MachineData}
    (h : MemcpyFrame s t) (h' : MemcpyFrame t u) : MemcpyFrame s u := by
  refine ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, ?_⟩
  intro r h1 h2 h3 h4 h5
  exact (h'.2.2.2 r h1 h2 h3 h4 h5).trans (h.2.2.2 r h1 h2 h3 h4 h5)

theorem memcpyBulk_frame (s : MachineData) (v : Int) : MemcpyFrame s (memcpyBulkState s v) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [memcpyBulkState, Reg64s.get64]

theorem memcpyByte_frame (s : MachineData) (v : Int) : MemcpyFrame s (memcpyByteState s v) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [memcpyByteState, Reg64s.get64]

macro "memcpy_step" : tactic => `(tactic|
  (apply step_cps
   simp (config := {instances := true}) [memcpyStep, step1, Executable.step,
     fetch0, fetch3, fetch7, fetch9, fetch12, fetch15, fetch19, fetch23,
     fetch27, fetch31, fetch33, fetch36, fetch38, fetch40, fetch42, fetch46,
     fetch50, fetch54, fetch56,
     List.zip, Directives.interp, Directive.interp, Instr.interp,
     Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
     AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
     MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
     Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
     BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
     BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
     labelBulk, labelTail, labelByte, labelDone, Int64.add_assoc]))

/-- Seven real ISA instructions execute a complete bulk iteration. The next
PC is determined by the actual comparison carry flag, not a surrogate branch. -/
theorem memcpy_bulk_runs (base : Int64) (s : MachineData) (v old : Int) (P : MachineState → Prop)
    (hs : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some v)
    (hd : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some old)
    (hp : Eventually (memcpyStep base) P
      (memcpyBulkState s v, if (memcpyBulkState s v).status.cf then base + 33 else base + 9)) :
    Eventually (memcpyStep base) P (s, base + 9) := by
  memcpy_step
  simp only [MachineData.load, Effects.All, hs]
  memcpy_step
  simp only [MachineData.store, Effects.All, hd]
  memcpy_step
  memcpy_step
  memcpy_step
  memcpy_step
  memcpy_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memcpyBulkState, memcpySubFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed, UInt64.add_comm, Effects.All]

private theorem memcpy_low_byte {w : Nat} (hi : BitVec w) (v : Int) :
    ((hi ++ BitVec.ofInt 8 v).toNat : Int).bmod 256 = v.bmod 256 := by
  have h := congrArg BitVec.toInt
    (BitVec.setWidth_append_eq_right (a := hi) (b := BitVec.ofInt 8 v))
  simpa using h

/-- Six real ISA instructions execute a complete byte iteration. -/
theorem memcpy_byte_runs (base : Int64) (s : MachineData) (v old : Int) (P : MachineState → Prop)
    (hs : Mem.loadInt s.dmem s.regs.rsi.toBitVec 1 = some v)
    (hd : Mem.loadInt s.dmem s.regs.rdi.toBitVec 1 = some old)
    (hp : Eventually (memcpyStep base) P
      (memcpyByteState s v, if (memcpyByteState s v).status.zf then base + 56 else base + 38)) :
    Eventually (memcpyStep base) P (s, base + 38) := by
  memcpy_step
  simp only [MachineData.load, Effects.All, hs]
  memcpy_step
  simp only [MachineData.store, Effects.All, hd]
  memcpy_step
  memcpy_step
  memcpy_step
  memcpy_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memcpyByteState, memcpySubFlags, StatusFlags.from_result,
      BitVec.replaceLow, BitVec.drop, BitVec.take, BitVec.signed,
      UInt64.add_comm, Effects.All, memcpy_low_byte]

/-- TEST's undefined AF is universally quantified by Kraken's Effects.All. -/
def memcpyTestState (s : MachineData) (af : Bool) : MachineData :=
  { s with status := .from_result s.regs.rdx.toBitVec { cf := false, af, of := false } }

theorem memcpy_tail_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ af, Eventually (memcpyStep base) P
      (memcpyTestState s af, if s.regs.rdx.toBitVec == 0 then base + 56 else base + 38)) :
    Eventually (memcpyStep base) P (s, base + 33) := by
  have next (af : Bool) :
      Eventually (memcpyStep base) P (memcpyTestState s af, base + 36) := by
    unfold memcpyTestState
    have hnext := hp af
    memcpy_step
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [memcpyTestState, StatusFlags.from_result, Effects.All]
  memcpy_step
  exact ⟨next false, next true⟩

/-- Entry preserves the original destination in RAX and selects the bulk or
tail path using the comparison's unsigned carry flag. -/
def memcpyEntryState (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with rax := s.regs.rdi }
    status := memcpySubFlags s.regs.rdx.toBitVec 8 }

theorem memcpy_entry_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (memcpyStep base) P
      (memcpyEntryState s, if (memcpyEntryState s).status.cf then base + 33 else base + 9)) :
    Eventually (memcpyStep base) P (s, base) := by
  memcpy_step
  memcpy_step
  memcpy_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [memcpyEntryState, memcpySubFlags, StatusFlags.from_result,
      BitVec.take, BitVec.signed, Effects.All]


/-- RET reads the mapped return slot, pops precisely eight bytes, and jumps
to the loaded return address. The slot itself is not written. -/
theorem memcpy_ret_runs (base : Int64) (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({ s with regs := { s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra)) :
    Eventually (memcpyStep base) P (s, base + 56) := by
  memcpy_step
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact Eventually.done _ hp

/-- Unsigned compare against eight: CF is exactly the predicate `n < 8`. -/
theorem memcpy_cf_sub8 (n : Nat) (hn : n < 2^64) :
    (memcpySubFlags (BitVec.ofNat 64 n) 8#64).cf = decide (n < 8) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memcpySubFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned]
  have hnat : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt hn
  by_cases h : n < 8
  · have hlt : BitVec.ofNat 64 n < 8#64 := by
      change (BitVec.ofNat 64 n).toNat < 8
      simpa only [hnat] using h
    rw [BitVec.toNat_sub_of_lt hlt]
    simp only [hnat, BitVec.toNat_ofNat]
    omega
  · have hle : (8#64 : BitVec 64) ≤ BitVec.ofNat 64 n := by
      change 8 ≤ (BitVec.ofNat 64 n).toNat
      rw [hnat]
      omega
    rw [BitVec.toNat_sub_of_le hle]
    simp only [hnat, BitVec.toNat_ofNat]
    omega

/-- Unsigned subtract-by-one: ZF is exactly the predicate `n = 1`. -/
theorem memcpy_zf_sub1 (n : Nat) (hn : n < 2^64) :
    (memcpySubFlags (BitVec.ofNat 64 n) 1#64).zf = decide (n = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [memcpySubFlags, StatusFlags.from_result, beq_iff_eq, decide_eq_true_eq]
  change BitVec.ofNat 64 n - 1#64 = 0#64 ↔ n = 1
  constructor
  · intro h
    have ha := congrArg (fun v : BitVec 64 => v + 1#64) h
    rw [BitVec.sub_add_cancel, BitVec.zero_add] at ha
    have hnat := congrArg BitVec.toNat ha
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using hnat
  · rintro rfl
    rfl

end SszX86


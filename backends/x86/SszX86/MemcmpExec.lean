import SszX86.MemcmpSpec

namespace SszX86.Memcmp

open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev step (base : Int64) := @step1 (memcmpLayout base) (memcmpExecutable base)

macro "memcmp_fetch" : tactic => `(tactic|
  (dsimp (config := {instances := true})
    [memcmpExecutable, memcmpLayout, memcmpProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses,
     Int64.add_assoc]))
macro "memcmp_label" : tactic => `(tactic|
  (dsimp (config := {instances := true})
    [Executable.labels, memcmpExecutable, memcmpLayout, memcmpProgram, Kraken.Layout.apply]
   simp [Kraken.Executable.withAddresses, memcmpLoadLeft, memcmpLoadRight, Int64.add_assoc]))

private theorem fetch0 (base : Int64) : (memcmpExecutable base).directivesAtAddress base =
    (parse("xorl %eax, %eax")).zip [2] := by memcmp_fetch
private theorem fetch2 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 2) =
    (parse("testq %rdx, %rdx")).zip [3] := by memcmp_fetch
private theorem fetch5 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 5) =
    (parse("jz done31")).zip [2] := by memcmp_fetch
private theorem fetch7 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 7) =
    [(.label "loop7", 0), (memcmpLoadLeft, 3)] := by memcmp_fetch
private theorem fetch10 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 10) =
    [(memcmpLoadRight, 3)] := by memcmp_fetch
private theorem fetch13 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 13) =
    (parse("subl %ecx, %eax")).zip [2] := by memcmp_fetch
private theorem fetch15 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 15) =
    (parse("jnz done31")).zip [2] := by memcmp_fetch
private theorem fetch17 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 17) =
    (parse("addq $1, %rdi")).zip [4] := by memcmp_fetch
private theorem fetch21 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 21) =
    (parse("addq $1, %rsi")).zip [4] := by memcmp_fetch
private theorem fetch25 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 25) =
    (parse("subq $1, %rdx")).zip [4] := by memcmp_fetch
private theorem fetch29 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 29) =
    (parse("jnz loop7")).zip [2] := by memcmp_fetch
private theorem fetch31 (base : Int64) : (memcmpExecutable base).directivesAtAddress (base + 31) =
    (parse("done31: ret")).zip [0,1] := by memcmp_fetch
private theorem labelLoop (base : Int64) :
    (Executable.labels (memcmpExecutable base)).label "loop7" = base + 7 := by memcmp_label
private theorem labelDone (base : Int64) :
    (Executable.labels (memcmpExecutable base)).label "done31" = base + 31 := by memcmp_label

/-- Exact memory and all non-clobbered registers, including the entire SysV
callee-saved set. The return-slot pointer is unchanged until RET. -/
def Frame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms ∧
  (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi →
    t.regs.get64 r = s.regs.get64 r)

theorem frame_refl (s : MachineData) : Frame s s :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
theorem frame_trans {s t u : MachineData} (h : Frame s t) (h' : Frame t u) : Frame s u := by
  refine ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, ?_⟩
  intro r h1 h2 h3 h4 h5
  exact (h'.2.2.2 r h1 h2 h3 h4 h5).trans (h.2.2.2 r h1 h2 h3 h4 h5)

def subFlags (a b : BitVec 32) : StatusFlags :=
  let v := a - b
  .from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }

def entry (s : MachineData) (af : Bool) : MachineData :=
  { s with
    regs := { s.regs with rax := 0 }
    status := .from_result s.regs.rdx.toBitVec { cf := false, af, of := false } }

def compare (s : MachineData) (a b : BitVec 8) : MachineData :=
  { s with
    regs := { s.regs with
      rax := UInt64.ofBitVec ((a.setWidth 32 - b.setWidth 32).setWidth 64)
      rcx := UInt64.ofBitVec (b.setWidth 64) }
    status := subFlags (a.setWidth 32) (b.setWidth 32) }

def advance (s : MachineData) : MachineData :=
  { s with
    regs := { s.regs with
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 1)
      rsi := UInt64.ofBitVec (s.regs.rsi.toBitVec + 1)
      rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec - 1) }
    status := memcpySubFlags s.regs.rdx.toBitVec 1 }

theorem entry_frame (s : MachineData) (af : Bool) : Frame s (entry s af) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [entry, Reg64s.get64]
theorem compare_frame (s : MachineData) (a b : BitVec 8) : Frame s (compare s a b) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [compare, Reg64s.get64]
theorem advance_frame (s : MachineData) : Frame s (advance s) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp_all [advance, Reg64s.get64]

private theorem byte_low32 (v : BitVec 8) :
    (v.setWidth 64).extractLsb' 0 32 = v.setWidth 32 := by
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  simp

private theorem byte_low4 (v : BitVec 8) :
    (v.setWidth 64).extractLsb' 0 4 = (v.setWidth 32).extractLsb' 0 4 := by
  simp only [BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 4 ≤ 64),
    BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 4 ≤ 32)]

macro "memcmp_step" : tactic => `(tactic|
  (apply step_cps
   simp (config := {instances := true}) [step, step1, Executable.step,
     fetch0, fetch2, fetch5, fetch7, fetch10, fetch13, fetch15, fetch17,
     fetch21, fetch25, fetch29, fetch31, memcmpLoadLeft, memcmpLoadRight,
     List.zip, Directives.interp, Directive.interp, Instr.interp,
     Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
     AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize,
     MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
     Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
     BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
     BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
     labelLoop, labelDone, byte_low32, byte_low4, Int64.add_assoc]))

/-- Entry performs no data access; both undefined auxiliary flags are universal. -/
theorem entry_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ af, Eventually (step base) P
      (entry s af, if s.regs.rdx.toBitVec == 0 then base + 31 else base + 7)) :
    Eventually (step base) P (s, base) := by
  have next (af : Bool) : Eventually (step base) P (entry s af, base + 5) := by
    have h := hp af
    unfold entry
    memcmp_step
    split <;> rename_i hb
    all_goals simp_all (config := {instances := true})
      [entry, StatusFlags.from_result, Effects.All]
  memcmp_step
  constructor <;> memcmp_step <;> exact ⟨next false, next true⟩

/-- The two mapped byte reads and SUB/JNZ, with no wider or speculative load. -/
theorem compare_runs (base : Int64) (s : MachineData) (a b : BitVec 8)
    (P : MachineState → Prop)
    (ha : Mem.loadInt s.dmem s.regs.rdi.toBitVec 1 = some (a.toNat : Int))
    (hb : Mem.loadInt s.dmem s.regs.rsi.toBitVec 1 = some (b.toNat : Int))
    (hp : Eventually (step base) P
      (compare s a b, if a = b then base + 17 else base + 31)) :
    Eventually (step base) P (s, base + 7) := by
  have hcast (v : BitVec 8) : BitVec.ofInt 8 (v.toNat : Int) = v := by bv_omega
  have hz : a.setWidth 32 - b.setWidth 32 = 0#32 ↔ a = b := by bv_omega
  memcmp_step
  simp only [MachineData.load, Effects.All, ha, hcast]
  memcmp_step
  simp only [MachineData.load, Effects.All, hb, hcast]
  memcmp_step
  memcmp_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [compare, subFlags, StatusFlags.from_result, BitVec.take, BitVec.signed,
      Effects.All]

/-- Pointer increments and bounded count decrement are reached only after equality. -/
theorem advance_runs (base : Int64) (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step base) P
      (advance s, if (advance s).status.zf then base + 31 else base + 7)) :
    Eventually (step base) P (s, base + 17) := by
  memcmp_step
  memcmp_step
  memcmp_step
  memcmp_step
  split <;> rename_i hbranch
  all_goals simp_all (config := {instances := true})
    [advance, memcpySubFlags, StatusFlags.from_result, BitVec.take, BitVec.signed,
      UInt64.add_comm, Effects.All]

/-- Real RET, including its only eight-byte load and exact stack pop. -/
theorem ret_runs (base : Int64) (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : P ({ s with regs := { s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra)) :
    Eventually (step base) P (s, base + 31) := by
  memcmp_step
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact Eventually.done _ hp

end SszX86.Memcmp

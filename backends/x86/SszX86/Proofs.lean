import SszX86.Impl
import SszX86.Bytes
import Kraken.X64.Sep

/-!
These are ordinary-memory contracts for the complete `movq; ret` kernels under
Kraken's x86-64 semantics. Instruction sizes and the load address are arbitrary;
no `fakeLayout` is used. Separation keeps the writable destination disjoint from
the return slot and from the caller's arbitrary frame. No alignment premise is
needed. Addresses and the stack increment use the model's modular 64-bit domain.

Kraken does not model canonical-address faults or page permissions here:
`Effects.All` discharges access-request effects. The parsed-assembly/object-byte
binding and Kraken's hand-written ISA semantics remain trust boundaries.
-/

namespace SszX86

open Std.ExtHashMap

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Complete post-load state: all fields not explicitly listed are unchanged. -/
def loaded (s : MachineData) (value : BitVec 64) : MachineData :=
  { s with regs := { s.regs with
      rax := UInt64.ofBitVec value
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }

/-- Complete post-store state: memory changes only by this eight-byte store;
only `rsp` changes among registers, and flags and vector registers are preserved. -/
def stored (s : MachineData) : MachineData :=
  { s with
    dmem := Mem.storeInt s.dmem s.regs.rdi.toBitVec 8 s.regs.rsi.toBitVec.toInt
    regs := { s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8) } }

private theorem loadProgram_runs [layout : Layout] (s : MachineData)
    (value ret : Int) (post : MachineState → Prop)
    (hload : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some value)
    (hret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some ret)
    (hpost : post (loaded s (BitVec.ofInt 64 value), Int64.ofBitVec (BitVec.ofInt 64 ret))) :
    straightlineStep (layout loadProgram) (s, layout.start) post := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp only [loadProgram]
  simpa [List.mapIdx, List.mapIdx.go, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Reg64s.get64, BitVec.take,
    MachineData.load, Effects.All, hload, hret, loaded] using hpost

private theorem storeProgram_runs [layout : Layout] (s : MachineData)
    (old ret : Int) (post : MachineState → Prop)
    (hload : Mem.loadInt s.dmem s.regs.rdi.toBitVec 8 = some old)
    (hret : Mem.loadInt (stored s).dmem s.regs.rsp.toBitVec 8 = some ret)
    (hpost : post (stored s, Int64.ofBitVec (BitVec.ofInt 64 ret))) :
    straightlineStep (layout storeProgram) (s, layout.start) post := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp only [storeProgram]
  have hret' : Mem.loadInt
      (Mem.storeInt s.dmem s.regs.rdi.toBitVec 8 s.regs.rsi.toBitVec.toInt)
      s.regs.rsp.toBitVec 8 = some ret := hret
  simpa [List.mapIdx, List.mapIdx.go, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    MachineData.set, Reg64s.set64, Reg64s.get, Reg64s.get64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    MachineData.load, MachineData.store, Effects.All, hload, hret', stored] using hpost

/-- Loading an owned eight-byte SSZ encoding returns its value, executes `ret`,
pops the return slot, and preserves the entire memory, flags, vector registers,
and all general-purpose registers other than `rax` and `rsp`.

The input and return-slot assertions are deliberately separate: read-only input
may overlap the return slot. `R` describes arbitrary caller-owned memory. -/
theorem loadProgram_correct [layout : Layout] (s : MachineData)
    (value ra : BitVec 64) (R : DataMem → Prop)
    (hmem : s.dmem =⋆ Eq ((wordBytes value).At s.regs.rdi.toBitVec) ⋆ R)
    (hret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra))) :
    straightlineStep (layout loadProgram) (s, layout.start) (fun s' =>
      s' = (loaded s value, Int64.ofBitVec ra) ∧
      s'.1.regs.rax.toBitVec = value ∧
      s'.2.toBitVec = ra ∧
      s'.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
      s'.1.dmem = s.dmem ∧
      (s'.1.dmem =⋆ Eq ((wordBytes value).At s.regs.rdi.toBitVec) ⋆ R) ∧
      s'.1.status = s.status ∧ s'.1.zmms = s.zmms ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → s'.1.regs.get64 r = s.regs.get64 r)) := by
  have hload := Mem.loadInt_sep (wordBytes value) s.regs.rdi.toBitVec 8 R s.dmem
    hmem (wordBytes_length value) (by decide)
  apply loadProgram_runs s (Int.ofBytes (wordBytes value))
    (Int.ofBytes (wordBytes ra)) _ hload hret
  simp only [ofBytes_wordBytes]
  simp [loaded, hmem]
  intro r hax hsp
  cases r <;> simp_all [Reg64s.get64]

/-- Storing a value writes exactly the eight upstream `Ssz.uintBytes` bytes into
the caller's existing buffer, preserves the disjoint return slot and arbitrary
frame `R`, returns to `ra`, and changes no registers except the popped `rsp`.
`old` can be any eight bytes, so the caller need not initialize the buffer to a
special encoding. Both the output and return-slot memory are ordinary mapped
memory; no allocation or alignment hypothesis appears. -/
theorem storeProgram_correct [layout : Layout] (s : MachineData)
    (old : List UInt8) (ra : BitVec 64) (R : DataMem → Prop)
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At s.regs.rdi.toBitVec) ⋆
      (Eq ((wordBytes ra).At s.regs.rsp.toBitVec) ⋆ R)) :
    straightlineStep (layout storeProgram) (s, layout.start) (fun s' =>
      s' = (stored s, Int64.ofBitVec ra) ∧
      s'.1.dmem = Mem.storeBytes s.dmem s.regs.rdi.toBitVec
        (wordBytes s.regs.rsi.toBitVec) ∧
      (s'.1.dmem =⋆ Eq ((wordBytes s.regs.rsi.toBitVec).At s.regs.rdi.toBitVec) ⋆
        (Eq ((wordBytes ra).At s.regs.rsp.toBitVec) ⋆ R)) ∧
      s'.2.toBitVec = ra ∧
      s'.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
      s'.1.status = s.status ∧ s'.1.zmms = s.zmms ∧
      (∀ r, r ≠ .rsp → s'.1.regs.get64 r = s.regs.get64 r)) := by
  have hload := Mem.loadInt_sep old s.regs.rdi.toBitVec 8
    (Eq ((wordBytes ra).At s.regs.rsp.toBitVec) ⋆ R) s.dmem hmem hlen (by decide)
  have hbytes : Int.toBytes 8 s.regs.rsi.toBitVec.toInt = wordBytes s.regs.rsi.toBitVec :=
    registerBytes_eq_uintBytes s.regs.rsi.toBitVec
  have hstore : (stored s).dmem =⋆
      Eq ((wordBytes s.regs.rsi.toBitVec).At s.regs.rdi.toBitVec) ⋆
        (Eq ((wordBytes ra).At s.regs.rsp.toBitVec) ⋆ R) := by
    simpa only [stored, hbytes] using
      Mem.storeInt_sep s.regs.rdi.toBitVec 8 old
        (Eq ((wordBytes ra).At s.regs.rsp.toBitVec) ⋆ R) s.dmem
        ⟨hmem, hlen⟩ s.regs.rsi.toBitVec.toInt
  have hretSep := hstore
  rw [sep_comm_l] at hretSep
  have hret := Mem.loadInt_sep (wordBytes ra) s.regs.rsp.toBitVec 8
    (Eq ((wordBytes s.regs.rsi.toBitVec).At s.regs.rdi.toBitVec) ⋆ R)
    (stored s).dmem hretSep (wordBytes_length ra) (by decide)
  apply storeProgram_runs s (Int.ofBytes old) (Int.ofBytes (wordBytes ra)) _ hload hret
  rw [ofBytes_wordBytes]
  refine ⟨rfl, ?_, hstore, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [stored, Mem.storeInt, hbytes]
  · rfl
  · rfl
  · intro r hsp
    cases r <;> simp_all [stored, Reg64s.get64]

#print axioms uintBytes_eq_toBytes
#print axioms registerBytes_eq_uintBytes
#print axioms loadProgram_correct
#print axioms storeProgram_correct

end SszX86

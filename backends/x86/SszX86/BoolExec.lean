import SszX86.BoolImpl
import SszX86.MemcmpExec
import SszX86.BoolMemory

namespace SszX86.BoolCodec
open Kraken.X64.Parser

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

macro "bool_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := step_at _ _ $hc
     (SszX86.BoolCodec.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.BoolCodec.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [program, directives, labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc]))

def lengthCompared (s : MachineData) : MachineData :=
  {s with status := memcpySubFlags s.regs.r14.toBitVec 1}

private theorem sub_zero_iff {w : Nat} (a b : BitVec w) :
    a - b = 0#w ↔ a = b := by
  constructor
  · intro h
    have hc := congrArg (fun v : BitVec w => v + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using hc
  · intro h
    subst a
    exact BitVec.sub_self b

/-- Actual CMP/JNE at function offsets 45/49. In particular, rejecting a
non-unit length makes no data-memory access, even for a high-bit-set length. -/
theorem length_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P
      (lengthCompared s, if s.regs.r14.toBitVec == 1#64 then base + 55 else base + 1580)) :
    Eventually (step e) P (s, base + 45) := by
  have target := hc.targets ("boolScope", 1580) (by decide)
  have next : Eventually (step e) P (lengthCompared s, base + 49) := by
    bool_step 1 using hc
    simp only [lengthCompared, memcpySubFlags, StatusFlags.from_result] at *
    simp only [target]
    by_cases h : s.regs.r14.toBitVec = 1#64
    · simpa [h, Effects.All] using hp
    · have hz : s.regs.r14.toBitVec - 1#64 ≠ 0#64 :=
        fun hzero => h ((sub_zero_iff _ _).mp hzero)
      simpa [h, hz, Effects.All] using hp
  bool_step 0 using hc
  simpa [lengthCompared, memcpySubFlags, BitVec.take, BitVec.signed] using next

def byteLoaded (s : MachineData) (value : BitVec 8) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec (value.setWidth 64)}}

def byteTested (s : MachineData) (af : Bool) : MachineData :=
  {s with status :=
    StatusFlags.from_result (s.regs.rax.toBitVec.take 32) {cf := false, af, of := false}}

def byteCompared (s : MachineData) : MachineData :=
  {s with status := Memcmp.subFlags (s.regs.rax.toBitVec.take 32) 1#32}

theorem byte_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 8) (P : MachineState → Prop)
    (hl : Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 = some (value.toNat : Int))
    (hp : Eventually (step e) P (byteLoaded s value, base + 58)) :
    Eventually (step e) P (s, base + 55) := by
  have hcast : BitVec.ofInt 8 (value.toNat : Int) = value := by bv_omega
  bool_step 2 using hc
  simp only [MachineData.load, Effects.All, hl, hcast]
  simpa [byteLoaded] using hp

/-- TEST/JZ preserves the entire byte value and quantifies both undefined AFs. -/
theorem byte_zero_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ af, Eventually (step e) P
      (byteTested s af, if s.regs.rax.toBitVec.take 32 == 0#32 then base + 2663 else base + 66)) :
    Eventually (step e) P (s, base + 58) := by
  have target := hc.targets ("boolZero", 2663) (by decide)
  have next (af : Bool) : Eventually (step e) P (byteTested s af, base + 60) := by
    have hnext := hp af
    bool_step 4 using hc
    simp only [target]
    split <;> rename_i hbranch
    all_goals simp_all (config := {instances := true})
      [byteTested, StatusFlags.from_result, Effects.All]
  bool_step 3 using hc
  exact ⟨next false, next true⟩

theorem byte_one_branch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P
      (byteCompared s, if s.regs.rax.toBitVec.take 32 == 1#32 then base + 75 else base + 2674)) :
    Eventually (step e) P (s, base + 66) := by
  have target := hc.targets ("boolBad", 2674) (by decide)
  have next : Eventually (step e) P (byteCompared s, base + 69) := by
    bool_step 6 using hc
    simp only [byteCompared, Memcmp.subFlags, StatusFlags.from_result] at *
    simp only [target]
    by_cases h : s.regs.rax.toBitVec.take 32 = 1#32
    · simpa [h, Effects.All] using hp
    · have hz : s.regs.rax.toBitVec.take 32 - 1#32 ≠ 0#32 :=
        fun hzero => h ((sub_zero_iff _ _).mp hzero)
      simpa [h, hz, Effects.All] using hp
  bool_step 5 using hc
  simpa [byteCompared, Memcmp.subFlags, BitVec.take, BitVec.signed] using next

end SszX86.BoolCodec

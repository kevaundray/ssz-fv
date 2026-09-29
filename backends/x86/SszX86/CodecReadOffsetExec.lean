import SszX86.CodecReadOffsetImpl
import SszX86.DelimitedCore
import SszX86.NatCompareExec

namespace SszX86.CodecReadOffset
open Kraken.X64.Parser
open SszX86.UintCodec

macro "codec_offset_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.CodecReadOffset.step_at _ _ $hc
     (SszX86.CodecReadOffset.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.CodecReadOffset.program, SszX86.CodecReadOffset.programChunk0,
     List.getElem_cons_zero, List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.CodecReadOffset.program, SszX86.CodecReadOffset.programChunk0,
      SszX86.CodecReadOffset.directives,
      SszX86.CodecReadOffset.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

macro "codec_offset_load " hl:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($hl), Delimited.word_cast,
      Delimited.byte_cast])

def state (s : MachineData) (a c d i : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec c
      rdx := UInt64.ofBitVec d
      rsi := UInt64.ofBitVec i}
    status := flags}

@[simp] theorem state_initial (s : MachineData) :
    state s s.regs.rax.toBitVec s.regs.rcx.toBitVec s.regs.rdx.toBitVec
      s.regs.rsi.toBitVec s.status = s := by
  cases s with | mk regs zmms status dmem => cases regs <;> rfl

/-- Only the actual scratch PUSH destination is written. -/
def pushedMem (s : MachineData) : DataMem :=
  Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.rax.toBitVec.toInt

def pushedState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := pushedMem s}

/-- Four byte observations, not a load of uninitialized surrounding bytes. -/
def BytesAt (m : DataMem) (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) : Prop :=
  Mem.loadInt m p 1 = some (b0.toNat : Int) ∧
  Mem.loadInt m (p + 1#64) 1 = some (b1.toNat : Int) ∧
  Mem.loadInt m (p + 2#64) 1 = some (b2.toNat : Int) ∧
  Mem.loadInt m (p + 3#64) 1 = some (b3.toNat : Int)

def value (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  (b3 ++ b2 ++ b1 ++ b0).setWidth 64

private theorem pack (b0 b1 b2 b3 : BitVec 8) :
    (((b1.setWidth 32 <<< 8).setWidth 64 ||| b0.setWidth 64) |||
      (b2.setWidth 32 <<< 16).setWidth 64) |||
      (b3.setWidth 32 <<< 24).setWidth 64 = value b0 b1 b2 b3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  simp only [value, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, Nat.sub_sub]
  by_cases h8 : bit < 8 <;> by_cases h16 : bit < 16 <;>
    by_cases h24 : bit < 24 <;> by_cases h32 : bit < 32
  all_goals first | omega | simp_all (disch := omega)

def arithmetic (pc : Nat) (s : MachineData) (flags : StatusFlags) : MachineData :=
  let a := s.regs.rax.toBitVec
  let c := s.regs.rcx.toBitVec
  let d := s.regs.rdx.toBitVec
  let i := s.regs.rsi.toBitVec
  match pc with
  | 39 => state s a c d ((i.setWidth 32 <<< 24).setWidth 64) flags
  | 42 => state s a c ((d.setWidth 32 <<< 16).setWidth 64) i flags
  | 45 => state s ((a.setWidth 32 <<< 8).setWidth 64) c d i flags
  | 48 => state s (a ||| c) c d i flags
  | 51 => state s (a ||| d) c d i flags
  | _ => state s (a ||| i) c d i flags

/-- Quantifying dead arithmetic flags prevents repeated suffix proofs for the
undefined AF and OF choices of the three encoded shifts. -/
theorem arithmetic_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (pc : Nat) (hpc : pc ∈ [39, 42, 45, 48, 51, 54]) (s : MachineData)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (arithmetic pc s flags, base + Int64.ofNat (pc + 3))) :
    Eventually (step e) P (s, base + Int64.ofNat pc) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arithmetic, state] at next
  · codec_offset_step 13 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offset_step 14 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offset_step 15 using hc
    simp [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      Effects.All, BitVec.take]
    repeat' first | apply And.intro | intro
    all_goals exact next _
  · codec_offset_step 16 using hc
    constructor <;> exact next _
  · codec_offset_step 17 using hc
    constructor <;> exact next _
  · codec_offset_step 18 using hc
    constructor <;> exact next _

/-- All eight native bounds tests precede the first input read. -/
theorem bounds_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length : 4 ≤ s.regs.rsi.toNat)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 24)) :
    Eventually (step e) P (s, base + 1) := by
  have h0 : s.regs.rsi.toBitVec ≠ 0#64 := by
    intro eq
    have n := congrArg BitVec.toNat eq
    change s.regs.rsi.toNat = 0 at n
    omega
  have h1 : s.regs.rsi.toBitVec ≠ 1#64 := by
    intro eq
    have n := congrArg BitVec.toNat eq
    change s.regs.rsi.toNat = 1 at n
    omega
  have h2 : s.regs.rsi.toBitVec ≠ 2#64 := by
    intro eq
    have n := congrArg BitVec.toNat eq
    change s.regs.rsi.toNat = 2 at n
    omega
  have h3 : s.regs.rsi.toBitVec ≠ 3#64 := by
    intro eq
    have n := congrArg BitVec.toNat eq
    change s.regs.rsi.toNat = 3 at n
    omega
  have hlt : ¬s.regs.rsi.toNat < 2 := by omega
  codec_offset_step 1 using hc
  constructor <;> codec_offset_step 2 using hc
  all_goals simp [StatusFlags.from_result, h0, Effects.All]
  all_goals codec_offset_step 3 using hc
  all_goals codec_offset_step 4 using hc
  all_goals simp [StatusFlags.from_result, h1, Effects.All]
  all_goals codec_offset_step 5 using hc
  all_goals codec_offset_step 6 using hc
  all_goals simp [StatusFlags.from_result, h2, hlt, Effects.All]
  all_goals codec_offset_step 7 using hc
  all_goals codec_offset_step 8 using hc
  all_goals simpa [StatusFlags.from_result, h3, Effects.All] using next _

theorem body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (b0 b1 b2 b3 : BitVec 8)
    (input : BytesAt s.dmem s.regs.rdi.toBitVec b0 b1 b2 b3)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (state s (value b0 b1 b2 b3) (b0.setWidth 64)
        ((b2.setWidth 32 <<< 16).setWidth 64)
        ((b3.setWidth 32 <<< 24).setWidth 64) flags, base + 57)) :
    Eventually (step e) P (s, base + 24) := by
  codec_offset_step 9 using hc
  codec_offset_load input.1
  codec_offset_step 10 using hc
  codec_offset_load input.2.1
  codec_offset_step 11 using hc
  codec_offset_load input.2.2.1
  codec_offset_step 12 using hc
  codec_offset_load input.2.2.2
  apply arithmetic_cps e base hc 39 (by decide)
  intro f1
  apply arithmetic_cps e base hc 42 (by decide)
  intro f2
  apply arithmetic_cps e base hc 45 (by decide)
  intro f3
  apply arithmetic_cps e base hc 48 (by decide)
  intro f4
  apply arithmetic_cps e base hc 51 (by decide)
  intro f5
  apply arithmetic_cps e base hc 54 (by decide)
  intro f6
  simpa [arithmetic, state, BitVec.setWidth_setWidth_of_le, pack] using next f6

end SszX86.CodecReadOffset

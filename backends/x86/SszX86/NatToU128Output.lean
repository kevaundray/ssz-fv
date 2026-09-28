import SszX86.NatToU128Impl
import SszX86.DelimitedCore
import SszNatNarrow

namespace SszX86.NatToU128
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

macro "natu128_out_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatToU128.step_at _ _ $hc
     (SszX86.NatToU128.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatToU128.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatToU128.program, SszX86.NatToU128.directives,
      SszX86.NatToU128.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

abbrev OutputMapped (s : MachineData) : Prop :=
  Large.Mapped s.dmem s.regs.rdi.toBitVec 32

macro "natu128_output " row:num " at " offset:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 32) (byteCount := 8))
  else
    `(tactic| apply Large.mapped_load (capacity := 32) (offset := $offset) («width» := 8))
  `(tactic|
    (natu128_out_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def noneMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0

def someMem (m : DataMem) (out : BitVec 64) (value : BitVec 128) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8
    ((value >>> (64 : Nat)).setWidth 64).toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 (value.setWidth 64).toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0

def resultMem (m : DataMem) (out : BitVec 64) : Option (BitVec 128) → DataMem
  | none => noneMem m out
  | some value => someMem m out value

def someState (s : MachineData) (value : BitVec 128) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := 1, rcx := 0}
    status := flags
    dmem := someMem s.dmem s.regs.rdi.toBitVec value}

/-- None defines both tag words and leaves all sixteen payload bytes untouched. -/
theorem publish_none_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s)
    (tag : s.regs.rax.toBitVec = 0) (upper : s.regs.rcx.toBitVec = 0)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := noneMem s.dmem s.regs.rdi.toBitVec}, base + 57)) :
    Eventually (step e) P (s, base + 50) := by
  natu128_output 14 at 0 using hc mapped hm
  natu128_output 15 at 8 using hc mapped hm
  simpa [noneMem, tag, upper] using next

/-- Some publishes high then low payload before its complete 128-bit tag. -/
theorem publish_some_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 128) (hm : OutputMapped s)
    (high : s.regs.rax.toBitVec = (value >>> (64 : Nat)).setWidth 64)
    (low : s.regs.rdx.toBitVec = value.setWidth 64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (someState s value flags, base + 118)) :
    Eventually (step e) P (s, base + 96) := by
  natu128_output 32 at 24 using hc mapped hm
  natu128_output 33 at 16 using hc mapped hm
  natu128_out_step 34 using hc
  natu128_out_step 35 using hc
  constructor <;> natu128_output 36 at 0 using hc mapped hm
  all_goals natu128_output 37 at 8 using hc mapped hm
  all_goals simpa [someState, someMem, high, low] using next _

/-- Both actual return sites consume precisely the incoming mapped stack word. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 57) ∧
      Eventually (step e) P (s, base + 118) := by
  constructor
  · natu128_out_step 16 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next
  · natu128_out_step 38 using hc
    simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
    exact Eventually.done _ next

end SszX86.NatToU128

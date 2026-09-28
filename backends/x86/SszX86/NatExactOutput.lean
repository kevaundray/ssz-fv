import SszX86.NatExactImpl
import SszX86.DelimitedCore
import SszNatNarrow

namespace SszX86.NatExact
open Kraken.X64.Parser
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

macro "natexact_out_step " k:num " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.NatExact.step_at _ _ $hc
     (SszX86.NatExact.program[$k]'(by decide)) (List.getElem_mem (by decide))
   simp only [SszX86.NatExact.program, List.getElem_cons_zero,
     List.getElem_cons_succ] at fetched
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.NatExact.program, SszX86.NatExact.directives,
      SszX86.NatExact.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

abbrev OutputMapped (s : MachineData) : Prop :=
  Large.Mapped s.dmem s.regs.rdi.toBitVec 68

macro "natexact_output " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 68) (byteCount := $byteCount))
  else
    `(tactic| apply Large.mapped_load (capacity := 68)
      (offset := $offset) («width» := $byteCount))
  `(tactic|
    (natexact_out_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

def successMem (m : DataMem) (out : BitVec 64) : DataMem :=
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 0

def errorHeaderMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1
  Mem.storeInt m (out + BitVec.ofNat 64 8) 8 0

def failureMem (m : DataMem) (out pointer payload actual : BitVec 64) : DataMem :=
  let m := errorHeaderMem m out
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 payload.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 actual.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  Mem.storeInt m (out + BitVec.ofNat 64 64) 4 3

def resultMem (m : DataMem) (out : BitVec 64)
    (expected : SszNative.NatOperand) (actual : BitVec 64) : DataMem :=
  if SszNative.NatNarrow.runExact expected actual then successMem m out
  else failureMem m out expected.pointer expected.payload actual

def failureState (s : MachineData) (pointer payload actual : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rax := 3, rcx := UInt64.ofBitVec payload}
    dmem := failureMem s.dmem s.regs.rdi.toBitVec pointer payload actual}

/-- Success defines only the four-byte Result status, not its unused payload. -/
theorem publish_success_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (status : s.regs.rax.toBitVec = 0)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := successMem s.dmem s.regs.rdi.toBitVec}, base + 174)) :
    Eventually (step e) P (s, base + 171) := by
  natexact_output 45 at 64 width 4 using hc mapped hm
  simpa [successMem, status] using next

/-- Failure reloads and stores the original pair after writing the text tag. -/
theorem publish_failure_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload actual : BitVec 64) (hm : OutputMapped s)
    (actualReg : s.regs.rdx.toBitVec = actual)
    (pointerRead : Mem.loadInt (errorHeaderMem s.dmem s.regs.rdi.toBitVec)
      s.regs.rsi.toBitVec 8 = some (pointer.toNat : Int))
    (payloadRead : Mem.loadInt (errorHeaderMem s.dmem s.regs.rdi.toBitVec)
      (s.regs.rsi.toBitVec + 8) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (failureState s pointer payload actual, base + 174)) :
    Eventually (step e) P (s, base + 108) := by
  natexact_output 34 at 0 width 8 using hc mapped hm
  natexact_output 35 at 8 width 8 using hc mapped hm
  natexact_out_step 36 using hc
  change Mem.loadInt _ _ _ = _ at pointerRead
  simp only [errorHeaderMem, BitVec.add_zero, BitVec.ofNat_eq_ofNat] at pointerRead payloadRead
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All, pointerRead]
  natexact_out_step 37 using hc
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, payloadRead]
  natexact_output 38 at 16 width 8 using hc mapped hm
  natexact_output 39 at 24 width 8 using hc mapped hm
  natexact_output 40 at 32 width 8 using hc mapped hm
  natexact_output 41 at 40 width 8 using hc mapped hm
  natexact_output 42 at 48 width 8 using hc mapped hm
  natexact_output 43 at 56 width 8 using hc mapped hm
  natexact_out_step 44 using hc
  natexact_output 45 at 64 width 4 using hc mapped hm
  simpa [failureState, failureMem, errorHeaderMem, actualReg] using next

/-- The sole actual RET consumes the mapped incoming return slot. -/
theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (next : P ({s with regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 174) := by
  natexact_out_step 46 using hc
  simp only [MachineData.load, Effects.All, ret, ofBytes_wordBytes]
  exact Eventually.done _ next

end SszX86.NatExact

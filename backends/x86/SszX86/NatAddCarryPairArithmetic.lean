import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Pair.Cuts
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def firstAddState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := 0
      r14 := UInt64.ofBitVec (get s .r15 + get s .r14)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++
        BitVec.ofNat 8 (Udivti3.addFlags (get s .r15) (get s .r14)).cf.toNat)}
    status := flags}

def secondAddState (s : MachineData) (carry : Bool) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec (get s .r12 + BitVec.ofNat 64 carry.toNat)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64
        (Udivti3.addFlags (get s .r12) (BitVec.ofNat 64 carry.toNat)).cf.toNat)}
    status := flags}

def finishState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rsi := UInt64.ofBitVec (get s .r15 + 1#64)}
    status := flags}

theorem first_add_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (firstAddState s flags, base + 1278)) :
    Eventually (step e) P (s, base + 1269) := by
  natadd_step 334 using hc
  constructor
  all_goals natadd_step 335 using hc
  all_goals natadd_step 336 using hc
  all_goals simpa (config := {instances := true})
    [firstAddState, get, Reg64s.get64, Udivti3.addFlags_cf, StatusFlags.from_result] using hp _

theorem second_add_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (carry : Bool)
    (hsi : s.regs.rsi = 0)
    (hbpl : (get s .rbp).setWidth 8 = BitVec.ofNat 8 carry.toNat)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (secondAddState s carry flags, base + 1239)) :
    Eventually (step e) P (s, base + 1226) := by
  simp only [get, Reg64s.get64] at hbpl
  natadd_step 320 using hc
  natadd_step 321 using hc
  constructor
  all_goals natadd_step 322 using hc
  all_goals natadd_step 323 using hc
  all_goals simpa (config := {instances := true}) [secondAddState, get, Reg64s.get64, hsi, hbpl,
    Udivti3.addFlags_cf, StatusFlags.from_result, carry_byte] using hp _

theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (finishState s flags,
      if get s .r15 = get s .r11 then base + 1297 else base + 1252)) :
    Eventually (step e) P (s, base + 1243) := by
  have target := hc.targets ("natAdd_u1297", 1297) (by decide)
  natadd_step 325 using hc
  natadd_step 326 using hc
  natadd_step 327 using hc
  by_cases last : s.regs.r15.toBitVec = s.regs.r11.toBitVec
  all_goals simpa [finishState, get, Reg64s.get64, StatusFlags.from_result, target,
    BitVec.ofInt_add, BitVec.ofInt_toInt, last, Effects.All] using hp _

end SszX86.NatAdd.Carry.Pair.Cuts

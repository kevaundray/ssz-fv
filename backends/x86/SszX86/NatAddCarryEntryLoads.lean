import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Entry
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def leftState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r9 := UInt64.ofBitVec value}
    status := flags}

def clearedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r14 := 0}
    status := flags}

def rightState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r15 := UInt64.ofBitVec value}
    status := flags}

theorem left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hptr : get s .rsi ≠ 0) (hlen : get s .rdx ≠ 0)
    (hl : Mem.loadInt s.dmem (get s .rsi) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (leftState s value flags, base + 882)) :
    Eventually (step e) P (s, base + 536) := by
  simp only [get, Reg64s.get64] at hptr hlen hl
  rw [show (0 : BitVec 64) = 0#64 by decide] at hptr hlen
  natadd_step 138 using hc
  constructor
  all_goals natadd_step 139 using hc
  all_goals simp [StatusFlags.from_result, hptr, Effects.All]
  all_goals natadd_step 140 using hc
  all_goals constructor
  all_goals natadd_step 141 using hc
  all_goals simp [StatusFlags.from_result, hlen, Effects.All]
  all_goals natadd_step 142 using hc
  all_goals natadd_load hl
  all_goals natadd_step 143 using hc
  all_goals simpa [leftState] using hp _

theorem dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (clearedState s flags,
      if get s .rcx = 0 then base + 900 else if get s .r8 = 0 then base + 914 else base + 895)) :
    Eventually (step e) P (s, base + 882) := by
  have targetSmall := hc.targets ("natAdd_u900", 900) (by decide)
  have targetZero := hc.targets ("natAdd_u914", 914) (by decide)
  by_cases small : s.regs.rcx.toBitVec = 0#64
  · natadd_step 225 using hc
    constructor
    all_goals natadd_step 226 using hc
    all_goals constructor
    all_goals natadd_step 227 using hc
    all_goals simpa [clearedState, get, Reg64s.get64, StatusFlags.from_result,
      small, targetSmall, Effects.All] using hp _
  · natadd_step 225 using hc
    constructor
    all_goals natadd_step 226 using hc
    all_goals constructor
    all_goals natadd_step 227 using hc
    all_goals simp [StatusFlags.from_result, small, Effects.All]
    all_goals natadd_step 228 using hc
    all_goals constructor
    all_goals natadd_step 229 using hc
    all_goals by_cases empty : s.regs.r8.toBitVec = 0#64
    all_goals simpa [clearedState, get, Reg64s.get64, StatusFlags.from_result,
      small, empty, targetZero, Effects.All] using hp _

theorem right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rcx) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (rightState s value s.status, base + 917)) :
    Eventually (step e) P (s, base + 895) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 230 using hc
  natadd_load hl
  natadd_step 231 using hc
  simpa only [rightState] using hp

theorem zero_right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (rightState s 0 flags, base + 917)) :
    Eventually (step e) P (s, base + 914) := by
  natadd_step 237 using hc
  constructor <;> simpa [rightState] using hp _

end SszX86.NatAdd.Carry.Entry

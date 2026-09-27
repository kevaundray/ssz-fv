import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Fetch
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def leftState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r15 := UInt64.ofBitVec value}
    status := flags}

def rightState (s : MachineData) (value : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r12 := UInt64.ofBitVec value}
    status := flags}

theorem load_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rsi + get s .rbx * 8#64) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (leftState s value s.status, base + 1017)) :
    Eventually (step e) P (s, base + 1013) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 264 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_load hl
  simpa only [leftState, get, Reg64s.get64] using hp

theorem zero_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (leftState s 0 flags, base + 1043)) :
    Eventually (step e) P (s, base + 1040) := by
  natadd_step 270 using hc
  constructor <;> simpa [leftState] using hp _

theorem load_right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64)
    (hl : Mem.loadInt s.dmem (get s .rcx + get s .rbx * 8#64) 8 = some (value.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (rightState s value s.status, base + 964)) :
    Eventually (step e) P (s, base + 960) := by
  simp only [get, Reg64s.get64] at hl
  natadd_step 249 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natadd_load hl
  simpa only [rightState, get, Reg64s.get64] using hp

theorem zero_right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (rightState s 0 flags, base + 964)) :
    Eventually (step e) P (s, base + 1055) := by
  natadd_step 275 using hc
  constructor
  all_goals natadd_step 276 using hc
  all_goals simpa [rightState] using hp _

theorem skip_right_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P (s, base + 1055)) :
    Eventually (step e) P (s, base + 1029) := by
  natadd_step 269 using hc
  exact hp

end SszX86.NatAdd.Carry.Fetch

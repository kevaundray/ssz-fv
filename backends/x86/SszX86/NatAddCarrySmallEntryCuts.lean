import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Pair.SmallEntry
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def seedState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r9 := s.regs.rdx, r14 := 0}
    status := flags}

def setupState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := 1
      rbx := UInt64.ofBitVec (get s .rbx + 8#64)
      r11 := UInt64.ofBitVec (get s .r11 &&& get s .rax)}
    status := flags}

theorem left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (zero : get s .rsi = 0) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 862)) :
    Eventually (step e) P (s, base + 536) := by
  simp only [get, Reg64s.get64] at zero
  have target := hc.targets ("natAdd_u862", 862) (by decide)
  natadd_step 138 using hc
  constructor
  all_goals natadd_step 139 using hc
  all_goals simpa [StatusFlags.from_result, zero, target, Effects.All] using hp _

theorem pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : get s .rcx ≠ 0) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 871)) :
    Eventually (step e) P (s, base + 862) := by
  have zeroWord : (0 : BitVec 64) = 0#64 := by decide
  simp only [get, Reg64s.get64, zeroWord] at nonzero
  have target := hc.targets ("natAdd_u1080", 1080) (by decide)
  natadd_step 219 using hc
  constructor
  all_goals natadd_step 220 using hc
  all_goals simpa [StatusFlags.from_result, nonzero, target, Effects.All] using hp _

theorem seed_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (seedState s flags, base + 890)) :
    Eventually (step e) P (s, base + 871) := by
  natadd_step 221 using hc
  constructor
  all_goals natadd_step 222 using hc
  all_goals natadd_step 223 using hc
  all_goals simpa only [seedState] using hp _

theorem length_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : get s .r8 ≠ 0) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 895)) :
    Eventually (step e) P (s, base + 890) := by
  have zeroWord : (0 : BitVec 64) = 0#64 := by decide
  simp only [get, Reg64s.get64, zeroWord] at nonzero
  have target := hc.targets ("natAdd_u914", 914) (by decide)
  natadd_step 228 using hc
  constructor
  all_goals natadd_step 229 using hc
  all_goals simpa [StatusFlags.from_result, nonzero, target, Effects.All] using hp _

theorem count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (notOne : get s .rax ≠ 1#64) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 1207)) :
    Eventually (step e) P (s, base + 1060) := by
  simp only [get, Reg64s.get64] at notOne
  have target := hc.targets ("natAdd_u1207", 1207) (by decide)
  natadd_step 277 using hc
  natadd_step 278 using hc
  simpa [StatusFlags.from_result, Udivti3.zf_sub, notOne, target, Effects.All] using hp _

theorem setup_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (setupState s flags, base + 1252)) :
    Eventually (step e) P (s, base + 1207) := by
  natadd_step 315 using hc
  constructor
  all_goals natadd_step 316 using hc
  all_goals natadd_step 317 using hc
  all_goals natadd_step 318 using hc
  all_goals simpa [setupState, get, Reg64s.get64, UInt64.add_comm, UInt64.and_comm] using hp _

end SszX86.NatAdd.Carry.Pair.SmallEntry

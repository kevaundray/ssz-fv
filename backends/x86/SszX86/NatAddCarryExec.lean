import SszX86.NatAddCarryMath

namespace SszX86.NatAdd.Carry
open Kraken.X64.Parser
open UintCodec
open UintCodec.Large

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

abbrev get (s : MachineData) (r : Reg64) : BitVec 64 := s.regs.get64 r

def added (s : MachineData) : BitVec 64 := get s .r14 + get s .r12 + get s .r15

def carried (s : MachineData) : BitVec 64 :=
  BitVec.ofNat 64 (Udivti3.addFlags (get s .r14) (get s .r12)).cf.toNat +
    BitVec.ofNat 64 (Udivti3.addFlags (get s .r14 + get s .r12) (get s .r15)).cf.toNat

def addState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r13 := UInt64.ofBitVec (carried s)
      r14 := UInt64.ofBitVec (added s)}
    status := flags}

theorem carry_byte (b : Bool) :
    0#56 ++ BitVec.ofNat 8 b.toNat = BitVec.ofNat 64 b.toNat := by
  cases b <;> decide

private theorem uint_add_left_comm (a b c : UInt64) : a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

private theorem bv_add_left_comm (a b c : BitVec 64) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem uint_carry_comm (a b : Nat) :
    (OfNat.ofNat (decide (Udivti3.radix ≤ a+b)).toNat : UInt64) =
      (OfNat.ofNat (decide (Udivti3.radix ≤ b+a)).toNat : UInt64) := by
  apply congrArg (fun n : Nat => (OfNat.ofNat n : UInt64))
  rw [Nat.add_comm a b]

/-- The real ADD/SETB/ADD/ADC block, with dead final flags abstracted. -/
theorem adds_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (addState s flags, base + 981)) :
    Eventually (step e) P (s, base + 964) := by
  have carryOrder := uint_carry_comm s.regs.r15.toNat
    ((s.regs.r12.toNat+s.regs.r14.toNat) % 18446744073709551616)
  natadd_step 250 using hc
  constructor
  all_goals natadd_step 251 using hc
  all_goals natadd_step 252 using hc
  all_goals natadd_step 253 using hc
  all_goals natadd_step 254 using hc
  all_goals simpa (config := {instances := true}) [addState, added, carried, get, Reg64s.get64,
    Udivti3.addFlags_cf, StatusFlags.from_result, carry_byte, carryOrder,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, uint_add_left_comm, UInt64.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hp _

def stored (s : MachineData) : MachineData :=
  {s with
    dmem := Mem.storeInt s.dmem (get s .r10 + get s .rbx * 8#64) 8
      (get s .r14).toInt}

/-- The only store in a scalar iteration has precisely its eight-byte footprint. -/
theorem store_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10 + get s .rbx * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (stored s, base + 985)) :
    Eventually (step e) P (s, base + 981) := by
  natadd_step 255 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact hm
  simpa [stored, get, Reg64s.get64, Effects.All] using hp

def advanced (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec (get s .rbx + 1#64)
      r14 := s.regs.r13
      r15 := UInt64.ofBitVec (get s .r11 + get s .rbx + 1#64)}
    status := flags}

/-- LEA/INC/INC/MOV/CMP/JE takes the exit after the extra carry-word write. -/
theorem advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (advanced s flags, if get s .r11 + get s .rbx + 1#64 = 1#64
        then base + 1325 else base + 1008)) :
    Eventually (step e) P (s, base + 985) := by
  have target := hc.targets ("natAdd_u1325", 1325) (by decide)
  natadd_step 256 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  natadd_step 257 using hc
  natadd_step 258 using hc
  natadd_step 259 using hc
  natadd_step 260 using hc
  natadd_step 261 using hc
  by_cases done : get s .r11 + get s .rbx + 1#64 = 1#64
  · simp only [get, Reg64s.get64] at done
    have branch : s.regs.r11.toBitVec + s.regs.rbx.toBitVec = 0#64 := by bv_omega
    have register : s.regs.r11 + s.regs.rbx + 1 = (1 : UInt64) := by
      apply UInt64.toBitVec_inj.1
      simpa using done
    simpa (config := {instances := true}) [advanced, get, Reg64s.get64,
      StatusFlags.from_result, Udivti3.zf_sub,
      target, done, branch, register, Effects.All] using hp _
  · simp only [get, Reg64s.get64] at done
    have branch : s.regs.r11.toBitVec + s.regs.rbx.toBitVec ≠ 0#64 := by bv_omega
    simpa [advanced, get, Reg64s.get64, StatusFlags.from_result, Udivti3.zf_sub,
      target, done, branch, Effects.All] using hp _

/-- One complete actual scalar arithmetic/store/back-edge block. -/
theorem body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : ∃ old, Mem.loadInt s.dmem (get s .r10 + get s .rbx * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ firstFlags flags, Eventually (step e) P
      (advanced (stored (addState s firstFlags)) flags,
        if get s .r11 + get s .rbx + 1#64 = 1#64
        then base + 1325 else base + 1008)) :
    Eventually (step e) P (s, base + 964) := by
  apply adds_cps e base hc s P
  intro firstFlags
  apply store_cps e base hc
  · exact hm
  apply advance_cps e base hc
  intro flags
  exact hp firstFlags flags

end SszX86.NatAdd.Carry

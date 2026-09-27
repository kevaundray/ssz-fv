import SszX86.NatAddCarryExec

namespace SszX86.NatAdd.Carry.Fetch
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def selectState (s : MachineData) (scratch : UInt64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r12 := scratch}
    status := flags}

def selectFlag (s : MachineData) (small : Bool) : Bool :=
  decide (¬small ∧ (get s .rbx).toNat < (get s .r8).toNat)

private theorem byte_append (hi : BitVec 56) (lo : BitVec 8) :
    BitVec.setWidth 8 (hi ++ lo) = lo := BitVec.setWidth_append_eq_right

theorem left_branch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with status := flags},
        if (get s .rbx).toNat < (get s .rdx).toNat then base + 1013 else base + 1040)) :
    Eventually (step e) P (s, base + 1008) := by
  have target := hc.targets ("natAdd_u1040", 1040) (by decide)
  natadd_step 262 using hc
  natadd_step 263 using hc
  by_cases present : s.regs.rbx.toNat < s.regs.rdx.toNat
  all_goals simpa [get, Reg64s.get64, StatusFlags.from_result, present, target, Effects.All] using hp _

/-- The temporary R12 value is dead after the subsequent full-word load or XOR.
Only the zero flag is exposed to the branch continuation. -/
theorem select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (small mirror : Bool)
    (hbpl : (get s .rbp).extractLsb' 0 8 = if small then 1#8 else 0#8)
    (P : MachineState → Prop)
    (hp : ∀ scratch flags, flags.zf = selectFlag s small →
      Eventually (step e) P
        (selectState s scratch flags, if mirror then base + 1053 else base + 1027)) :
    Eventually (step e) P (s, if mirror then base + 1043 else base + 1017) := by
  simp only [get, Reg64s.get64] at hbpl
  rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] at hbpl
  cases mirror with
  | false =>
    natadd_step 265 using hc
    natadd_step 266 using hc
    natadd_step 267 using hc
    constructor
    all_goals apply hp
    all_goals cases small <;>
      by_cases present : s.regs.rbx.toNat < s.regs.r8.toNat <;>
      simp [selectFlag, get, Reg64s.get64, StatusFlags.from_result, byte_append, hbpl, present]
  | true =>
    natadd_step 271 using hc
    natadd_step 272 using hc
    natadd_step 273 using hc
    constructor
    all_goals apply hp
    all_goals cases small <;>
      by_cases present : s.regs.rbx.toNat < s.regs.r8.toNat <;>
      simp [selectFlag, get, Reg64s.get64, StatusFlags.from_result, byte_append, hbpl, present]

theorem right_branch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (mirror : Bool) (P : MachineState → Prop)
    (hp : Eventually (step e) P (s,
      if s.status.zf then base + 960 else if mirror then base + 1055 else base + 1029)) :
    Eventually (step e) P (s, if mirror then base + 1053 else base + 1027) := by
  have target := hc.targets ("natAdd_u960", 960) (by decide)
  cases mirror with
  | false =>
    natadd_step 268 using hc
    cases hz : s.status.zf <;> simpa [target, hz, Effects.All] using hp
  | true =>
    natadd_step 274 using hc
    cases hz : s.status.zf <;> simpa [target, hz, Effects.All] using hp

end SszX86.NatAdd.Carry.Fetch

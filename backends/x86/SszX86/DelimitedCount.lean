import SszX86.DelimitedMath

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def countState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbp := UInt64.ofBitVec (s.regs.r13.toBitVec >>> 61)
      r14 := UInt64.ofBitVec (s.regs.rbx.toBitVec + s.regs.r13.toBitVec * 8)
      rax := 2305843009213693953}
    status := flags}

/-- The SHR high word and scaled LEA low word are literal linked instructions.
Only the dead shift flags are abstracted before the threshold comparison. -/
theorem count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (countState s flags, if 2^61 < s.regs.rcx.toNat then base + 269 else base + 133)) :
    Eventually (step e) P (s, base + 103) := by
  have target := hc.targets ("delimited_u269", 269) (by decide)
  have rest (flags : StatusFlags) : Eventually (step e) P
      ({s with
        regs := {s.regs with rbp := UInt64.ofBitVec (s.regs.r13.toBitVec >>> 61)}
        status := flags}, base + 110) := by
    delimited_step 32 using hc
    delimited_step 33 using hc
    delimited_step 34 using hc
    delimited_step 35 using hc
    by_cases large : 2^61 < s.regs.rcx.toNat
    · have hn : ¬ s.regs.rcx.toNat < 2305843009213693953 := by omega
      simpa [large, hn, target, countState, StatusFlags.from_result,
        Effects.All, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        BitVec.add_comm] using hp _
    · have hn : s.regs.rcx.toNat < 2305843009213693953 := by omega
      simpa [large, hn, countState, StatusFlags.from_result,
        Effects.All, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
        BitVec.add_comm] using hp _
  delimited_step 30 using hc
  delimited_step 31 using hc
  simp (config := {instances := true})
    [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, Effects.All]
  repeat' apply And.intro
  all_goals exact rest _

/-- Small native Nat is (zero pointer, immediate count), with no arena access. -/
theorem small_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0, r15 := s.regs.r14}, status := flags}, base + 139)) :
    Eventually (step e) P (s, base + 133) := by
  delimited_step 36 using hc
  constructor <;> delimited_step 37 using hc
  all_goals exact hp _

/-- Both allocation sizes converge on the same two valid Option tags. -/
theorem small_option_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : BitVec 32)
    (hl : Mem.loadInt s.dmem s.regs.rsi.toBitVec 4 = some (tag.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if tag = 1#32 then base + 374 else base + 523)) :
    Eventually (step e) P (s, base + 139) := by
  have target := hc.targets ("delimited_u374", 374) (by decide)
  delimited_step 38 using hc
  delimited_load hl
  delimited_step 39 using hc
  by_cases one : tag = 1#32
  · simpa [one, target, StatusFlags.from_result, Effects.All] using hp _
  · have unequal : tag - 1#32 ≠ 0#32 := by
      intro hz
      apply one
      bv_omega
    simp [StatusFlags.from_result, unequal, Effects.All]
    delimited_step 40 using hc
    simpa [one] using hp _

end SszX86.Delimited

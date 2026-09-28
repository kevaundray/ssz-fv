import SszX86.NatMulReserveExec

namespace SszX86.NatMul.Reservation

def countState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r14 := UInt64.ofBitVec (s.regs.r13.toBitVec + s.regs.r12.toBitVec)}
    status := flags}

/-- The carry branch precedes every byte-count or arena check. -/
theorem count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (countState s flags, if s.regs.r12.toNat + s.regs.r13.toNat < 2^64
        then base + 287 else base + 746)) :
    Eventually (step e) P (s, base + 275) := by
  have target := hc.targets ("natMul_u746", 746) (by decide)
  natmul_step 2 row 26 using hc
  natmul_step 2 row 27 using hc
  natmul_step 2 row 28 using hc
  by_cases bound : s.regs.r12.toNat + s.regs.r13.toNat < 2^64
  · have carry : ¬ Udivti3.radix ≤ s.regs.r12.toNat + s.regs.r13.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_left bound] at next
    simpa [countState, StatusFlags.from_result, carry, Effects.All, UInt64.add_comm] using next _
  · have carry : Udivti3.radix ≤ s.regs.r12.toNat + s.regs.r13.toNat := by
      dsimp [Udivti3.radix]; omega
    rw [ite_eq_right bound] at next
    simpa [countState, StatusFlags.from_result, carry, target, Effects.All, UInt64.add_comm] using next _

def lengthState (s : MachineData) (scratch8 scratch11 : UInt64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec (s.regs.r14.toBitVec * 8#64)
      r8 := scratch8
      r11 := scratch11}
    status := flags}

private theorem length_iff (n : UInt64) :
    ((n.toBitVec >>> (61 : Nat)) = 0#64 ∧ (n.toBitVec * 8#64).toNat < 2^63) ↔
      8 * n.toNat < 2^63 := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    UInt64.toNat_toBitVec, BitVec.toNat_mul]
  have bound := n.toBitVec.isLt
  omega

/-- SHR/SETNE checks multiplication overflow; TEST/SETL checks isize.
Only the low bytes of scratch registers participate in the final OR. -/
theorem length_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ scratch8 scratch11 flags, Eventually (step e) P
      (lengthState s scratch8 scratch11 flags,
        if 8 * s.regs.r14.toNat < 2^63 then base + 393 else base + 318)) :
    Eventually (step e) P (s, base + 287) := by
  have target := hc.targets ("natMul_u393", 393) (by decide)
  have byteNat : (s.regs.r14.toBitVec * 8#64).toNat =
      s.regs.r14.toNat * 8 % 18446744073709551616 := rfl
  simp only [← length_iff, byteNat] at next
  let mark8 := UInt64.ofBitVec ((s.regs.r14.toBitVec >>> (61 : Nat)).replaceLow
    (BitVec.ofNat 8 (!(s.regs.r14.toBitVec >>> (61 : Nat) == 0#64)).toNat))
  let mark11 := UInt64.ofBitVec (s.regs.r11.toBitVec.replaceLow
    (BitVec.ofNat 8 (decide (9223372036854775808 ≤
      s.regs.r14.toNat * 8 % 18446744073709551616)).toNat))
  let beforeOr (flags : StatusFlags) : MachineData :=
    {s with
      regs := {s.regs with
        rdx := UInt64.ofBitVec (s.regs.r14.toBitVec * 8#64)
        r8 := mark8
        r11 := mark11}
      status := flags}
  have joined (flags : StatusFlags) :
      Eventually (step e) P (beforeOr flags, base + 313) := by
    dsimp only [beforeOr]
    natmul_step 3 row 3 using hc
    constructor <;> natmul_step 3 row 4 using hc
    all_goals
      by_cases hm : (s.regs.r14.toBitVec >>> (61 : Nat)) = 0#64 <;>
        by_cases hs : s.regs.r14.toNat * 8 % 18446744073709551616 < 9223372036854775808
      all_goals
        have sign : (9223372036854775808 ≤ s.regs.r14.toNat * 8 % 18446744073709551616) ↔
            ¬ s.regs.r14.toNat * 8 % 18446744073709551616 < 9223372036854775808 := by omega
        have shiftBool : (s.regs.r14.toBitVec >>> (61 : Nat) == 0#64) =
            decide (s.regs.r14.toBitVec >>> (61 : Nat) = 0#64) := by
          by_cases zero : s.regs.r14.toBitVec >>> (61 : Nat) = 0#64
          · simp only [zero, beq_self_eq_true, decide_true]
          · simp only [beq_eq_false_iff_ne.mpr zero, zero, decide_false]
        simpa [lengthState, mark8, mark11, StatusFlags.from_result,
          BitVec.msb_eq_decide, sign, shiftBool, hm, hs, target, Effects.All,
          BitVec.replaceLow, BitVec.drop, BitVec.take, NatCompare.byte_append,
          NatCompare.byte_extract, UInt64.add_comm] using next _ _ _
  let beforeTest (flags : StatusFlags) : MachineData :=
    {s with
      regs := {s.regs with
        rdx := UInt64.ofBitVec (s.regs.r14.toBitVec * 8#64)
        r8 := mark8}
      status := flags}
  have tested (flags : StatusFlags) :
      Eventually (step e) P (beforeTest flags, base + 306) := by
    dsimp only [beforeTest]
    natmul_step 3 row 1 using hc
    constructor <;> natmul_step 3 row 2 using hc
    all_goals
      simpa [beforeOr, mark11, StatusFlags.from_result, BitVec.msb_eq_decide,
        BitVec.replaceLow, BitVec.drop, BitVec.take] using joined _
  natmul_step 2 row 29 using hc
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]
  natmul_step 2 row 30 using hc
  natmul_step 2 row 31 using hc
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    ConstExpr.interp, BitVec.take, StatusFlags.from_result, Effects.All]
  all_goals repeat' apply And.intro
  all_goals
    natmul_step 3 row 0 using hc
    simpa [beforeTest, mark8, StatusFlags.from_result,
      BitVec.replaceLow, BitVec.drop, BitVec.take] using tested _

end SszX86.NatMul.Reservation

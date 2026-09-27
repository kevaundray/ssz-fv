import SszX86.DelimitedMath
import SszDelimited

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem uint64_literal (n : Nat) : (OfNat.ofNat n : UInt64) = UInt64.ofNat n := by
  apply UInt64.toBitVec_inj.1
  exact (UInt64.toBitVec_ofNat n).trans (UInt64.toBitVec_ofNat' n).symm

def retainPrepared (s : MachineData) (length highest : Nat) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec (((BitVec.ofNat 32 highest) ^^^ 7#32).setWidth 64)
      rcx := UInt64.ofNat (SszNative.Delimited.retainedBytes length highest)
      rax := if highest = 0 then 0 else 1
      rsi := 0}
    status := flags}

/-- The byte-aligned delimiter selects len-1; all other delimiter positions
select len. The partial-byte SETNE is preceded by a complete EAX clear. -/
theorem retain_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length highest : Nat) (hbyte : highest < 8)
    (hlen : s.regs.rcx = UInt64.ofNat length)
    (hpred : s.regs.r13 = UInt64.ofNat (length - 1))
    (hbit : s.regs.rbx = UInt64.ofNat highest)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (retainPrepared s length highest flags, base + 540)) :
    Eventually (step e) P (s, base + 523) := by
  have guard : (((BitVec.ofNat 8 highest ^^^ 7#8) - 7#8) == 0#8) =
      decide (highest = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
    simpa using highest_xor highest hbyte
  have widened : (BitVec.ofNat 32 highest).setWidth 64 = BitVec.ofNat 64 highest :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  delimited_step 119 using hc
  constructor <;> delimited_step 120 using hc
  all_goals constructor <;> delimited_step 121 using hc
  all_goals delimited_step 122 using hc
  all_goals delimited_step 123 using hc
  all_goals delimited_step 124 using hc
  all_goals constructor
  all_goals
    by_cases zero : highest = 0 <;>
      simpa (config := {instances := true})
        [hlen, hpred, hbit, UInt64.toBitVec_ofNat', SszNative.Delimited.retainedBytes, retainPrepared,
        StatusFlags.from_result, widened, guard, zero, uint64_literal length,
        uint64_literal (length - 1), Effects.All] using hp _

def retainAdded (s : MachineData) (n : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat n, rsi := 0}, status := flags}

/-- The reconstructed byte count cannot overflow, even when the usize sign bit
is set. SETB therefore publishes a zero carry byte. -/
theorem retain_add_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (length highest : Nat)
    (positive : 0 < length) (physical : length < 2^64)
    (hpred : s.regs.r13 = UInt64.ofNat (length - 1))
    (hcount : s.regs.rax = if highest = 0 then 0 else 1)
    (hzero : s.regs.rsi = 0)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (retainAdded s (SszNative.Delimited.retainedBytes length highest) flags, base + 547)) :
    Eventually (step e) P (s, base + 540) := by
  delimited_step 125 using hc
  delimited_step 126 using hc
  have predBound : length - 1 < 2^64 := by omega
  have noPredCarry : ¬ Udivti3.radix ≤ length - 1 := by
    change ¬ 2^64 ≤ length - 1
    omega
  by_cases zero : highest = 0
  · simpa [hpred, hcount, hzero, zero, SszNative.Delimited.retainedBytes, retainAdded, StatusFlags.from_result,
      Nat.mod_eq_of_lt predBound, noPredCarry, Effects.All] using hp _
  · have plus : length - 1 + 1 = length := by omega
    have advance : UInt64.ofNat (length - 1) + 1 = UInt64.ofNat length := by
      simpa only [UInt64.ofNat_add, UInt64.ofNat_one] using
        congrArg UInt64.ofNat (show length - 1 + 1 = length by omega)
    have noCarry : ¬ Udivti3.radix ≤ length := by
      change ¬ 2^64 ≤ length
      omega
    simpa [hpred, hcount, hzero, zero, SszNative.Delimited.retainedBytes, retainAdded, StatusFlags.from_result,
      Nat.mod_eq_of_lt predBound, noCarry, plus, advance, Effects.All] using hp _

/-- Equality with the already-selected retained length forces the real JNE at
553 to fall through, making the BadRepresentation stores unreachable. -/
theorem retain_check_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (heq : s.regs.rax = s.regs.rcx) (hzero : s.regs.rsi = 0)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 555)) :
    Eventually (step e) P (s, base + 547) := by
  delimited_step 127 using hc
  constructor <;> delimited_step 128 using hc
  all_goals constructor <;> delimited_step 129 using hc
  all_goals simpa [heq, hzero, StatusFlags.from_result, Effects.All] using hp _

end SszX86.Delimited

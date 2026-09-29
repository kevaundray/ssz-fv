import SszArm.IndicesRebaseCountOps
import SszArm.DelimitedContract

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Count

open Dispatch.Block (next put branch)

/-- The route retains the real conditional carry and remainder branches. -/
def incrementOps (low : BitVec 64) : List Op :=
  [.p12, .p16] ++
    (if (AddWithCarry low 1#64 0#1).2.c = 1#1 then [.p28] else [.p20, .p24])

def quotientOps : List Op := [.p32, .p36, .p40, .p44, .p48, .p52, .p56, .p60, .p64]

def roundOps (low : BitVec 64) : List Op :=
  if low &&& 63#64 = 0#64 then [.p68, .p72] else [.p76]

def carryOps (low high : BitVec 64) : List Op :=
  [.p80, .p84] ++
    (if (AddWithCarry (Words.quotientLow low high) (Words.roundWord low) 0#1).2.c = 1#1
      then [.p96] else [.p88, .p92]) ++ [.p100]

def ops (s : ArmState) : List Op :=
  incrementOps (r (.GPR 4#5) s) ++ quotientOps ++
    roundOps (Words.incrementLow (r (.GPR 4#5) s)) ++
    carryOps (Words.incrementLow (r (.GPR 4#5) s))
      (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s))

@[irreducible] def counted (s : ArmState) : ArmState := block (ops s) s

private theorem logical_zero (value : BitVec 64) :
    (DPI.update_logical_imm_pstate value).z = 1#1 ↔ value = 0#64 := by
  simp [DPI.update_logical_imm_pstate]

theorem count_control (s : ArmState) (base : BitVec 64)
    (entry : read_pc s = base + 12#64) : ControlFlow base (ops s) s := by
  change r .PC s = _ at entry
  by_cases incrementCarry : (AddWithCarry (r (.GPR 4#5) s) 1#64 0#1).2.c = 1#1 <;>
    by_cases remainder : Words.incrementLow (r (.GPR 4#5) s) &&& 63#64 = 0#64 <;>
    by_cases countCarry :
      (AddWithCarry
        (Words.quotientLow (Words.incrementLow (r (.GPR 4#5) s))
          (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)))
        (Words.roundWord (Words.incrementLow (r (.GPR 4#5) s))) 0#1).2.c = 1#1
  all_goals
    simp_all (config := {decide := true, instances := true})
      [ops, incrementOps, quotientOps, roundOps, carryOps, ControlFlow, Op.row,
       Op.effect, next, put, branch, Udivti3.flagged, Udivti3.next,
       Words.incrementLow, Words.incrementHigh, Words.quotientLow,
       Words.quotientHigh, Words.roundWord, Udivti3.adc_value,
       state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, logical_zero]

theorem count_run (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (entry : read_pc s = base + 12#64) :
    run (ops s).length s = counted s :=
  block_run (ops s) s base code error aligned (count_control s base entry)

/-- The concrete state at the checked-usize dispatch preserves the original
operand and arena registers and exposes both halves of the increment and count. -/
theorem counted_values (s : ArmState) :
    r (.GPR 8#5) (counted s) =
      Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s) ∧
    r (.GPR 9#5) (counted s) = Words.incrementLow (r (.GPR 4#5) s) ∧
    r (.GPR 10#5) (counted s) =
      Words.countLow (Words.incrementLow (r (.GPR 4#5) s))
        (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)) ∧
    r (.GPR 11#5) (counted s) =
      Words.countHigh (Words.incrementLow (r (.GPR 4#5) s))
        (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)) := by
  by_cases incrementCarry : (AddWithCarry (r (.GPR 4#5) s) 1#64 0#1).2.c = 1#1 <;>
    by_cases remainder : Words.incrementLow (r (.GPR 4#5) s) &&& 63#64 = 0#64 <;>
    by_cases countCarry :
      (AddWithCarry
        (Words.quotientLow (Words.incrementLow (r (.GPR 4#5) s))
          (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)))
        (Words.roundWord (Words.incrementLow (r (.GPR 4#5) s))) 0#1).2.c = 1#1
  all_goals
    simp_all (config := {decide := true, instances := true})
      [counted, block, ops, incrementOps, quotientOps, roundOps, carryOps,
       Op.effect, next, put, branch, Udivti3.flagged, Udivti3.next,
       Words.incrementLow, Words.incrementHigh, Words.quotientLow,
       Words.quotientHigh, Words.roundWord, Words.countLow, Words.countHigh,
       Udivti3.adc_value, state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem counted_pc (s : ArmState) (base : BitVec 64)
    (entry : read_pc s = base + 12#64) :
    read_pc (counted s) =
      if Words.countHigh (Words.incrementLow (r (.GPR 4#5) s))
          (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)) = 0#64
      then base + 304#64 else base + 104#64 := by
  change r .PC s = _ at entry
  by_cases incrementCarry : (AddWithCarry (r (.GPR 4#5) s) 1#64 0#1).2.c = 1#1 <;>
    by_cases remainder : Words.incrementLow (r (.GPR 4#5) s) &&& 63#64 = 0#64 <;>
    by_cases countCarry :
      (AddWithCarry
        (Words.quotientLow (Words.incrementLow (r (.GPR 4#5) s))
          (Words.incrementHigh (r (.GPR 4#5) s) (r (.GPR 5#5) s)))
        (Words.roundWord (Words.incrementLow (r (.GPR 4#5) s))) 0#1).2.c = 1#1
  all_goals
    simp_all (config := {decide := true, instances := true})
      [counted, block, ops, incrementOps, quotientOps, roundOps, carryOps,
       Op.effect, next, put, branch, Udivti3.flagged, Udivti3.next,
       Words.incrementLow, Words.incrementHigh, Words.quotientLow,
       Words.quotientHigh, Words.roundWord, Words.countHigh, Udivti3.adc_value,
       state_simp_rules, BitVec.add_assoc, BitVec.sub_eq_add_neg, apply_ite]

theorem counted_registers (s : ArmState) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) (h10 : reg ≠ 10#5)
    (h11 : reg ≠ 11#5) (h12 : reg ≠ 12#5) :
    r (.GPR reg) (counted s) = r (.GPR reg) s := by
  unfold counted ops incrementOps roundOps carryOps
  split <;> split <;> split <;>
    simp [block, quotientOps, Op.effect, next, put, branch, Udivti3.flagged,
      Udivti3.next, state_simp_rules, h8, h9, h10, h11, h12,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

@[simp] theorem counted_program (s : ArmState) : (counted s).program = s.program := by
  simp [counted]

@[simp] theorem counted_error (s : ArmState) : read_err (counted s) = read_err s := by
  simp [counted]

@[simp] theorem counted_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (counted s) = r (.SFP reg) s := by
  simp [counted]

theorem counted_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (counted s) := block_aligned (ops s) s aligned

/-- Only the original X11 spill is written during the checked count prefix. -/
theorem counted_memory (s : ArmState) :
    (counted s).mem = (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (r (.GPR 11#5) s) s).mem := by
  unfold counted ops incrementOps roundOps carryOps
  split <;> split <;> split <;>
    simp [block, quotientOps, Op.effect, next, put, branch, Udivti3.flagged,
      Udivti3.next, state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc]

def writes (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16)]

theorem counted_frame (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame (writes s) s (counted s) := by
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    have bound := (r (.GPR 31#5) s).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [writes])
  simp only [Prod.fst, Prod.snd] at apart
  rw [counted_memory]
  apply BoolCodec.write_mem_bytes_frame
  · rw [pointer]
    have bound := (r (.GPR 31#5) s).isLt
    omega
  · rw [pointer]
    omega

end SszArm.Indices.Rebase.Count

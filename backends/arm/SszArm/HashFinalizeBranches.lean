import SszArm.HashFinalizeControl

namespace SszArm.Hash.Finalize

theorem guard_pc (s : ArmState) (aligned : CheckSPAlignment s)
    (bound : (r (.GPR 8#5) s).toNat < 64) :
    read_pc (guardState s) = read_pc s + 8#64 := by
  have high := Udivti3.cmp_high (r (.GPR 8#5) s) 63#64
  have safe : ¬ ((AddWithCarry (r (.GPR 8#5) s) (~~~63#64) 1#1).2.c = 1#1 ∧
      (AddWithCarry (r (.GPR 8#5) s) (~~~63#64) 1#1).2.z = 0#1) := by
    rw [high]
    simpa using bound
  arm_word_nf at safe
  simp (config := {decide := true, instances := true})
    [guardState, effect, guardOps, p16, p20, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, safe, BitVec.add_assoc]

theorem overflow_guard_pc (s : ArmState) (aligned : CheckSPAlignment s)
    (bound : (r (.GPR 0#5) s).toNat ≤ 64) :
    read_pc (overflowGuardState s) = read_pc s + 8#64 := by
  have high := Udivti3.cmp_high (r (.GPR 0#5) s) 64#64
  have safe : ¬ ((AddWithCarry (r (.GPR 0#5) s) (~~~64#64) 1#1).2.c = 1#1 ∧
      (AddWithCarry (r (.GPR 0#5) s) (~~~64#64) 1#1).2.z = 0#1) := by
    rw [high]
    simpa using bound
  arm_word_nf at safe
  simp (config := {decide := true, instances := true})
    [overflowGuardState, effect, overflowGuardOps, p84, p88, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, safe, BitVec.add_assoc]

def preparedCount (s : ArmState) : BitVec 64 :=
  read_mem_bytes 8 (r (.GPR 1#5) s + 96#64) s + 1#64

theorem prepare_observe (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 0#5) (prepareState s) = preparedCount s ∧
    r (.GPR 8#5) (prepareState s) = read_mem_bytes 8 (r (.GPR 1#5) s + 96#64) s ∧
    r (.GPR 19#5) (prepareState s) = r (.GPR 0#5) s ∧
    r (.GPR 20#5) (prepareState s) = r (.GPR 1#5) s ∧
    (prepareState s).mem =
      (write_mem_bytes 8 (r (.GPR 1#5) s + 96#64) (preparedCount s) s).mem := by
  simp (config := {decide := true, instances := true})
    [prepareState, effect, prepareOps, p56, p60, p64, p68, p72, p76, p80,
     preparedCount, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, BitVec.add_assoc, Memory.write_mem_bytes_eq_mem_write_bytes]

theorem prepare_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (prepareState s) = read_pc s +
      if (preparedCount s).toNat ≤ 56 then 112#64 else 28#64 := by
  have high := Udivti3.cmp_high (preparedCount s) 56#64
  arm_word_nf at high
  simp (config := {decide := true, instances := true})
    [prepareState, effect, prepareOps, p56, p60, p64, p68, p72, p76, p80,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     aligned, ← preparedCount, high, BitVec.add_assoc]
  all_goals split <;> simp_all <;> omega

end SszArm.Hash.Finalize

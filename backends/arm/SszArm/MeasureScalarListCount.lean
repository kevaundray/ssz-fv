import SszArm.MeasureScalarListMath

namespace SszArm.Measure.Scalar.Bytes

open Result

@[irreducible] def listCountReady (s : ArmState) (base : BitVec 64) (count : Nat) : ArmState :=
  w .PC (base + 2332#64) (w (.GPR 11#5) (BitVec.ofNat 64 count) s)

theorem list_count_run (s : ArmState) (base : BitVec 64) (count : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (if count = 0 then 2328 else 868))
    (bound : count < 2^64)
    (remembered : count ≠ 0 → r (.GPR 11#5) s + 1#64 = BitVec.ofNat 64 (count - 1)) :
    run (if count = 0 then 1 else 2) s = listCountReady s base count := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  by_cases zero : count = 0
  · subst count
    have follows : Follows base [p2328] s := by
      simpa [Follows, p2328, r, read_base_pc, read_pc, read_err] using And.intro error (And.intro pc trivial)
    rw [show (if 0 = 0 then 1 else 2) = [p2328].length by rfl, runs _ s base code follows]
    simp (config := {decide := true, instances := true})
      [effect, p2328, Op.effect, exec_inst, listCountReady, state_simp_rules,
       bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc]
  · have increment : r (.GPR 11#5) s + 2#64 = BitVec.ofNat 64 count := by
      have index := remembered zero
      bv_omega
    have follows : Follows base [p868, p872] s := by
      simp (config := {decide := true, instances := true})
        [Follows, p868, p872, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
         minimal_theory, pc, zero, error, BitVec.add_assoc]
    rw [if_neg zero, show 2 = [p868, p872].length by rfl, runs _ s base code follows]
    simp (config := {decide := true, instances := true})
      [effect, p868, p872, Op.effect, exec_inst, listCountReady, state_simp_rules,
       bitvec_rules, minimal_theory, pc, zero, increment, BitVec.add_assoc,
       NatExact.gpr_w_pc, w_of_w_shadow]

theorem list_count_frame (s : ArmState) (base : BitVec 64) (count : Nat) :
    NatNarrow.Frame s (listCountReady s base count) := by
  constructor
  · simp [listCountReady, state_simp_rules]
  · simp [listCountReady, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [listCountReady, state_simp_rules]
  · intro reg; simp [listCountReady, state_simp_rules]
  · intro address outside; simp [listCountReady, state_simp_rules]

end SszArm.Measure.Scalar.Bytes

import SszArm.BoolExec

namespace SszArm.BoolCodec

/-- The five actual unconditional edges between Boolean store blocks. -/
def storeJumps : List (Nat × Nat) :=
  [(684, 4504), (2244, 4732), (4140, 4504), (4296, 4720), (4540, 4732)]

theorem jump_to (s : ArmState) (base : BitVec 64) (offset target : Nat)
    (hj : (offset, target) ∈ storeJumps) (hc : CodeAt s base)
    (hp : read_pc s = base + BitVec.ofNat 64 offset) (he : read_err s = .None) :
    stepi s = w .PC (base + BitVec.ofNat 64 target) s := by
  simp only [storeJumps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hj
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals have hpc : r .PC s = _ := hp
  · have hf := hc (684, 0x140003bb#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]
  · have hf := hc (2244, 0x1400026e#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]
  · have hf := hc (4140, 0x1400005b#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]
  · have hf := hc (4296, 0x1400006a#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]
  · have hf := hc (4540, 0x14000030#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hpc, BitVec.add_assoc]

end SszArm.BoolCodec

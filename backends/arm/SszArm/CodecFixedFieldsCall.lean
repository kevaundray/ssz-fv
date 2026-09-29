import SszArm.CodecFixedBody

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)

def fieldCallOps : List Op := [.p108, .p112, .p116, .p120]

theorem field_call_pcs (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 108#64) (nonempty : r (.GPR 19#5) s ≠ 0#64) :
    PCs base fieldCallOps s := by
  change r .PC s = _ at pc
  simp [fieldCallOps, PCs, Op.row, Op.effect, next, put, branch,
    state_simp_rules, pc, nonempty, BitVec.add_assoc]

theorem field_call_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 108#64) (nonempty : r (.GPR 19#5) s ≠ 0#64) :
    run 4 s = block fieldCallOps s :=
  run_block fieldCallOps s base code error aligned (field_call_pcs s base pc nonempty)

theorem field_call_arguments (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 108#64) (nonempty : r (.GPR 19#5) s ≠ 0#64) :
    read_pc (block fieldCallOps s) = base ∧
    r (.GPR 0#5) (block fieldCallOps s) = read_mem_bytes 8 (r (.GPR 8#5) s + 16#64) s ∧
    r (.GPR 19#5) (block fieldCallOps s) = r (.GPR 19#5) s ∧
    r (.GPR 20#5) (block fieldCallOps s) = r (.GPR 8#5) s + 24#64 ∧
    r (.GPR 30#5) (block fieldCallOps s) = base + 124#64 ∧
    r (.GPR 31#5) (block fieldCallOps s) = r (.GPR 31#5) s := by
  change r .PC s = _ at pc
  simp [fieldCallOps, block, Op.effect, next, put, branch,
    state_simp_rules, pc, nonempty, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem field_call_memory (s : ArmState) : (block fieldCallOps s).mem = s.mem := by
  simp [fieldCallOps, block, Op.effect, next, put, branch, state_simp_rules]

theorem field_call_register (s : ArmState) (reg : BitVec 5)
    (different : reg ≠ 0#5 ∧ reg ≠ 20#5 ∧ reg ≠ 30#5) :
    r (.GPR reg) (block fieldCallOps s) = r (.GPR reg) s := by
  rcases different with ⟨h0, h20, h30⟩
  simp [fieldCallOps, block, Op.effect, next, put, branch,
    state_simp_rules, h0, h20, h30]

theorem BodyContext.field_call {source current : ArmState} (context : BodyContext source current) :
    BodyContext source (block fieldCallOps current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨(field_call_register current 31#5 (by decide)).trans context.saved.sp, ?_, ?_, ?_⟩
    all_goals rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (field_call_memory current))]
    · exact context.saved.link
    · exact context.saved.first
    · exact context.saved.second
  · intro reg lower upper h19 h20 h30
    exact (field_call_register current reg ⟨by bv_omega, h20, h30⟩).trans
      (context.registers reg lower upper h19 h20 h30)
  · intro reg lower upper
    rw [block_vector]
    exact context.vectors reg lower upper

end SszArm.Codec.Fixed.IsFixed

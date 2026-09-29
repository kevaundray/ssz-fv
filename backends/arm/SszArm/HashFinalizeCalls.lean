import SszArm.HashFinalizeControl

namespace SszArm.Hash.Finalize

theorem overflow_zero_arguments (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 92#64) :
    read_pc (overflowZeroCallState s) = base + memsetOffset ∧
    r (.GPR 30#5) (overflowZeroCallState s) = base + finalizeOffset + 112#64 ∧
    r (.GPR 0#5) (overflowZeroCallState s) = r (.GPR 20#5) s + r (.GPR 0#5) s ∧
    r (.GPR 1#5) (overflowZeroCallState s) = 0#64 ∧
    r (.GPR 2#5) (overflowZeroCallState s) = 63#64 - r (.GPR 8#5) s := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [overflowZeroCallState, effect, overflowZeroCallOps, p92, p96, p100, p104, p108,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, finalizeOffset, memsetOffset, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem overflow_compress_arguments (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 112#64) :
    read_pc (overflowCompressCallState s) = base + compressOffset ∧
    r (.GPR 30#5) (overflowCompressCallState s) = base + finalizeOffset + 124#64 ∧
    r (.GPR 0#5) (overflowCompressCallState s) = r (.GPR 20#5) s + 64#64 ∧
    r (.GPR 1#5) (overflowCompressCallState s) = r (.GPR 20#5) s := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [overflowCompressCallState, effect, overflowCompressCallOps, p112, p116, p120,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, finalizeOffset, compressOffset, BitVec.add_assoc, BitVec.sub_eq_add_neg]

theorem last_zero_arguments (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + finalizeOffset + 168#64) :
    read_pc (lastZeroCallState s) = base + memsetOffset ∧
    r (.GPR 30#5) (lastZeroCallState s) = base + finalizeOffset + 188#64 ∧
    r (.GPR 0#5) (lastZeroCallState s) = r (.GPR 20#5) s + r (.GPR 0#5) s ∧
    r (.GPR 1#5) (lastZeroCallState s) = 0#64 ∧
    r (.GPR 2#5) (lastZeroCallState s) = 56#64 - r (.GPR 0#5) s := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [lastZeroCallState, effect, lastZeroCallOps, p168, p172, p176, p180, p184,
     Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     pc, finalizeOffset, memsetOffset, BitVec.add_assoc, BitVec.sub_eq_add_neg]

end SszArm.Hash.Finalize

import SszArm.HashFinalizeScalar
import SszArm.HashFinalizeCompression
import SszArm.Udivti3Arithmetic

namespace SszArm.Hash.Finalize

private theorem memory_p16 (s : ArmState) : (p16.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p16, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p20 (s : ArmState) : (p20.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p20, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     apply_ite, ArmState.mem_w_eq_mem, ite_self]

private theorem memory_p84 (s : ArmState) : (p84.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p84, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p88 (s : ArmState) : (p88.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p88, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     apply_ite, ArmState.mem_w_eq_mem, ite_self]

private theorem memory_p92 (s : ArmState) : (p92.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p92, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p96 (s : ArmState) : (p96.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p96, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p100 (s : ArmState) : (p100.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p100, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p104 (s : ArmState) : (p104.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p104, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p108 (s : ArmState) : (p108.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p108, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p112 (s : ArmState) : (p112.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p112, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p116 (s : ArmState) : (p116.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p116, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p120 (s : ArmState) : (p120.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p120, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p168 (s : ArmState) : (p168.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p168, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p172 (s : ArmState) : (p172.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p172, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p176 (s : ArmState) : (p176.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p176, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p180 (s : ArmState) : (p180.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p180, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p184 (s : ArmState) : (p184.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p184, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem memory_p544 (s : ArmState) : (p544.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p544, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     apply_ite, ArmState.mem_w_eq_mem, ite_self]

private theorem memory_p548 (s : ArmState) : (p548.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p548, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     apply_ite, ArmState.mem_w_eq_mem, ite_self]

private theorem memory_p552 (s : ArmState) : (p552.effect s).mem = s.mem := by
  simp (config := {decide := true, instances := true}) only
    [p552, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     ArmState.mem_w_eq_mem]

private theorem sp_p28 (s : ArmState) :
    r (.GPR 31#5) (p28.effect s) = r (.GPR 31#5) s - 16#64 := by
  change r (.GPR 31#5)
    (write_gpr 64 31#5 (AddWithCarry (read_gpr 64 31#5 s) (~~~16#64) 1#1).1
      (write_pc (read_pc s + 4#64) s)) = _
  rw [write_gpr, r_of_w_same, BitVec.setWidth_eq, fst_AddWithCarry_eq_sub_neg,
    BitVec.not_not, read_gpr, BitVec.setWidth_eq]

private theorem sp_p52 (s : ArmState) :
    r (.GPR 31#5) (p52.effect s) = r (.GPR 31#5) s + 16#64 := by
  change r (.GPR 31#5)
    (write_gpr 64 31#5 (AddWithCarry (read_gpr 64 31#5 s) 16#64 0#1).1
      (write_pc (read_pc s + 4#64) s)) = _
  rw [write_gpr, r_of_w_same, BitVec.setWidth_eq, fst_AddWithCarry_eq_add,
    read_gpr, BitVec.setWidth_eq]

private theorem sp_p128 (s : ArmState) :
    r (.GPR 31#5) (p128.effect s) = r (.GPR 31#5) s - 16#64 := by
  change r (.GPR 31#5)
    (write_gpr 64 31#5 (AddWithCarry (read_gpr 64 31#5 s) (~~~16#64) 1#1).1
      (write_pc (read_pc s + 4#64) s)) = _
  rw [write_gpr, r_of_w_same, BitVec.setWidth_eq, fst_AddWithCarry_eq_sub_neg,
    BitVec.not_not, read_gpr, BitVec.setWidth_eq]

private theorem sp_p164 (s : ArmState) :
    r (.GPR 31#5) (p164.effect s) = r (.GPR 31#5) s + 16#64 := by
  change r (.GPR 31#5)
    (write_gpr 64 31#5 (AddWithCarry (read_gpr 64 31#5 s) 16#64 0#1).1
      (write_pc (read_pc s + 4#64) s)) = _
  rw [write_gpr, r_of_w_same, BitVec.setWidth_eq, fst_AddWithCarry_eq_add,
    read_gpr, BitVec.setWidth_eq]

theorem guard_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (guardState s).mem = s.mem := by
  simp only [guardState, effect, guardOps, List.foldl_cons, List.foldl_nil]
  rw [memory_p20, memory_p16]

theorem overflowGuard_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (overflowGuardState s).mem = s.mem := by
  simp only [overflowGuardState, effect, overflowGuardOps, List.foldl_cons, List.foldl_nil]
  rw [memory_p88, memory_p84]

theorem overflowZeroCall_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (overflowZeroCallState s).mem = s.mem := by
  simp only [overflowZeroCallState, effect, overflowZeroCallOps, List.foldl_cons, List.foldl_nil]
  rw [memory_p108, memory_p104, memory_p100, memory_p96, memory_p92]

theorem overflowCompressCall_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (overflowCompressCallState s).mem = s.mem := by
  simp only [overflowCompressCallState, effect, overflowCompressCallOps,
    List.foldl_cons, List.foldl_nil]
  rw [memory_p120, memory_p116, memory_p112]

theorem lastZeroCall_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (lastZeroCallState s).mem = s.mem := by
  simp only [lastZeroCallState, effect, lastZeroCallOps, List.foldl_cons, List.foldl_nil]
  rw [memory_p184, memory_p180, memory_p176, memory_p172, memory_p168]

theorem return_memory (s : ArmState) (aligned : CheckSPAlignment s) :
    (returnState s).mem = s.mem := by
  simp only [returnState, effect, returnOps, List.foldl_cons, List.foldl_nil]
  rw [memory_p552, memory_p548, memory_p544]

theorem BufferAt.of_memory {s t u : ArmState} {buf : Vector UInt8 64}
    {words : Vector UInt32 8} {byteLen : UInt64}
    (stored : BufferAt s t buf words byteLen) (memory : u.mem = t.mem) :
    BufferAt s u buf words byteLen := by
  have frame : Delimited.MemoryFrame [] t u := fun _ _ => congrFun memory _
  constructor
  · intro i
    change u.mem _ = _
    rw [memory]
    exact stored.buffer i
  · intro i
    have same : read_mem_bytes 4 (statePtr s + 64#64 + BitVec.ofNat 64 (4 * i.val)) u =
        read_mem_bytes 4 (statePtr s + 64#64 + BitVec.ofNat 64 (4 * i.val)) t := by
      apply BoolCodec.read_bytes_congr
      intro j hj
      change u.mem _ = t.mem _
      rw [memory]
    exact same.trans (stored.chaining i)
  · have same : read_mem_bytes 8 (statePtr s + 104#64) u =
        read_mem_bytes 8 (statePtr s + 104#64) t := by
      apply BoolCodec.read_bytes_congr
      intro j hj
      change u.mem _ = t.mem _
      rw [memory]
    exact same.trans stored.length

theorem guard_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (guardState s) = r (.GPR 31#5) s :=
  (guard_scalar s aligned).registers 31#5 (by decide)

theorem delimiter_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (delimiterState s) = r (.GPR 31#5) s := by
  let t1 := p24.effect s
  have step1 := scalar_p24 s aligned
  let t2 := p28.effect t1
  have step2 := scalar_p28 t1 step1.aligned
  let t3 := p32.effect t2
  have step3 := scalar_p32 t2 step2.aligned
  let t4 := p36.effect t3
  have step4 := scalar_p36 t3 step3.aligned
  let t5 := p40.effect t4
  have step5 := scalar_p40 t4 step4.aligned
  let t6 := p44.effect t5
  have step6 := scalar_p44 t5 step5.aligned
  let t7 := p48.effect t6
  have step7 := scalar_p48 t6 step6.aligned
  unfold delimiterState
  change r (.GPR 31#5) (p52.effect t7) = r (.GPR 31#5) s
  rw [sp_p52, step7.frame.registers 31#5 (by decide),
    step6.frame.registers 31#5 (by decide), step5.frame.registers 31#5 (by decide),
    step4.frame.registers 31#5 (by decide), step3.frame.registers 31#5 (by decide),
    sp_p28, step1.frame.registers 31#5 (by decide), BitVec.sub_add_cancel]

theorem prepare_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (prepareState s) = r (.GPR 31#5) s :=
  (prepare_scalar s aligned).registers 31#5 (by decide)

theorem overflowGuard_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (overflowGuardState s) = r (.GPR 31#5) s :=
  (overflowGuard_scalar s aligned).registers 31#5 (by decide)

theorem overflowZeroCall_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (overflowZeroCallState s) = r (.GPR 31#5) s :=
  (overflowZeroCall_scalar s aligned).registers 31#5 (by decide)

theorem overflowCompressCall_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (overflowCompressCallState s) = r (.GPR 31#5) s :=
  (overflowCompressCall_scalar s aligned).registers 31#5 (by decide)

theorem reset_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (resetState s) = r (.GPR 31#5) s := by
  let t1 := p124.effect s
  have step1 := scalar_p124 s aligned
  let t2 := p128.effect t1
  have step2 := scalar_p128 t1 step1.aligned
  let t3 := p132.effect t2
  have step3 := scalar_p132 t2 step2.aligned
  let t4 := p136.effect t3
  have step4 := scalar_p136 t3 step3.aligned
  let t5 := p140.effect t4
  have step5 := scalar_p140 t4 step4.aligned
  let t6 := p144.effect t5
  have step6 := scalar_p144 t5 step5.aligned
  let t7 := p148.effect t6
  have step7 := scalar_p148 t6 step6.aligned
  let t8 := p152.effect t7
  have step8 := scalar_p152 t7 step7.aligned
  let t9 := p156.effect t8
  have step9 := scalar_p156 t8 step8.aligned
  let t10 := p160.effect t9
  have step10 := scalar_p160 t9 step9.aligned
  unfold resetState
  change r (.GPR 31#5) (p164.effect t10) = r (.GPR 31#5) s
  rw [sp_p164, step10.frame.registers 31#5 (by decide),
    step9.frame.registers 31#5 (by decide), step8.frame.registers 31#5 (by decide),
    step7.frame.registers 31#5 (by decide), step6.frame.registers 31#5 (by decide),
    step5.frame.registers 31#5 (by decide), step4.frame.registers 31#5 (by decide),
    step3.frame.registers 31#5 (by decide), sp_p128,
    step1.frame.registers 31#5 (by decide), BitVec.sub_add_cancel]

theorem lastZeroCall_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (lastZeroCallState s) = r (.GPR 31#5) s :=
  (lastZeroCall_scalar s aligned).registers 31#5 (by decide)

theorem lengthCall_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (lengthCallState s) = r (.GPR 31#5) s :=
  (lengthCall_scalar s aligned).registers 31#5 (by decide)

theorem emit0_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit0State s) = r (.GPR 31#5) s :=
  (emit0_scalar s aligned).registers 31#5 (by decide)

theorem emit1_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit1State s) = r (.GPR 31#5) s :=
  (emit1_scalar s aligned).registers 31#5 (by decide)

theorem emit2_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit2State s) = r (.GPR 31#5) s :=
  (emit2_scalar s aligned).registers 31#5 (by decide)

theorem emit3_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit3State s) = r (.GPR 31#5) s :=
  (emit3_scalar s aligned).registers 31#5 (by decide)

theorem emit4_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit4State s) = r (.GPR 31#5) s :=
  (emit4_scalar s aligned).registers 31#5 (by decide)

theorem emit5_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit5State s) = r (.GPR 31#5) s :=
  (emit5_scalar s aligned).registers 31#5 (by decide)

theorem emit6_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit6State s) = r (.GPR 31#5) s :=
  (emit6_scalar s aligned).registers 31#5 (by decide)

theorem emit7_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit7State s) = r (.GPR 31#5) s :=
  (emit7_scalar s aligned).registers 31#5 (by decide)

theorem emit8_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit8State s) = r (.GPR 31#5) s :=
  (emit8_scalar s aligned).registers 31#5 (by decide)

theorem emit9_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit9State s) = r (.GPR 31#5) s :=
  (emit9_scalar s aligned).registers 31#5 (by decide)

theorem emit10_sp (s : ArmState) (aligned : CheckSPAlignment s) :
    r (.GPR 31#5) (emit10State s) = r (.GPR 31#5) s :=
  (emit10_scalar s aligned).registers 31#5 (by decide)

end SszArm.Hash.Finalize

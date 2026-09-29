import SszArm.HashFinalizeDigest2

namespace SszArm.Hash.Finalize

theorem emit0_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit0State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit0State, effect, emit0Ops, p216, p220, p224, p228, p232, p236, p240, p244, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit1_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit1State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit1State, effect, emit1Ops, p248, p252, p256, p260, p264, p268, p272, p276, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit2_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit2State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit2State, effect, emit2Ops, p280, p284, p288, p292, p296, p300, p304, p308, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit3_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit3State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit3State, effect, emit3Ops, p312, p316, p320, p324, p328, p332, p336, p340, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit4_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit4State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit4State, effect, emit4Ops, p344, p348, p352, p356, p360, p364, p368, p372, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit5_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit5State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit5State, effect, emit5Ops, p376, p380, p384, p388, p392, p396, p400, p404, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit6_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit6State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit6State, effect, emit6Ops, p408, p412, p416, p420, p424, p428, p432, p436, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit7_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit7State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit7State, effect, emit7Ops, p440, p444, p448, p452, p456, p460, p464, p468, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit8_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit8State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit8State, effect, emit8Ops, p472, p476, p480, p484, p488, p492, p496, p500, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit9_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit9State s) = read_pc s + 32#64 := by
  simp (config := {decide := true, instances := true})
    [emit9State, effect, emit9Ops, p504, p508, p512, p516, p520, p524, p528, p532, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

theorem emit10_pc (s : ArmState) (aligned : CheckSPAlignment s) :
    read_pc (emit10State s) = read_pc s + 8#64 := by
  simp (config := {decide := true, instances := true})
    [emit10State, effect, emit10Ops, p536, p540, Op.effect, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, aligned, BitVec.add_assoc]

def digestWritten : List (Fin 32) := [⟨0, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨10, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨18, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨26, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨30, by decide⟩, ⟨29, by decide⟩]

theorem digest_written_all (i : Fin 32) : i ∈ digestWritten := by
  have all : ∀ j : Fin 32, j ∈ digestWritten := by decide
  exact all i

theorem digest_run (s t : ArmState) (base : BitVec 64) (words : Vector UInt32 8)
    (code : CodeAt s base) (g : Geometry s) (aligned : CheckSPAlignment s)
    (live : Live s t) (chaining : ChainingAt t (statePtr s + 64#64) words)
    (pc : read_pc t = base + finalizeOffset + 216#64) :
    ∃ u, run 82 t = u ∧ Live s u ∧
      BytesAt u (outputPtr s) (Ssz.Sha256.digest words) ∧
      read_pc u = base + finalizeOffset + 544#64 := by
  have done0 : DigestAt s t words [] := by intro i member; cases member
  have aligned1 := live.toActivation.aligned aligned
  let u1 := emit0State t
  obtain ⟨regs1, memory1⟩ := emit0_observe s t words g live chaining
  have live1 : Live s u1 := live.emitMemory g (emit0_scalar t aligned1)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit0_sp t aligned1) emit0Written memory1
  have chain1 := chaining.emitMemory g emit0Written memory1
  have done1 : DigestAt s u1 words ([] ++ emit0Written) := by
    intro i member
    rw [memory1]
    exact done0.emitMemory emit0Written g.outputBound i member
  have pc1 : read_pc u1 = base + finalizeOffset + 248#64 := by
    rw [emit0_pc t aligned1, pc]
    simp [BitVec.add_assoc]
  have aligned2 := live1.toActivation.aligned aligned
  let u2 := emit1State u1
  obtain ⟨regs2, memory2⟩ := emit1_observe s u1 words g live1 chain1 regs1
  have live2 : Live s u2 := live1.emitMemory g (emit1_scalar u1 aligned2)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit1_sp u1 aligned2) emit1Written memory2
  have chain2 := chain1.emitMemory g emit1Written memory2
  have done2 : DigestAt s u2 words (([] ++ emit0Written) ++ emit1Written) := by
    intro i member
    rw [memory2]
    exact done1.emitMemory emit1Written g.outputBound i member
  have pc2 : read_pc u2 = base + finalizeOffset + 280#64 := by
    rw [emit1_pc u1 aligned2, pc1]
    simp [BitVec.add_assoc]
  have aligned3 := live2.toActivation.aligned aligned
  let u3 := emit2State u2
  obtain ⟨regs3, memory3⟩ := emit2_observe s u2 words g live2 chain2 regs2
  have live3 : Live s u3 := live2.emitMemory g (emit2_scalar u2 aligned3)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit2_sp u2 aligned3) emit2Written memory3
  have chain3 := chain2.emitMemory g emit2Written memory3
  have done3 : DigestAt s u3 words ((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) := by
    intro i member
    rw [memory3]
    exact done2.emitMemory emit2Written g.outputBound i member
  have pc3 : read_pc u3 = base + finalizeOffset + 312#64 := by
    rw [emit2_pc u2 aligned3, pc2]
    simp [BitVec.add_assoc]
  have aligned4 := live3.toActivation.aligned aligned
  let u4 := emit3State u3
  obtain ⟨regs4, memory4⟩ := emit3_observe s u3 words g live3 chain3 regs3
  have live4 : Live s u4 := live3.emitMemory g (emit3_scalar u3 aligned4)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit3_sp u3 aligned4) emit3Written memory4
  have chain4 := chain3.emitMemory g emit3Written memory4
  have done4 : DigestAt s u4 words (((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) := by
    intro i member
    rw [memory4]
    exact done3.emitMemory emit3Written g.outputBound i member
  have pc4 : read_pc u4 = base + finalizeOffset + 344#64 := by
    rw [emit3_pc u3 aligned4, pc3]
    simp [BitVec.add_assoc]
  have aligned5 := live4.toActivation.aligned aligned
  let u5 := emit4State u4
  obtain ⟨regs5, memory5⟩ := emit4_observe s u4 words g live4 chain4 regs4
  have live5 : Live s u5 := live4.emitMemory g (emit4_scalar u4 aligned5)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit4_sp u4 aligned5) emit4Written memory5
  have chain5 := chain4.emitMemory g emit4Written memory5
  have done5 : DigestAt s u5 words ((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) := by
    intro i member
    rw [memory5]
    exact done4.emitMemory emit4Written g.outputBound i member
  have pc5 : read_pc u5 = base + finalizeOffset + 376#64 := by
    rw [emit4_pc u4 aligned5, pc4]
    simp [BitVec.add_assoc]
  have aligned6 := live5.toActivation.aligned aligned
  let u6 := emit5State u5
  obtain ⟨regs6, memory6⟩ := emit5_observe s u5 words g live5 chain5 regs5
  have live6 : Live s u6 := live5.emitMemory g (emit5_scalar u5 aligned6)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit5_sp u5 aligned6) emit5Written memory6
  have chain6 := chain5.emitMemory g emit5Written memory6
  have done6 : DigestAt s u6 words (((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) := by
    intro i member
    rw [memory6]
    exact done5.emitMemory emit5Written g.outputBound i member
  have pc6 : read_pc u6 = base + finalizeOffset + 408#64 := by
    rw [emit5_pc u5 aligned6, pc5]
    simp [BitVec.add_assoc]
  have aligned7 := live6.toActivation.aligned aligned
  let u7 := emit6State u6
  obtain ⟨regs7, memory7⟩ := emit6_observe s u6 words g live6 chain6 regs6
  have live7 : Live s u7 := live6.emitMemory g (emit6_scalar u6 aligned7)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit6_sp u6 aligned7) emit6Written memory7
  have chain7 := chain6.emitMemory g emit6Written memory7
  have done7 : DigestAt s u7 words ((((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) ++ emit6Written) := by
    intro i member
    rw [memory7]
    exact done6.emitMemory emit6Written g.outputBound i member
  have pc7 : read_pc u7 = base + finalizeOffset + 440#64 := by
    rw [emit6_pc u6 aligned7, pc6]
    simp [BitVec.add_assoc]
  have aligned8 := live7.toActivation.aligned aligned
  let u8 := emit7State u7
  obtain ⟨regs8, memory8⟩ := emit7_observe s u7 words g live7 chain7 regs7
  have live8 : Live s u8 := live7.emitMemory g (emit7_scalar u7 aligned8)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit7_sp u7 aligned8) emit7Written memory8
  have chain8 := chain7.emitMemory g emit7Written memory8
  have done8 : DigestAt s u8 words (((((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) ++ emit6Written) ++ emit7Written) := by
    intro i member
    rw [memory8]
    exact done7.emitMemory emit7Written g.outputBound i member
  have pc8 : read_pc u8 = base + finalizeOffset + 472#64 := by
    rw [emit7_pc u7 aligned8, pc7]
    simp [BitVec.add_assoc]
  have aligned9 := live8.toActivation.aligned aligned
  let u9 := emit8State u8
  obtain ⟨regs9, memory9⟩ := emit8_observe s u8 words g live8 chain8 regs8
  have live9 : Live s u9 := live8.emitMemory g (emit8_scalar u8 aligned9)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit8_sp u8 aligned9) emit8Written memory9
  have chain9 := chain8.emitMemory g emit8Written memory9
  have done9 : DigestAt s u9 words ((((((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) ++ emit6Written) ++ emit7Written) ++ emit8Written) := by
    intro i member
    rw [memory9]
    exact done8.emitMemory emit8Written g.outputBound i member
  have pc9 : read_pc u9 = base + finalizeOffset + 504#64 := by
    rw [emit8_pc u8 aligned9, pc8]
    simp [BitVec.add_assoc]
  have aligned10 := live9.toActivation.aligned aligned
  let u10 := emit9State u9
  obtain ⟨regs10, memory10⟩ := emit9_observe s u9 words g live9 chain9 regs9
  have live10 : Live s u10 := live9.emitMemory g (emit9_scalar u9 aligned10)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit9_sp u9 aligned10) emit9Written memory10
  have chain10 := chain9.emitMemory g emit9Written memory10
  have done10 : DigestAt s u10 words (((((((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) ++ emit6Written) ++ emit7Written) ++ emit8Written) ++ emit9Written) := by
    intro i member
    rw [memory10]
    exact done9.emitMemory emit9Written g.outputBound i member
  have pc10 : read_pc u10 = base + finalizeOffset + 536#64 := by
    rw [emit9_pc u9 aligned10, pc9]
    simp [BitVec.add_assoc]
  have aligned11 := live10.toActivation.aligned aligned
  let u11 := emit10State u10
  obtain ⟨regs11, memory11⟩ := emit10_observe s u10 words g live10 chain10 regs10
  have live11 : Live s u11 := live10.emitMemory g (emit10_scalar u10 aligned11)
    (by intro reg lo hi; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]; bv_omega)
    (emit10_sp u10 aligned11) emit10Written memory11
  have chain11 := chain10.emitMemory g emit10Written memory11
  have done11 : DigestAt s u11 words ((((((((((([] ++ emit0Written) ++ emit1Written) ++ emit2Written) ++ emit3Written) ++ emit4Written) ++ emit5Written) ++ emit6Written) ++ emit7Written) ++ emit8Written) ++ emit9Written) ++ emit10Written) := by
    intro i member
    rw [memory11]
    exact done10.emitMemory emit10Written g.outputBound i member
  have pc11 : read_pc u11 = base + finalizeOffset + 544#64 := by
    rw [emit10_pc u10 aligned11, pc10]
    simp [BitVec.add_assoc]
  refine ⟨u11, ?_, live11, ?_, pc11⟩
  · rw [show 82 = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (2)))))))))) by decide, run_plus,
      emit0_run t base (live.toActivation.code code) live.error aligned1 pc, run_plus,
      emit1_run u1 base (live1.toActivation.code code) live1.error aligned2 pc1, run_plus,
      emit2_run u2 base (live2.toActivation.code code) live2.error aligned3 pc2, run_plus,
      emit3_run u3 base (live3.toActivation.code code) live3.error aligned4 pc3, run_plus,
      emit4_run u4 base (live4.toActivation.code code) live4.error aligned5 pc4, run_plus,
      emit5_run u5 base (live5.toActivation.code code) live5.error aligned6 pc5, run_plus,
      emit6_run u6 base (live6.toActivation.code code) live6.error aligned7 pc6, run_plus,
      emit7_run u7 base (live7.toActivation.code code) live7.error aligned8 pc7, run_plus,
      emit8_run u8 base (live8.toActivation.code code) live8.error aligned9 pc8, run_plus,
      emit9_run u9 base (live9.toActivation.code code) live9.error aligned10 pc9,
      emit10_run u10 base (live10.toActivation.code code) live10.error aligned11 pc10]
  · have complete : DigestAt s u11 words digestWritten := by
      simpa only [digestWritten, emit0Written, emit1Written, emit2Written, emit3Written, emit4Written, emit5Written, emit6Written, emit7Written, emit8Written, emit9Written, emit10Written, List.append_nil,
        List.nil_append, List.cons_append] using done11
    intro i
    have bound : i.val < 32 := by simpa only [SszNative.HashStream.digest_size] using i.isLt
    exact (complete ⟨i.val, bound⟩ (digest_written_all _)).trans
      (digest_byte words ⟨i.val, bound⟩).symm

end SszArm.Hash.Finalize

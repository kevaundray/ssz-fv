import SszArm.BitVectorImpl

namespace SszArm.BitVector

private theorem program_ite (condition : Prop) [Decidable condition] (yes no : ArmState) :
    (if condition then yes else no).program =
      if condition then yes.program else no.program := by
  split <;> rfl

private theorem program_dite (condition : Prop) [Decidable condition]
    (yes : condition → ArmState) (no : ¬ condition → ArmState) :
    (if h : condition then yes h else no h).program =
      if h : condition then (yes h).program else (no h).program := by
  split <;> rfl

private theorem pair_program_ite {α : Type} (condition : Prop) [Decidable condition]
    (yes no : α × ArmState) :
    (if condition then yes else no).2.program =
      if condition then yes.2.program else no.2.program := by
  split <;> rfl

private theorem immediate_decode_program (inst : Advanced_simd_modified_immediate_cls)
    (s : ArmState) : (DPSFP.decode_immediate_op inst s).2.program = s.program := by
  simp only [DPSFP.decode_immediate_op, pair_program_ite, write_err, w_program, ite_self]

private theorem immediate_program (inst : Advanced_simd_modified_immediate_cls)
    (s : ArmState) : (DPSFP.exec_advanced_simd_modified_immediate inst s).program = s.program := by
  have preserved := immediate_decode_program inst s
  unfold DPSFP.exec_advanced_simd_modified_immediate
  cases decoded : DPSFP.decode_immediate_op inst s with
  | mk operation state =>
    have program : state.program = s.program := by simpa only [decoded] using preserved
    cases operation <;> simp only [write_sfp, write_pc, w_program, program]

/-- Instruction execution changes architectural fields or data memory, never
the separately modelled instruction map. Only this projection is simplified. -/
theorem exec_program (instruction : ArmInst) (s : ArmState) :
    (exec_inst instruction s).program = s.program := by
  cases instruction <;> rename_i operation <;> cases operation
  all_goals
    unfold exec_inst
    simp only [
      DPI.exec_add_sub_imm, DPI.exec_pc_rel_addressing, DPI.exec_logical_imm,
      DPI.exec_bitfield, DPI.exec_move_wide_imm,
      BR.exec_compare_branch, BR.exec_uncond_branch_imm, BR.exec_uncond_branch_reg,
      BR.exec_cond_branch_imm, BR.exec_hints,
      DPR.exec_add_sub_carry, DPR.exec_add_sub_shifted_reg, DPR.exec_conditional_select,
      DPR.exec_data_processing_one_source, DPR.exec_data_processing_rev,
      DPR.exec_data_processing_two_source, DPR.exec_data_processing_shift,
      DPR.exec_logical_shifted_reg, DPR.exec_data_processing_three_source,
      DPR.exec_data_processing_madd,
      DPSFP.exec_advanced_simd_copy, DPSFP.exec_dup_element, DPSFP.exec_dup_general,
      DPSFP.exec_ins_element, DPSFP.exec_ins_general, DPSFP.exec_smov_umov,
      DPSFP.exec_crypto_aes, DPSFP.exec_aese, DPSFP.exec_aesmc,
      DPSFP.exec_crypto_two_reg_sha512, DPSFP.exec_crypto_three_reg_sha512,
      DPSFP.exec_crypto_four_reg, DPSFP.exec_advanced_simd_two_reg_misc,
      DPSFP.exec_advanced_simd_extract, DPSFP.exec_advanced_simd_permute, DPSFP.exec_trn,
      immediate_program,
      DPSFP.exec_advanced_simd_shift_by_immediate, DPSFP.exec_shift_right_vector,
      DPSFP.exec_shl_vector, DPSFP.exec_advanced_simd_scalar_shift_by_immediate,
      DPSFP.exec_shift_right_scalar, DPSFP.exec_shl_scalar,
      DPSFP.exec_advanced_simd_scalar_copy, DPSFP.exec_advanced_simd_table_lookup,
      DPSFP.exec_tblx, DPSFP.exec_advanced_simd_three_same, DPSFP.exec_binary_vector,
      DPSFP.exec_logic_vector, DPSFP.exec_advanced_simd_three_different, DPSFP.exec_pmull,
      DPSFP.exec_conversion_between_FP_and_Int, DPSFP.exec_fmov_general,
      DPSFP.fmov_general_aux, Vpart_write,
      LDST.exec_reg_imm_post_indexed, LDST.exec_reg_imm_unsigned_offset,
      LDST.exec_reg_imm_common, LDST.reg_imm_operation,
      LDST.exec_reg_unscaled_imm, LDST.exec_ldstur,
      LDST.exec_reg_pair_pre_indexed, LDST.exec_reg_pair_post_indexed,
      LDST.exec_reg_pair_signed_offset, LDST.exec_reg_pair_common, LDST.reg_pair_operation,
      LDST.exec_advanced_simd_multiple_struct, LDST.exec_advanced_simd_multiple_struct_post_indexed,
      LDST.ld1_st1_operation, ldst_write,
      write_gpr, write_gpr_zr, write_sfp, write_pc, write_pstate, write_flag, write_err,
      w_program, write_mem_bytes_program, program_ite, program_dite, ite_self, dite_eq_ite]
    repeat' first
      | split <;> try simp only [w_program, write_mem_bytes_program, program_ite,
          program_dite, ite_self, dite_eq_ite, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
      | rfl

/-- Fetch/decode failures also leave instruction memory unchanged. -/
theorem step_program (s : ArmState) : (stepi s).program = s.program := by
  unfold stepi
  cases error : read_err s <;> simp only [error]
  all_goals first
    | rfl
    | (cases fetched : fetch_inst (read_pc s) s <;> simp only [fetched]
       · simp only [state_simp_rules]
       · rename_i word
         cases decoded : decode_raw_inst word <;> simp only [decoded]
         · simp only [state_simp_rules]
         · exact exec_program _ _)

/-- Enables structural JointCodeAt transport across opaque, proved Nat calls. -/
theorem run_program (fuel : Nat) (s : ArmState) : (run fuel s).program = s.program := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel induction =>
    exact (induction (stepi s)).trans (step_program s)

end SszArm.BitVector

import SszArm.CodecLinkedBase

namespace SszArm.Indices.Linked.Branches

/-- CeilShift + 272: b 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>. -/
theorem ceil_shift_p272 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2264260#64)
    (fetched : s.program.find? (bias + 2264260#64) = some 0x1400017c#32) :
    stepi s = w .PC (bias + 2265780#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkCount + 852: b 0x228bb4 <_ZN13ssz_fv_native7indices10ceil_shift17hfe7605b69b9bc83bE>. -/
theorem chunk_count_p852 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2262120#64)
    (fetched : s.program.find? (bias + 2262120#64) = some 0x140001d3#32) :
    stepi s = w .PC (bias + 2263988#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkCount + 880: bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>. -/
theorem chunk_count_p880 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2262148#64)
    (fetched : s.program.find? (bias + 2262148#64) = some 0x97fff0fe#32) :
    stepi s = w (.GPR 30#5) (bias + 2262152#64)
      (w .PC (bias + 2246780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkCount + 908: bl 0x24d4d0 <memcpy>. -/
theorem chunk_count_p908 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2262176#64)
    (fetched : s.program.find? (bias + 2262176#64) = some 0x9400940c#32) :
    stepi s = w (.GPR 30#5) (bias + 2262180#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 44: bl 0x227d40 <_ZN13ssz_fv_native7indices12element_type17hc2546e08b1adae5eE>. -/
theorem chunk_position_p44 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2258160#64)
    (fetched : s.program.find? (bias + 2258160#64) = some 0x94000214#32) :
    stepi s = w (.GPR 30#5) (bias + 2258164#64)
      (w .PC (bias + 2260288#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 644: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem chunk_position_p644 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2258760#64)
    (fetched : s.program.find? (bias + 2258760#64) = some 0x97fff799#32) :
    stepi s = w (.GPR 30#5) (bias + 2258764#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 812: bl 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>. -/
theorem chunk_position_p812 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2258928#64)
    (fetched : s.program.find? (bias + 2258928#64) = some 0x940006b1#32) :
    stepi s = w (.GPR 30#5) (bias + 2258932#64)
      (w .PC (bias + 2265780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 836: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p836 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2258952#64)
    (fetched : s.program.find? (bias + 2258952#64) = some 0x94009732#32) :
    stepi s = w (.GPR 30#5) (bias + 2258956#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 856: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p856 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2258972#64)
    (fetched : s.program.find? (bias + 2258972#64) = some 0x9400972d#32) :
    stepi s = w (.GPR 30#5) (bias + 2258976#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1424: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p1424 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259540#64)
    (fetched : s.program.find? (bias + 2259540#64) = some 0x9400969f#32) :
    stepi s = w (.GPR 30#5) (bias + 2259544#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1708: bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>. -/
theorem chunk_position_p1708 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259824#64)
    (fetched : s.program.find? (bias + 2259824#64) = some 0x97fff343#32) :
    stepi s = w (.GPR 30#5) (bias + 2259828#64)
      (w .PC (bias + 2246780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1736: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p1736 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259852#64)
    (fetched : s.program.find? (bias + 2259852#64) = some 0x94009651#32) :
    stepi s = w (.GPR 30#5) (bias + 2259856#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1780: bl 0x220c98 <_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE>. -/
theorem chunk_position_p1780 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259896#64)
    (fetched : s.program.find? (bias + 2259896#64) = some 0x97ffe438#32) :
    stepi s = w (.GPR 30#5) (bias + 2259900#64)
      (w .PC (bias + 2231448#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1816: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p1816 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259932#64)
    (fetched : s.program.find? (bias + 2259932#64) = some 0x9400963d#32) :
    stepi s = w (.GPR 30#5) (bias + 2259936#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1872: bl 0x2292b4 <_ZN13ssz_fv_native3nat3Nat3shr17he988a53a952ee485E>. -/
theorem chunk_position_p1872 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2259988#64)
    (fetched : s.program.find? (bias + 2259988#64) = some 0x940005a8#32) :
    stepi s = w (.GPR 30#5) (bias + 2259992#64)
      (w .PC (bias + 2265780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1896: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p1896 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2260012#64)
    (fetched : s.program.find? (bias + 2260012#64) = some 0x94009629#32) :
    stepi s = w (.GPR 30#5) (bias + 2260016#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 1916: bl 0x24d4d0 <memcpy>. -/
theorem chunk_position_p1916 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2260032#64)
    (fetched : s.program.find? (bias + 2260032#64) = some 0x94009624#32) :
    stepi s = w (.GPR 30#5) (bias + 2260036#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ChunkPosition + 2092: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem chunk_position_p2092 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2260208#64)
    (fetched : s.program.find? (bias + 2260208#64) = some 0x97ffeecf#32) :
    stepi s = w (.GPR 30#5) (bias + 2260212#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ElementType + 320: bl 0x24d4d0 <memcpy>. -/
theorem element_type_p320 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2260608#64)
    (fetched : s.program.find? (bias + 2260608#64) = some 0x94009594#32) :
    stepi s = w (.GPR 30#5) (bias + 2260612#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ElementType + 748: bl 0x24d4d0 <memcpy>. -/
theorem element_type_p748 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2261036#64)
    (fetched : s.program.find? (bias + 2261036#64) = some 0x94009529#32) :
    stepi s = w (.GPR 30#5) (bias + 2261040#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- GeneralizedIndex + 52: bl 0x22656c <_ZN13ssz_fv_native7indices12resolve_step17hc445f88b4eb19d18E>. -/
theorem generalized_index_p52 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2411056#64)
    (fetched : s.program.find? (bias + 2411056#64) = some 0x97ff66cf#32) :
    stepi s = w (.GPR 30#5) (bias + 2411060#64)
      (w .PC (bias + 2254188#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- GeneralizedIndex + 516: bl 0x24c9fc <_ZN13ssz_fv_native7indices17generalized_index17h7859d2dc0e7dcce2E>. -/
theorem generalized_index_p516 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2411520#64)
    (fetched : s.program.find? (bias + 2411520#64) = some 0x97ffff7f#32) :
    stepi s = w (.GPR 30#5) (bias + 2411524#64)
      (w .PC (bias + 2411004#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- GeneralizedIndex + 544: bl 0x24d4d0 <memcpy>. -/
theorem generalized_index_p544 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2411548#64)
    (fetched : s.program.find? (bias + 2411548#64) = some 0x9400022d#32) :
    stepi s = w (.GPR 30#5) (bias + 2411552#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 728: bl 0x2466e0 <_ZN13ssz_fv_native7indices18reject_claim_paths17hef042388294333e5E>. -/
theorem helper_indices_p728 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2369340#64)
    (fetched : s.program.find? (bias + 2369340#64) = some 0x94000fe9#32) :
    stepi s = w (.GPR 30#5) (bias + 2369344#64)
      (w .PC (bias + 2385632#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 1028: bl 0x24d4d0 <memcpy>. -/
theorem helper_indices_p1028 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2369640#64)
    (fetched : s.program.find? (bias + 2369640#64) = some 0x94002b1a#32) :
    stepi s = w (.GPR 30#5) (bias + 2369644#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 1920: bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>. -/
theorem helper_indices_p1920 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2370532#64)
    (fetched : s.program.find? (bias + 2370532#64) = some 0x940001e4#32) :
    stepi s = w (.GPR 30#5) (bias + 2370536#64)
      (w .PC (bias + 2372468#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 2008: bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>. -/
theorem helper_indices_p2008 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2370620#64)
    (fetched : s.program.find? (bias + 2370620#64) = some 0x940001ce#32) :
    stepi s = w (.GPR 30#5) (bias + 2370624#64)
      (w .PC (bias + 2372468#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 2908: bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>. -/
theorem helper_indices_p2908 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2371520#64)
    (fetched : s.program.find? (bias + 2371520#64) = some 0x940000ed#32) :
    stepi s = w (.GPR 30#5) (bias + 2371524#64)
      (w .PC (bias + 2372468#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3004: bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>. -/
theorem helper_indices_p3004 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2371616#64)
    (fetched : s.program.find? (bias + 2371616#64) = some 0x940000d5#32) :
    stepi s = w (.GPR 30#5) (bias + 2371620#64)
      (w .PC (bias + 2372468#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3344: bl 0x241978 <_ZN13ssz_fv_native7indices9shift_xor17h45a956e38b065bb1E>. -/
theorem helper_indices_p3344 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2371956#64)
    (fetched : s.program.find? (bias + 2371956#64) = some 0x97fffa01#32) :
    stepi s = w (.GPR 30#5) (bias + 2371960#64)
      (w .PC (bias + 2365816#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3424: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem helper_indices_p3424 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372036#64)
    (fetched : s.program.find? (bias + 2372036#64) = some 0x97ff6bdf#32) :
    stepi s = w (.GPR 30#5) (bias + 2372040#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3468: bl 0x24d4d0 <memcpy>. -/
theorem helper_indices_p3468 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372080#64)
    (fetched : s.program.find? (bias + 2372080#64) = some 0x940028b8#32) :
    stepi s = w (.GPR 30#5) (bias + 2372084#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3556: bl 0x24d4d0 <memcpy>. -/
theorem helper_indices_p3556 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372168#64)
    (fetched : s.program.find? (bias + 2372168#64) = some 0x940028a2#32) :
    stepi s = w (.GPR 30#5) (bias + 2372172#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3804: bl 0x243b48 <_ZN4core5slice4sort6shared9smallsort25insertion_sort_shift_left17hedcf71437a340f54E>. -/
theorem helper_indices_p3804 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372416#64)
    (fetched : s.program.find? (bias + 2372416#64) = some 0x94000202#32) :
    stepi s = w (.GPR 30#5) (bias + 2372420#64)
      (w .PC (bias + 2374472#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3820: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem helper_indices_p3820 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372432#64)
    (fetched : s.program.find? (bias + 2372432#64) = some 0x97ff6b88#32) :
    stepi s = w (.GPR 30#5) (bias + 2372436#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3828: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem helper_indices_p3828 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372440#64)
    (fetched : s.program.find? (bias + 2372440#64) = some 0x97ff6b86#32) :
    stepi s = w (.GPR 30#5) (bias + 2372444#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- HelperIndices + 3848: bl 0x243990 <_ZN4core5slice4sort8unstable7ipnsort17h2a30cf48fed7d7bfE>. -/
theorem helper_indices_p3848 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2372460#64)
    (fetched : s.program.find? (bias + 2372460#64) = some 0x94000189#32) :
    stepi s = w (.GPR 30#5) (bias + 2372464#64)
      (w .PC (bias + 2374032#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- RejectClaimPaths + 600: bl 0x243374 <_ZN13ssz_fv_native7indices12prefix_equal17h455af9025a76ffe0E>. -/
theorem reject_claim_paths_p600 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2386232#64)
    (fetched : s.program.find? (bias + 2386232#64) = some 0x97fff28f#32) :
    stepi s = w (.GPR 30#5) (bias + 2386236#64)
      (w .PC (bias + 2372468#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 620: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem resolve_step_p620 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2254808#64)
    (fetched : s.program.find? (bias + 2254808#64) = some 0x97fffb75#32) :
    stepi s = w (.GPR 30#5) (bias + 2254812#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 652: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p652 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2254840#64)
    (fetched : s.program.find? (bias + 2254840#64) = some 0x94009b36#32) :
    stepi s = w (.GPR 30#5) (bias + 2254844#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 764: bl 0x2274c4 <_ZN13ssz_fv_native7indices14chunk_position17he9da7fe78b73f603E>. -/
theorem resolve_step_p764 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2254952#64)
    (fetched : s.program.find? (bias + 2254952#64) = some 0x94000317#32) :
    stepi s = w (.GPR 30#5) (bias + 2254956#64)
      (w .PC (bias + 2258116#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 792: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p792 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2254980#64)
    (fetched : s.program.find? (bias + 2254980#64) = some 0x94009b13#32) :
    stepi s = w (.GPR 30#5) (bias + 2254984#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 816: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p816 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255004#64)
    (fetched : s.program.find? (bias + 2255004#64) = some 0x94009b0d#32) :
    stepi s = w (.GPR 30#5) (bias + 2255008#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 952: bl 0x2274c4 <_ZN13ssz_fv_native7indices14chunk_position17he9da7fe78b73f603E>. -/
theorem resolve_step_p952 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255140#64)
    (fetched : s.program.find? (bias + 2255140#64) = some 0x940002e8#32) :
    stepi s = w (.GPR 30#5) (bias + 2255144#64)
      (w .PC (bias + 2258116#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 980: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p980 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255168#64)
    (fetched : s.program.find? (bias + 2255168#64) = some 0x94009ae4#32) :
    stepi s = w (.GPR 30#5) (bias + 2255172#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 1004: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p1004 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255192#64)
    (fetched : s.program.find? (bias + 2255192#64) = some 0x94009ade#32) :
    stepi s = w (.GPR 30#5) (bias + 2255196#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 1384: bl 0x228114 <_ZN13ssz_fv_native7indices11chunk_count17hd16e3dc1986da804E>. -/
theorem resolve_step_p1384 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255572#64)
    (fetched : s.program.find? (bias + 2255572#64) = some 0x94000590#32) :
    stepi s = w (.GPR 30#5) (bias + 2255576#64)
      (w .PC (bias + 2261268#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 1412: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p1412 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2255600#64)
    (fetched : s.program.find? (bias + 2255600#64) = some 0x94009a78#32) :
    stepi s = w (.GPR 30#5) (bias + 2255604#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2028: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p2028 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256216#64)
    (fetched : s.program.find? (bias + 2256216#64) = some 0x940099de#32) :
    stepi s = w (.GPR 30#5) (bias + 2256220#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2368: bl 0x227d40 <_ZN13ssz_fv_native7indices12element_type17hc2546e08b1adae5eE>. -/
theorem resolve_step_p2368 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256556#64)
    (fetched : s.program.find? (bias + 2256556#64) = some 0x940003a5#32) :
    stepi s = w (.GPR 30#5) (bias + 2256560#64)
      (w .PC (bias + 2260288#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2392: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p2392 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256580#64)
    (fetched : s.program.find? (bias + 2256580#64) = some 0x94009983#32) :
    stepi s = w (.GPR 30#5) (bias + 2256584#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2412: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p2412 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256600#64)
    (fetched : s.program.find? (bias + 2256600#64) = some 0x9400997e#32) :
    stepi s = w (.GPR 30#5) (bias + 2256604#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2576: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p2576 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256764#64)
    (fetched : s.program.find? (bias + 2256764#64) = some 0x94009955#32) :
    stepi s = w (.GPR 30#5) (bias + 2256768#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2592: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p2592 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256780#64)
    (fetched : s.program.find? (bias + 2256780#64) = some 0x94009951#32) :
    stepi s = w (.GPR 30#5) (bias + 2256784#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2660: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem resolve_step_p2660 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2256848#64)
    (fetched : s.program.find? (bias + 2256848#64) = some 0x97fff977#32) :
    stepi s = w (.GPR 30#5) (bias + 2256852#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 2896: bl 0x2284d8 <_ZN13ssz_fv_native3nat3Nat15is_power_of_two17hc06f51fda78fd5d7E>. -/
theorem resolve_step_p2896 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257084#64)
    (fetched : s.program.find? (bias + 2257084#64) = some 0x94000507#32) :
    stepi s = w (.GPR 30#5) (bias + 2257088#64)
      (w .PC (bias + 2262232#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3032: bl 0x2285d0 <_ZN13ssz_fv_native7indices6rebase17h0203817c13357eb1E>. -/
theorem resolve_step_p3032 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257220#64)
    (fetched : s.program.find? (bias + 2257220#64) = some 0x94000523#32) :
    stepi s = w (.GPR 30#5) (bias + 2257224#64)
      (w .PC (bias + 2262480#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3056: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p3056 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257244#64)
    (fetched : s.program.find? (bias + 2257244#64) = some 0x940098dd#32) :
    stepi s = w (.GPR 30#5) (bias + 2257248#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3076: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p3076 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257264#64)
    (fetched : s.program.find? (bias + 2257264#64) = some 0x940098d8#32) :
    stepi s = w (.GPR 30#5) (bias + 2257268#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3108: bl 0x227d40 <_ZN13ssz_fv_native7indices12element_type17hc2546e08b1adae5eE>. -/
theorem resolve_step_p3108 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257296#64)
    (fetched : s.program.find? (bias + 2257296#64) = some 0x940002ec#32) :
    stepi s = w (.GPR 30#5) (bias + 2257300#64)
      (w .PC (bias + 2260288#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3132: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p3132 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257320#64)
    (fetched : s.program.find? (bias + 2257320#64) = some 0x940098ca#32) :
    stepi s = w (.GPR 30#5) (bias + 2257324#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3152: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p3152 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257340#64)
    (fetched : s.program.find? (bias + 2257340#64) = some 0x940098c5#32) :
    stepi s = w (.GPR 30#5) (bias + 2257344#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ResolveStep + 3176: bl 0x24d4d0 <memcpy>. -/
theorem resolve_step_p3176 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2257364#64)
    (fetched : s.program.find? (bias + 2257364#64) = some 0x940098bf#32) :
    stepi s = w (.GPR 30#5) (bias + 2257368#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

end SszArm.Indices.Linked.Branches

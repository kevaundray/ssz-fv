import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked.Branches

/-- Serialize + 48: bl 0x22f2fc <_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E>. -/
theorem serialize_p48 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328584#64)
    (fetched : s.program.find? (bias + 2328584#64) = some 0x97ffdabd#32) :
    stepi s = w (.GPR 30#5) (bias + 2328588#64)
      (w .PC (bias + 2290428#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Serialize + 668: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem serialize_p668 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2329204#64)
    (fetched : s.program.find? (bias + 2329204#64) = some 0x97ffde62#32) :
    stepi s = w (.GPR 30#5) (bias + 2329208#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 160: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem measure_p160 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2290588#64)
    (fetched : s.program.find? (bias + 2290588#64) = some 0x97ffd884#32) :
    stepi s = w (.GPR 30#5) (bias + 2290592#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 1052: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem measure_p1052 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2291480#64)
    (fetched : s.program.find? (bias + 2291480#64) = some 0x97ffd7a5#32) :
    stepi s = w (.GPR 30#5) (bias + 2291484#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 1092: bl 0x22f2fc <_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E>. -/
theorem measure_p1092 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2291520#64)
    (fetched : s.program.find? (bias + 2291520#64) = some 0x97fffeef#32) :
    stepi s = w (.GPR 30#5) (bias + 2291524#64)
      (w .PC (bias + 2290428#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 1728: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem measure_p1728 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2292156#64)
    (fetched : s.program.find? (bias + 2292156#64) = some 0x97ffd6fc#32) :
    stepi s = w (.GPR 30#5) (bias + 2292160#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 1912: bl 0x22b578 <_ZN13ssz_fv_native3nat3Nat9from_u12817h73292f97725c3b7dE>. -/
theorem measure_p1912 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2292340#64)
    (fetched : s.program.find? (bias + 2292340#64) = some 0x97ffeec1#32) :
    stepi s = w (.GPR 30#5) (bias + 2292344#64)
      (w .PC (bias + 2274680#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 1940: bl 0x24d4d0 <memcpy>. -/
theorem measure_p1940 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2292368#64)
    (fetched : s.program.find? (bias + 2292368#64) = some 0x94007690#32) :
    stepi s = w (.GPR 30#5) (bias + 2292372#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 2928: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_p2928 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2293356#64)
    (fetched : s.program.find? (bias + 2293356#64) = some 0x97ffce70#32) :
    stepi s = w (.GPR 30#5) (bias + 2293360#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 2952: bl 0x24d4d0 <memcpy>. -/
theorem measure_p2952 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2293380#64)
    (fetched : s.program.find? (bias + 2293380#64) = some 0x94007593#32) :
    stepi s = w (.GPR 30#5) (bias + 2293384#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 2972: bl 0x24d4d0 <memcpy>. -/
theorem measure_p2972 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2293400#64)
    (fetched : s.program.find? (bias + 2293400#64) = some 0x9400758e#32) :
    stepi s = w (.GPR 30#5) (bias + 2293404#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 3108: bl 0x23113c <_ZN13ssz_fv_native5codec13measure_parts17h3804244188cbc0c8E>. -/
theorem measure_p3108 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2293536#64)
    (fetched : s.program.find? (bias + 2293536#64) = some 0x94000487#32) :
    stepi s = w (.GPR 30#5) (bias + 2293540#64)
      (w .PC (bias + 2298172#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Measure + 4308: bl 0x2317e0 <_ZN13ssz_fv_native5arena5Arena10slice_with17h0d5d48f70484df3cE>. -/
theorem measure_p4308 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2294736#64)
    (fetched : s.program.find? (bias + 2294736#64) = some 0x94000504#32) :
    stepi s = w (.GPR 30#5) (bias + 2294740#64)
      (w .PC (bias + 2299872#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 648: bl 0x24d4d0 <memcpy>. -/
theorem emit_p648 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2295428#64)
    (fetched : s.program.find? (bias + 2295428#64) = some 0x94007393#32) :
    stepi s = w (.GPR 30#5) (bias + 2295432#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 856: bl 0x24d4d0 <memcpy>. -/
theorem emit_p856 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2295636#64)
    (fetched : s.program.find? (bias + 2295636#64) = some 0x9400735f#32) :
    stepi s = w (.GPR 30#5) (bias + 2295640#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1252: bl 0x24d4d0 <memcpy>. -/
theorem emit_p1252 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296032#64)
    (fetched : s.program.find? (bias + 2296032#64) = some 0x940072fc#32) :
    stepi s = w (.GPR 30#5) (bias + 2296036#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1572: bl 0x230bc8 <_ZN13ssz_fv_native5codec10emit_parts17h64cc0a69cd66c152E>. -/
theorem emit_p1572 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296352#64)
    (fetched : s.program.find? (bias + 2296352#64) = some 0x9400006a#32) :
    stepi s = w (.GPR 30#5) (bias + 2296356#64)
      (w .PC (bias + 2296776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1652: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem emit_p1652 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296432#64)
    (fetched : s.program.find? (bias + 2296432#64) = some 0x97ffd2cf#32) :
    stepi s = w (.GPR 30#5) (bias + 2296436#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1700: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem emit_p1700 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296480#64)
    (fetched : s.program.find? (bias + 2296480#64) = some 0x97fffe57#32) :
    stepi s = w (.GPR 30#5) (bias + 2296484#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1728: bl 0x24d4d0 <memcpy>. -/
theorem emit_p1728 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296508#64)
    (fetched : s.program.find? (bias + 2296508#64) = some 0x94007285#32) :
    stepi s = w (.GPR 30#5) (bias + 2296512#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1924: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_p1924 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296704#64)
    (fetched : s.program.find? (bias + 2296704#64) = some 0x97ffb570#32) :
    stepi s = w (.GPR 30#5) (bias + 2296708#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1940: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_p1940 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296720#64)
    (fetched : s.program.find? (bias + 2296720#64) = some 0x97ffb56c#32) :
    stepi s = w (.GPR 30#5) (bias + 2296724#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1956: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_p1956 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296736#64)
    (fetched : s.program.find? (bias + 2296736#64) = some 0x97ffb568#32) :
    stepi s = w (.GPR 30#5) (bias + 2296740#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1968: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem emit_p1968 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296748#64)
    (fetched : s.program.find? (bias + 2296748#64) = some 0x97ffb571#32) :
    stepi s = w (.GPR 30#5) (bias + 2296752#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1980: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem emit_p1980 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296760#64)
    (fetched : s.program.find? (bias + 2296760#64) = some 0x97ffb56e#32) :
    stepi s = w (.GPR 30#5) (bias + 2296764#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Emit + 1992: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem emit_p1992 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2296772#64)
    (fetched : s.program.find? (bias + 2296772#64) = some 0x97ffb56b#32) :
    stepi s = w (.GPR 30#5) (bias + 2296776#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 124: b 0x237710 <_ZN13ssz_fv_native5codec11decode_list17h1123a2f8d52877c5E>. -/
theorem deserialize_p124 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2309660#64)
    (fetched : s.program.find? (bias + 2309660#64) = some 0x14000e3d#32) :
    stepi s = w .PC (bias + 2324240#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- Deserialize + 292: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem deserialize_p292 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2309828#64)
    (fetched : s.program.find? (bias + 2309828#64) = some 0x97fff46b#32) :
    stepi s = w (.GPR 30#5) (bias + 2309832#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 352: bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>. -/
theorem deserialize_p352 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2309888#64)
    (fetched : s.program.find? (bias + 2309888#64) = some 0x94000af5#32) :
    stepi s = w (.GPR 30#5) (bias + 2309892#64)
      (w .PC (bias + 2321108#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 384: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p384 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2309920#64)
    (fetched : s.program.find? (bias + 2309920#64) = some 0x9400656c#32) :
    stepi s = w (.GPR 30#5) (bias + 2309924#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 468: bl 0x220c98 <_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE>. -/
theorem deserialize_p468 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2310004#64)
    (fetched : s.program.find? (bias + 2310004#64) = some 0x97ffb349#32) :
    stepi s = w (.GPR 30#5) (bias + 2310008#64)
      (w .PC (bias + 2231448#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 504: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p504 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2310040#64)
    (fetched : s.program.find? (bias + 2310040#64) = some 0x9400654e#32) :
    stepi s = w (.GPR 30#5) (bias + 2310044#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 600: b 0x2366e0 <_ZN13ssz_fv_native5codec16decode_delimited17h0ab2ea8991fd33aeE>. -/
theorem deserialize_p600 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2310136#64)
    (fetched : s.program.find? (bias + 2310136#64) = some 0x140009ba#32) :
    stepi s = w .PC (bias + 2320096#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- Deserialize + 840: bl 0x237710 <_ZN13ssz_fv_native5codec11decode_list17h1123a2f8d52877c5E>. -/
theorem deserialize_p840 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2310376#64)
    (fetched : s.program.find? (bias + 2310376#64) = some 0x94000d8a#32) :
    stepi s = w (.GPR 30#5) (bias + 2310380#64)
      (w .PC (bias + 2324240#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 1636: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem deserialize_p1636 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2311172#64)
    (fetched : s.program.find? (bias + 2311172#64) = some 0x97fff31b#32) :
    stepi s = w (.GPR 30#5) (bias + 2311176#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 1692: bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>. -/
theorem deserialize_p1692 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2311228#64)
    (fetched : s.program.find? (bias + 2311228#64) = some 0x940009a6#32) :
    stepi s = w (.GPR 30#5) (bias + 2311232#64)
      (w .PC (bias + 2321108#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 1820: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem deserialize_p1820 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2311356#64)
    (fetched : s.program.find? (bias + 2311356#64) = some 0x97ffbcdc#32) :
    stepi s = w (.GPR 30#5) (bias + 2311360#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 2076: bl 0x2366e0 <_ZN13ssz_fv_native5codec16decode_delimited17h0ab2ea8991fd33aeE>. -/
theorem deserialize_p2076 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2311612#64)
    (fetched : s.program.find? (bias + 2311612#64) = some 0x94000849#32) :
    stepi s = w (.GPR 30#5) (bias + 2311616#64)
      (w .PC (bias + 2320096#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 3412: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem deserialize_p3412 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2312948#64)
    (fetched : s.program.find? (bias + 2312948#64) = some 0x97ffbb4e#32) :
    stepi s = w (.GPR 30#5) (bias + 2312952#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 3436: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p3436 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2312972#64)
    (fetched : s.program.find? (bias + 2312972#64) = some 0x94006271#32) :
    stepi s = w (.GPR 30#5) (bias + 2312976#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 3456: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p3456 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2312992#64)
    (fetched : s.program.find? (bias + 2312992#64) = some 0x9400626c#32) :
    stepi s = w (.GPR 30#5) (bias + 2312996#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4008: bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>. -/
theorem deserialize_p4008 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2313544#64)
    (fetched : s.program.find? (bias + 2313544#64) = some 0x97fffc16#32) :
    stepi s = w (.GPR 30#5) (bias + 2313548#64)
      (w .PC (bias + 2309536#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4036: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p4036 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2313572#64)
    (fetched : s.program.find? (bias + 2313572#64) = some 0x940061db#32) :
    stepi s = w (.GPR 30#5) (bias + 2313576#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4052: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p4052 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2313588#64)
    (fetched : s.program.find? (bias + 2313588#64) = some 0x940061d7#32) :
    stepi s = w (.GPR 30#5) (bias + 2313592#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4908: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p4908 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314444#64)
    (fetched : s.program.find? (bias + 2314444#64) = some 0x94006101#32) :
    stepi s = w (.GPR 30#5) (bias + 2314448#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4944: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p4944 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314480#64)
    (fetched : s.program.find? (bias + 2314480#64) = some 0x940060f8#32) :
    stepi s = w (.GPR 30#5) (bias + 2314484#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 4960: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p4960 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314496#64)
    (fetched : s.program.find? (bias + 2314496#64) = some 0x940060f4#32) :
    stepi s = w (.GPR 30#5) (bias + 2314500#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5220: bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>. -/
theorem deserialize_p5220 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314756#64)
    (fetched : s.program.find? (bias + 2314756#64) = some 0x97ffbd9e#32) :
    stepi s = w (.GPR 30#5) (bias + 2314760#64)
      (w .PC (bias + 2246780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5256: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p5256 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314792#64)
    (fetched : s.program.find? (bias + 2314792#64) = some 0x940060aa#32) :
    stepi s = w (.GPR 30#5) (bias + 2314796#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5368: bl 0x224e84 <_ZN13ssz_fv_native3nat3Nat8mul_word17h44eb4fbc8039a355E>. -/
theorem deserialize_p5368 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314904#64)
    (fetched : s.program.find? (bias + 2314904#64) = some 0x97ffbefb#32) :
    stepi s = w (.GPR 30#5) (bias + 2314908#64)
      (w .PC (bias + 2248324#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5396: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p5396 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2314932#64)
    (fetched : s.program.find? (bias + 2314932#64) = some 0x94006087#32) :
    stepi s = w (.GPR 30#5) (bias + 2314936#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5960: bl 0x2381b4 <_ZN13ssz_fv_native5codec5exact17hfce8663ef07a8e63E>. -/
theorem deserialize_p5960 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2315496#64)
    (fetched : s.program.find? (bias + 2315496#64) = some 0x94000b33#32) :
    stepi s = w (.GPR 30#5) (bias + 2315500#64)
      (w .PC (bias + 2326964#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 5984: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p5984 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2315520#64)
    (fetched : s.program.find? (bias + 2315520#64) = some 0x94005ff4#32) :
    stepi s = w (.GPR 30#5) (bias + 2315524#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 6272: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p6272 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2315808#64)
    (fetched : s.program.find? (bias + 2315808#64) = some 0x94005fac#32) :
    stepi s = w (.GPR 30#5) (bias + 2315812#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 6588: bl 0x2382dc <_ZN13ssz_fv_native3nat3Nat7to_u12817h7b219376ab6746a8E>. -/
theorem deserialize_p6588 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2316124#64)
    (fetched : s.program.find? (bias + 2316124#64) = some 0x94000ae0#32) :
    stepi s = w (.GPR 30#5) (bias + 2316128#64)
      (w .PC (bias + 2327260#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 7424: bl 0x2381b4 <_ZN13ssz_fv_native5codec5exact17hfce8663ef07a8e63E>. -/
theorem deserialize_p7424 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2316960#64)
    (fetched : s.program.find? (bias + 2316960#64) = some 0x940009c5#32) :
    stepi s = w (.GPR 30#5) (bias + 2316964#64)
      (w .PC (bias + 2326964#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 7448: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p7448 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2316984#64)
    (fetched : s.program.find? (bias + 2316984#64) = some 0x94005e86#32) :
    stepi s = w (.GPR 30#5) (bias + 2316988#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 7468: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p7468 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317004#64)
    (fetched : s.program.find? (bias + 2317004#64) = some 0x94005e81#32) :
    stepi s = w (.GPR 30#5) (bias + 2317008#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 7492: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p7492 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317028#64)
    (fetched : s.program.find? (bias + 2317028#64) = some 0x94005e7b#32) :
    stepi s = w (.GPR 30#5) (bias + 2317032#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 8048: bl 0x2370c0 <_ZN13ssz_fv_native5codec11read_offset17h14742c7c7578f3fcE>. -/
theorem deserialize_p8048 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317584#64)
    (fetched : s.program.find? (bias + 2317584#64) = some 0x940004ec#32) :
    stepi s = w (.GPR 30#5) (bias + 2317588#64)
      (w .PC (bias + 2322624#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 8068: bl 0x22b4cc <_ZN13ssz_fv_native3nat3Nat9cmp_usize17h857d9c8293a9444eE>. -/
theorem deserialize_p8068 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317604#64)
    (fetched : s.program.find? (bias + 2317604#64) = some 0x97ffd5ea#32) :
    stepi s = w (.GPR 30#5) (bias + 2317608#64)
      (w .PC (bias + 2274508#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 8292: b 0x23712c <_ZN13ssz_fv_native5codec14decode_offsets17h3986df5c439cd32dE>. -/
theorem deserialize_p8292 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317828#64)
    (fetched : s.program.find? (bias + 2317828#64) = some 0x140004ca#32) :
    stepi s = w .PC (bias + 2322732#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- Deserialize + 8408: bl 0x23845c <_ZN13ssz_fv_native5arena5Arena10slice_with17h0ed27805c5c943ffE>. -/
theorem deserialize_p8408 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317944#64)
    (fetched : s.program.find? (bias + 2317944#64) = some 0x94000979#32) :
    stepi s = w (.GPR 30#5) (bias + 2317948#64)
      (w .PC (bias + 2327644#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 8436: bl 0x24d4d0 <memcpy>. -/
theorem deserialize_p8436 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2317972#64)
    (fetched : s.program.find? (bias + 2317972#64) = some 0x94005d8f#32) :
    stepi s = w (.GPR 30#5) (bias + 2317976#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 9876: b 0x236e10 <_ZN13ssz_fv_native5codec12decode_fixed17hd268ce61b5ac9b5fE>. -/
theorem deserialize_p9876 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319412#64)
    (fetched : s.program.find? (bias + 2319412#64) = some 0x14000277#32) :
    stepi s = w .PC (bias + 2321936#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- Deserialize + 9888: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem deserialize_p9888 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319424#64)
    (fetched : s.program.find? (bias + 2319424#64) = some 0x97ff9f4c#32) :
    stepi s = w (.GPR 30#5) (bias + 2319428#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 9900: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem deserialize_p9900 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319436#64)
    (fetched : s.program.find? (bias + 2319436#64) = some 0x97ff9f49#32) :
    stepi s = w (.GPR 30#5) (bias + 2319440#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 9912: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem deserialize_p9912 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319448#64)
    (fetched : s.program.find? (bias + 2319448#64) = some 0x97ff9f46#32) :
    stepi s = w (.GPR 30#5) (bias + 2319452#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 9924: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem deserialize_p9924 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319460#64)
    (fetched : s.program.find? (bias + 2319460#64) = some 0x97ff9f43#32) :
    stepi s = w (.GPR 30#5) (bias + 2319464#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Deserialize + 9936: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem deserialize_p9936 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2319472#64)
    (fetched : s.program.find? (bias + 2319472#64) = some 0x97ff9f40#32) :
    stepi s = w (.GPR 30#5) (bias + 2319476#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 100: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem measure_parts_p100 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2298272#64)
    (fetched : s.program.find? (bias + 2298272#64) = some 0x97ffffb4#32) :
    stepi s = w (.GPR 30#5) (bias + 2298276#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 164: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem measure_parts_p164 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2298336#64)
    (fetched : s.program.find? (bias + 2298336#64) = some 0x97ffffa4#32) :
    stepi s = w (.GPR 30#5) (bias + 2298340#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 472: bl 0x231958 <_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E>. -/
theorem measure_parts_p472 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2298644#64)
    (fetched : s.program.find? (bias + 2298644#64) = some 0x94000191#32) :
    stepi s = w (.GPR 30#5) (bias + 2298648#64)
      (w .PC (bias + 2300248#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 592: bl 0x231958 <_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E>. -/
theorem measure_parts_p592 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2298764#64)
    (fetched : s.program.find? (bias + 2298764#64) = some 0x94000173#32) :
    stepi s = w (.GPR 30#5) (bias + 2298768#64)
      (w .PC (bias + 2300248#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 860: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_parts_p860 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299032#64)
    (fetched : s.program.find? (bias + 2299032#64) = some 0x97ffc8e5#32) :
    stepi s = w (.GPR 30#5) (bias + 2299036#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 888: bl 0x24d4d0 <memcpy>. -/
theorem measure_parts_p888 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299060#64)
    (fetched : s.program.find? (bias + 2299060#64) = some 0x94007007#32) :
    stepi s = w (.GPR 30#5) (bias + 2299064#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 1096: bl 0x24d4d0 <memcpy>. -/
theorem measure_parts_p1096 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299268#64)
    (fetched : s.program.find? (bias + 2299268#64) = some 0x94006fd3#32) :
    stepi s = w (.GPR 30#5) (bias + 2299272#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 1116: bl 0x24d4d0 <memcpy>. -/
theorem measure_parts_p1116 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299288#64)
    (fetched : s.program.find? (bias + 2299288#64) = some 0x94006fce#32) :
    stepi s = w (.GPR 30#5) (bias + 2299292#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureParts + 1136: bl 0x24d4d0 <memcpy>. -/
theorem measure_parts_p1136 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299308#64)
    (fetched : s.program.find? (bias + 2299308#64) = some 0x94006fc9#32) :
    stepi s = w (.GPR 30#5) (bias + 2299312#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 112: bl 0x22f2fc <_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E>. -/
theorem measure_child_p112 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300360#64)
    (fetched : s.program.find? (bias + 2300360#64) = some 0x97fff64d#32) :
    stepi s = w (.GPR 30#5) (bias + 2300364#64)
      (w .PC (bias + 2290428#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 204: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem measure_child_p204 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300452#64)
    (fetched : s.program.find? (bias + 2300452#64) = some 0x97fffd93#32) :
    stepi s = w (.GPR 30#5) (bias + 2300456#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 332: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_child_p332 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300580#64)
    (fetched : s.program.find? (bias + 2300580#64) = some 0x97ffc762#32) :
    stepi s = w (.GPR 30#5) (bias + 2300584#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 356: bl 0x24d4d0 <memcpy>. -/
theorem measure_child_p356 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300604#64)
    (fetched : s.program.find? (bias + 2300604#64) = some 0x94006e85#32) :
    stepi s = w (.GPR 30#5) (bias + 2300608#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 376: bl 0x24d4d0 <memcpy>. -/
theorem measure_child_p376 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300624#64)
    (fetched : s.program.find? (bias + 2300624#64) = some 0x94006e80#32) :
    stepi s = w (.GPR 30#5) (bias + 2300628#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 424: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_child_p424 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300672#64)
    (fetched : s.program.find? (bias + 2300672#64) = some 0x97ffc74b#32) :
    stepi s = w (.GPR 30#5) (bias + 2300676#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 448: bl 0x24d4d0 <memcpy>. -/
theorem measure_child_p448 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300696#64)
    (fetched : s.program.find? (bias + 2300696#64) = some 0x94006e6e#32) :
    stepi s = w (.GPR 30#5) (bias + 2300700#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 468: bl 0x24d4d0 <memcpy>. -/
theorem measure_child_p468 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300716#64)
    (fetched : s.program.find? (bias + 2300716#64) = some 0x94006e69#32) :
    stepi s = w (.GPR 30#5) (bias + 2300720#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 580: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem measure_child_p580 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300828#64)
    (fetched : s.program.find? (bias + 2300828#64) = some 0x97ffb175#32) :
    stepi s = w (.GPR 30#5) (bias + 2300832#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureChild + 592: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem measure_child_p592 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2300840#64)
    (fetched : s.program.find? (bias + 2300840#64) = some 0x97ffb172#32) :
    stepi s = w (.GPR 30#5) (bias + 2300844#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 284: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem emit_parts_p284 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297060#64)
    (fetched : s.program.find? (bias + 2297060#64) = some 0x940000e3#32) :
    stepi s = w (.GPR 30#5) (bias + 2297064#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 376: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem emit_parts_p376 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297152#64)
    (fetched : s.program.find? (bias + 2297152#64) = some 0x97fffdaf#32) :
    stepi s = w (.GPR 30#5) (bias + 2297156#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 496: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem emit_parts_p496 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297272#64)
    (fetched : s.program.find? (bias + 2297272#64) = some 0x97fffd91#32) :
    stepi s = w (.GPR 30#5) (bias + 2297276#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 592: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem emit_parts_p592 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297368#64)
    (fetched : s.program.find? (bias + 2297368#64) = some 0x97fffd79#32) :
    stepi s = w (.GPR 30#5) (bias + 2297372#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 684: bl 0x2303fc <_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE>. -/
theorem emit_parts_p684 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297460#64)
    (fetched : s.program.find? (bias + 2297460#64) = some 0x97fffd62#32) :
    stepi s = w (.GPR 30#5) (bias + 2297464#64)
      (w .PC (bias + 2294780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 716: bl 0x24d4d0 <memcpy>. -/
theorem emit_parts_p716 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297492#64)
    (fetched : s.program.find? (bias + 2297492#64) = some 0x9400718f#32) :
    stepi s = w (.GPR 30#5) (bias + 2297496#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 868: bl 0x24d4d0 <memcpy>. -/
theorem emit_parts_p868 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297644#64)
    (fetched : s.program.find? (bias + 2297644#64) = some 0x94007169#32) :
    stepi s = w (.GPR 30#5) (bias + 2297648#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 1132: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_parts_p1132 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297908#64)
    (fetched : s.program.find? (bias + 2297908#64) = some 0x97ffb443#32) :
    stepi s = w (.GPR 30#5) (bias + 2297912#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 1148: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_parts_p1148 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297924#64)
    (fetched : s.program.find? (bias + 2297924#64) = some 0x97ffb43f#32) :
    stepi s = w (.GPR 30#5) (bias + 2297928#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 1164: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem emit_parts_p1164 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297940#64)
    (fetched : s.program.find? (bias + 2297940#64) = some 0x97ffb43b#32) :
    stepi s = w (.GPR 30#5) (bias + 2297944#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 1176: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem emit_parts_p1176 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297952#64)
    (fetched : s.program.find? (bias + 2297952#64) = some 0x97ffb444#32) :
    stepi s = w (.GPR 30#5) (bias + 2297956#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- EmitParts + 1188: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem emit_parts_p1188 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2297964#64)
    (fetched : s.program.find? (bias + 2297964#64) = some 0x97ffb441#32) :
    stepi s = w (.GPR 30#5) (bias + 2297968#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- IsFixed + 120: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem is_fixed_p120 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2298088#64)
    (fetched : s.program.find? (bias + 2298088#64) = some 0x97ffffe2#32) :
    stepi s = w (.GPR 30#5) (bias + 2298092#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 88: bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>. -/
theorem measure_fixed_p88 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321196#64)
    (fetched : s.program.find? (bias + 2321196#64) = some 0x97ffffea#32) :
    stepi s = w (.GPR 30#5) (bias + 2321200#64)
      (w .PC (bias + 2321108#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 120: bl 0x24d4d0 <memcpy>. -/
theorem measure_fixed_p120 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321228#64)
    (fetched : s.program.find? (bias + 2321228#64) = some 0x94005a61#32) :
    stepi s = w (.GPR 30#5) (bias + 2321232#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 252: bl 0x220c98 <_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE>. -/
theorem measure_fixed_p252 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321360#64)
    (fetched : s.program.find? (bias + 2321360#64) = some 0x97ffa832#32) :
    stepi s = w (.GPR 30#5) (bias + 2321364#64)
      (w .PC (bias + 2231448#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 284: bl 0x24d4d0 <memcpy>. -/
theorem measure_fixed_p284 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321392#64)
    (fetched : s.program.find? (bias + 2321392#64) = some 0x94005a38#32) :
    stepi s = w (.GPR 30#5) (bias + 2321396#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 360: bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>. -/
theorem measure_fixed_p360 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321468#64)
    (fetched : s.program.find? (bias + 2321468#64) = some 0x97ffffa6#32) :
    stepi s = w (.GPR 30#5) (bias + 2321472#64)
      (w .PC (bias + 2321108#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 436: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_fixed_p436 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321544#64)
    (fetched : s.program.find? (bias + 2321544#64) = some 0x97ffb2e9#32) :
    stepi s = w (.GPR 30#5) (bias + 2321548#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 496: bl 0x22382c <_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE>. -/
theorem measure_fixed_p496 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321604#64)
    (fetched : s.program.find? (bias + 2321604#64) = some 0x97ffb2da#32) :
    stepi s = w (.GPR 30#5) (bias + 2321608#64)
      (w .PC (bias + 2242604#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 524: bl 0x24d4d0 <memcpy>. -/
theorem measure_fixed_p524 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321632#64)
    (fetched : s.program.find? (bias + 2321632#64) = some 0x940059fc#32) :
    stepi s = w (.GPR 30#5) (bias + 2321636#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 608: bl 0x22487c <_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E>. -/
theorem measure_fixed_p608 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321716#64)
    (fetched : s.program.find? (bias + 2321716#64) = some 0x97ffb6d2#32) :
    stepi s = w (.GPR 30#5) (bias + 2321720#64)
      (w .PC (bias + 2246780#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 768: bl 0x24d4d0 <memcpy>. -/
theorem measure_fixed_p768 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321876#64)
    (fetched : s.program.find? (bias + 2321876#64) = some 0x940059bf#32) :
    stepi s = w (.GPR 30#5) (bias + 2321880#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- MeasureFixed + 808: bl 0x24d4d0 <memcpy>. -/
theorem measure_fixed_p808 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2321916#64)
    (fetched : s.program.find? (bias + 2321916#64) = some 0x940059b5#32) :
    stepi s = w (.GPR 30#5) (bias + 2321920#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 356: bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>. -/
theorem decode_fixed_p356 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322292#64)
    (fetched : s.program.find? (bias + 2322292#64) = some 0x97fff38b#32) :
    stepi s = w (.GPR 30#5) (bias + 2322296#64)
      (w .PC (bias + 2309536#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 424: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p424 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322360#64)
    (fetched : s.program.find? (bias + 2322360#64) = some 0x94005946#32) :
    stepi s = w (.GPR 30#5) (bias + 2322364#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 440: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p440 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322376#64)
    (fetched : s.program.find? (bias + 2322376#64) = some 0x94005942#32) :
    stepi s = w (.GPR 30#5) (bias + 2322380#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 484: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p484 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322420#64)
    (fetched : s.program.find? (bias + 2322420#64) = some 0x94005937#32) :
    stepi s = w (.GPR 30#5) (bias + 2322424#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 548: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p548 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322484#64)
    (fetched : s.program.find? (bias + 2322484#64) = some 0x94005927#32) :
    stepi s = w (.GPR 30#5) (bias + 2322488#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 644: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p644 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322580#64)
    (fetched : s.program.find? (bias + 2322580#64) = some 0x9400590f#32) :
    stepi s = w (.GPR 30#5) (bias + 2322584#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 664: bl 0x24d4d0 <memcpy>. -/
theorem decode_fixed_p664 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322600#64)
    (fetched : s.program.find? (bias + 2322600#64) = some 0x9400590a#32) :
    stepi s = w (.GPR 30#5) (bias + 2322604#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeFixed + 684: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem decode_fixed_p684 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322620#64)
    (fetched : s.program.find? (bias + 2322620#64) = some 0x97ff9c21#32) :
    stepi s = w (.GPR 30#5) (bias + 2322624#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 956: bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>. -/
theorem decode_offsets_p956 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2323688#64)
    (fetched : s.program.find? (bias + 2323688#64) = some 0x97fff22e#32) :
    stepi s = w (.GPR 30#5) (bias + 2323692#64)
      (w .PC (bias + 2309536#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1024: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1024 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2323756#64)
    (fetched : s.program.find? (bias + 2323756#64) = some 0x940057e9#32) :
    stepi s = w (.GPR 30#5) (bias + 2323760#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1040: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1040 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2323772#64)
    (fetched : s.program.find? (bias + 2323772#64) = some 0x940057e5#32) :
    stepi s = w (.GPR 30#5) (bias + 2323776#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1084: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1084 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2323816#64)
    (fetched : s.program.find? (bias + 2323816#64) = some 0x940057da#32) :
    stepi s = w (.GPR 30#5) (bias + 2323820#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1160: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1160 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2323892#64)
    (fetched : s.program.find? (bias + 2323892#64) = some 0x940057c7#32) :
    stepi s = w (.GPR 30#5) (bias + 2323896#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1304: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1304 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324036#64)
    (fetched : s.program.find? (bias + 2324036#64) = some 0x940057a3#32) :
    stepi s = w (.GPR 30#5) (bias + 2324040#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1324: bl 0x24d4d0 <memcpy>. -/
theorem decode_offsets_p1324 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324056#64)
    (fetched : s.program.find? (bias + 2324056#64) = some 0x9400579e#32) :
    stepi s = w (.GPR 30#5) (bias + 2324060#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1344: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem decode_offsets_p1344 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324076#64)
    (fetched : s.program.find? (bias + 2324076#64) = some 0x97ff9ab5#32) :
    stepi s = w (.GPR 30#5) (bias + 2324080#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1360: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1360 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324092#64)
    (fetched : s.program.find? (bias + 2324092#64) = some 0x97ff9abd#32) :
    stepi s = w (.GPR 30#5) (bias + 2324096#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1376: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1376 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324108#64)
    (fetched : s.program.find? (bias + 2324108#64) = some 0x97ff9ab9#32) :
    stepi s = w (.GPR 30#5) (bias + 2324112#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1392: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1392 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324124#64)
    (fetched : s.program.find? (bias + 2324124#64) = some 0x97ff9ab5#32) :
    stepi s = w (.GPR 30#5) (bias + 2324128#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1408: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1408 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324140#64)
    (fetched : s.program.find? (bias + 2324140#64) = some 0x97ff9ab1#32) :
    stepi s = w (.GPR 30#5) (bias + 2324144#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1420: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1420 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324152#64)
    (fetched : s.program.find? (bias + 2324152#64) = some 0x97ff9aae#32) :
    stepi s = w (.GPR 30#5) (bias + 2324156#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1432: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1432 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324164#64)
    (fetched : s.program.find? (bias + 2324164#64) = some 0x97ff9aab#32) :
    stepi s = w (.GPR 30#5) (bias + 2324168#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1444: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1444 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324176#64)
    (fetched : s.program.find? (bias + 2324176#64) = some 0x97ff9aa8#32) :
    stepi s = w (.GPR 30#5) (bias + 2324180#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1456: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1456 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324188#64)
    (fetched : s.program.find? (bias + 2324188#64) = some 0x97ff9aa5#32) :
    stepi s = w (.GPR 30#5) (bias + 2324192#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1468: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1468 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324200#64)
    (fetched : s.program.find? (bias + 2324200#64) = some 0x97ff9aa2#32) :
    stepi s = w (.GPR 30#5) (bias + 2324204#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1480: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1480 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324212#64)
    (fetched : s.program.find? (bias + 2324212#64) = some 0x97ff9a9f#32) :
    stepi s = w (.GPR 30#5) (bias + 2324216#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1492: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1492 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324224#64)
    (fetched : s.program.find? (bias + 2324224#64) = some 0x97ff9a9c#32) :
    stepi s = w (.GPR 30#5) (bias + 2324228#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeOffsets + 1504: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_offsets_p1504 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324236#64)
    (fetched : s.program.find? (bias + 2324236#64) = some 0x97ff9a99#32) :
    stepi s = w (.GPR 30#5) (bias + 2324240#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 252: bl 0x231070 <_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E>. -/
theorem decode_list_p252 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324492#64)
    (fetched : s.program.find? (bias + 2324492#64) = some 0x97ffe619#32) :
    stepi s = w (.GPR 30#5) (bias + 2324496#64)
      (w .PC (bias + 2297968#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 312: bl 0x236ad4 <_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E>. -/
theorem decode_list_p312 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324552#64)
    (fetched : s.program.find? (bias + 2324552#64) = some 0x97fffca3#32) :
    stepi s = w (.GPR 30#5) (bias + 2324556#64)
      (w .PC (bias + 2321108#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 344: bl 0x24d4d0 <memcpy>. -/
theorem decode_list_p344 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2324584#64)
    (fetched : s.program.find? (bias + 2324584#64) = some 0x9400571a#32) :
    stepi s = w (.GPR 30#5) (bias + 2324588#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 1772: bl 0x2386dc <_ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE>. -/
theorem decode_list_p1772 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326012#64)
    (fetched : s.program.find? (bias + 2326012#64) = some 0x94000238#32) :
    stepi s = w (.GPR 30#5) (bias + 2326016#64)
      (w .PC (bias + 2328284#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 1836: b 0x23712c <_ZN13ssz_fv_native5codec14decode_offsets17h3986df5c439cd32dE>. -/
theorem decode_list_p1836 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326076#64)
    (fetched : s.program.find? (bias + 2326076#64) = some 0x17fffcbc#32) :
    stepi s = w .PC (bias + 2322732#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- DecodeList + 2436: bl 0x2386dc <_ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE>. -/
theorem decode_list_p2436 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326676#64)
    (fetched : s.program.find? (bias + 2326676#64) = some 0x94000192#32) :
    stepi s = w (.GPR 30#5) (bias + 2326680#64)
      (w .PC (bias + 2328284#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 2460: bl 0x24d4d0 <memcpy>. -/
theorem decode_list_p2460 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326700#64)
    (fetched : s.program.find? (bias + 2326700#64) = some 0x94005509#32) :
    stepi s = w (.GPR 30#5) (bias + 2326704#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeList + 2524: b 0x236e10 <_ZN13ssz_fv_native5codec12decode_fixed17hd268ce61b5ac9b5fE>. -/
theorem decode_list_p2524 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326764#64)
    (fetched : s.program.find? (bias + 2326764#64) = some 0x17fffb49#32) :
    stepi s = w .PC (bias + 2321936#64) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]

/-- DecodeList + 2720: bl 0x21e67c <_ZN4core5slice4sort6shared9smallsort22panic_on_ord_violation17h3e94085727ccf329E>. -/
theorem decode_list_p2720 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2326960#64)
    (fetched : s.program.find? (bias + 2326960#64) = some 0x97ff9933#32) :
    stepi s = w (.GPR 30#5) (bias + 2326964#64)
      (w .PC (bias + 2221692#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ReadOffset + 76: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem read_offset_p76 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322700#64)
    (fetched : s.program.find? (bias + 2322700#64) = some 0x97ff9c19#32) :
    stepi s = w (.GPR 30#5) (bias + 2322704#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ReadOffset + 84: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem read_offset_p84 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322708#64)
    (fetched : s.program.find? (bias + 2322708#64) = some 0x97ff9c17#32) :
    stepi s = w (.GPR 30#5) (bias + 2322712#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ReadOffset + 96: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem read_offset_p96 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322720#64)
    (fetched : s.program.find? (bias + 2322720#64) = some 0x97ff9c14#32) :
    stepi s = w (.GPR 30#5) (bias + 2322724#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- ReadOffset + 104: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem read_offset_p104 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2322728#64)
    (fetched : s.program.find? (bias + 2322728#64) = some 0x97ff9c12#32) :
    stepi s = w (.GPR 30#5) (bias + 2322732#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- Bounded + 52: bl 0x2255ac <_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE>. -/
theorem bounded_p52 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328336#64)
    (fetched : s.program.find? (bias + 2328336#64) = some 0x97ffb3a7#32) :
    stepi s = w (.GPR 30#5) (bias + 2328340#64)
      (w .PC (bias + 2250156#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- PlanSingleton + 104: bl 0x24d4d0 <memcpy>. -/
theorem plan_singleton_p104 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2299976#64)
    (fetched : s.program.find? (bias + 2299976#64) = some 0x94006f22#32) :
    stepi s = w (.GPR 30#5) (bias + 2299980#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 244: bl 0x233da0 <_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE>. -/
theorem decode_struct_values_p244 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2327888#64)
    (fetched : s.program.find? (bias + 2327888#64) = some 0x97ffee14#32) :
    stepi s = w (.GPR 30#5) (bias + 2327892#64)
      (w .PC (bias + 2309536#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 316: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p316 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2327960#64)
    (fetched : s.program.find? (bias + 2327960#64) = some 0x940053ce#32) :
    stepi s = w (.GPR 30#5) (bias + 2327964#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 332: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p332 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2327976#64)
    (fetched : s.program.find? (bias + 2327976#64) = some 0x940053ca#32) :
    stepi s = w (.GPR 30#5) (bias + 2327980#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 376: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p376 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328020#64)
    (fetched : s.program.find? (bias + 2328020#64) = some 0x940053bf#32) :
    stepi s = w (.GPR 30#5) (bias + 2328024#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 444: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p444 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328088#64)
    (fetched : s.program.find? (bias + 2328088#64) = some 0x940053ae#32) :
    stepi s = w (.GPR 30#5) (bias + 2328092#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 560: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p560 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328204#64)
    (fetched : s.program.find? (bias + 2328204#64) = some 0x94005391#32) :
    stepi s = w (.GPR 30#5) (bias + 2328208#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 580: bl 0x24d4d0 <memcpy>. -/
theorem decode_struct_values_p580 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328224#64)
    (fetched : s.program.find? (bias + 2328224#64) = some 0x9400538c#32) :
    stepi s = w (.GPR 30#5) (bias + 2328228#64)
      (w .PC (bias + 2413776#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 612: bl 0x21e140 <_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E>. -/
theorem decode_struct_values_p612 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328256#64)
    (fetched : s.program.find? (bias + 2328256#64) = some 0x97ff96a0#32) :
    stepi s = w (.GPR 30#5) (bias + 2328260#64)
      (w .PC (bias + 2220352#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 624: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_struct_values_p624 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328268#64)
    (fetched : s.program.find? (bias + 2328268#64) = some 0x97ff96a9#32) :
    stepi s = w (.GPR 30#5) (bias + 2328272#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

/-- DecodeStructValues + 636: bl 0x21e170 <_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE>. -/
theorem decode_struct_values_p636 (s : ArmState) (bias : BitVec 64)
    (error : read_err s = .None)
    (entry : read_pc s = bias + 2328280#64)
    (fetched : s.program.find? (bias + 2328280#64) = some 0x97ff96a6#32) :
    stepi s = w (.GPR 30#5) (bias + 2328284#64)
      (w .PC (bias + 2220400#64) s) := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at entry
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, entry, BitVec.add_assoc]
  all_goals exact w_of_w_commute (by decide)

end SszArm.Codec.Linked.Branches

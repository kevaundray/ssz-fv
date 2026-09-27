import SszArm.ByteViewImpl
import SszArm.BoolMemory

namespace SszArm.ByteView.Vector

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def widthLoaded (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64)
    (w (.GPR 9) (read_mem_bytes 8 (r (.GPR 1) s + 16#64) s)
      (w (.GPR 8) (read_mem_bytes 8 (r (.GPR 1) s + 8#64) s) s))

theorem width_load (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 1972#64) (he : read_err s = .None) :
    stepi s = widthLoaded s := by
  have hf := hc (1972, 0xa940a428#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, widthLoaded, state_simp_rules, bitvec_rules, minimal_theory,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]

theorem width_cbz (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 1976#64) (he : read_err s = .None) :
    stepi s = w .PC (if r (.GPR 8) s = 0#64 then base + 3468#64 else base + 1980#64) s := by
  have hf := hc (1976, 0xb4002ea8#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = base + 1976#64 at hp
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hp, BitVec.add_assoc]

/-- The actual descriptor pair load and niche test select Small versus Large. -/
theorem width_branch (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 1972#64) (he : read_err s = .None) :
    run 2 s = w .PC
      (if read_mem_bytes 8 (r (.GPR 1) s + 8#64) s = 0#64 then base + 3468#64 else base + 1980#64)
      (widthLoaded s) := by
  have hc' : CodeAt (widthLoaded s) base := by
    simpa [CodeAt, widthLoaded, state_simp_rules] using hc
  have hp' : read_pc (widthLoaded s) = base + 1976#64 := by
    have hpc : r .PC s = base + 1972#64 := hp
    simp [widthLoaded, state_simp_rules, hpc, BitVec.add_assoc]
  have he' : read_err (widthLoaded s) = .None := by
    simpa [widthLoaded, state_simp_rules] using he
  change stepi (stepi s) = _
  rw [width_load s base hc hp he, width_cbz (widthLoaded s) base hc' hp' he']
  simp (config := {decide := true}) [widthLoaded, state_simp_rules]

def widthXored (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR 10) (r (.GPR 10) s ^^^ r (.GPR 3) s) s)

def widthJoined (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR 10) (r (.GPR 10) s ||| r (.GPR 11) s) s)

theorem width_xor (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4480#64) (he : read_err s = .None) :
    stepi s = widthXored s := by
  have hf := hc (4480, 0xca03014a#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, widthXored, state_simp_rules, bitvec_rules, minimal_theory]
  exact w_of_w_commute (by decide)

theorem width_or (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4484#64) (he : read_err s = .None) :
    stepi s = widthJoined s := by
  have hf := hc (4484, 0xaa0b014a#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, widthJoined, state_simp_rules, bitvec_rules, minimal_theory]
  exact w_of_w_commute (by decide)

theorem width_cbnz (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4488#64) (he : read_err s = .None) :
    stepi s = w .PC (if r (.GPR 10) s = 0#64 then base + 4492#64 else base + 4544#64) s := by
  have hf := hc (4488, 0xb50001ca#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = base + 4488#64 at hp
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, hp, BitVec.add_assoc]

/-- The two-word width comparison rejects exactly a nonzero high word or a
mismatching low word, without truncating a wide descriptor to the input length. -/
theorem width_comparison (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4480#64) (he : read_err s = .None) :
    run 3 s = w .PC
      (if r (.GPR 10) s = r (.GPR 3) s ∧ r (.GPR 11) s = 0#64
       then base + 4492#64 else base + 4544#64) (widthJoined (widthXored s)) := by
  have hc1 : CodeAt (widthXored s) base := by
    simpa [CodeAt, widthXored, state_simp_rules] using hc
  have he1 : read_err (widthXored s) = .None := by
    simpa [widthXored, state_simp_rules] using he
  have hp1 : read_pc (widthXored s) = base + 4484#64 := by
    have hpc : r .PC s = base + 4480#64 := hp
    simp [widthXored, state_simp_rules, hpc, BitVec.add_assoc]
  have hc2 : CodeAt (widthJoined (widthXored s)) base := by
    simpa [CodeAt, widthJoined, state_simp_rules] using hc1
  have he2 : read_err (widthJoined (widthXored s)) = .None := by
    simpa [widthJoined, state_simp_rules] using he1
  have hp2 : read_pc (widthJoined (widthXored s)) = base + 4488#64 := by
    have hpc : r .PC (widthXored s) = base + 4484#64 := hp1
    simp [widthJoined, state_simp_rules, hpc, BitVec.add_assoc]
  change stepi (stepi (stepi s)) = _
  rw [width_xor s base hc hp he, width_or (widthXored s) base hc1 hp1 he1,
    width_cbnz (widthJoined (widthXored s)) base hc2 hp2 he2]
  simp (config := {decide := true}) [widthJoined, widthXored, state_simp_rules]

def smallWidthPrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4480#64) (w (.GPR 10) (r (.GPR 9) s) (w (.GPR 11) 0#64 s))

theorem small_width (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 3468#64) (he : read_err s = .None) :
    run 3 s = smallWidthPrepared s base := by
  let s1 := w .PC (base + 3472#64) (w (.GPR 11) 0#64 s)
  let s2 := w .PC (base + 3476#64) (w (.GPR 10) (r (.GPR 9) s) s1)
  have hpc : r .PC s = base + 3468#64 := hp
  have h1 : stepi s = s1 := by
    have hf := hc (3468, 0xaa1f03eb#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, s1, hpc, BitVec.add_assoc]
    exact w_of_w_commute (by decide)
  have h2 : stepi s1 = s2 := by
    have hf := hc (3472, 0xaa0903ea#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s1 _ _ _
      (by simpa [s1, state_simp_rules] using he)
      (show read_pc s1 = base + 3472#64 by simp [s1, state_simp_rules])
      (by simpa [fetch_inst, s1, state_simp_rules] using (fetch_inst_from_program.trans hf)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, s2, s1, BitVec.add_assoc]
    simp [w, write_base_pc, write_base_gpr]
  have h3 : stepi s2 = w .PC (base + 4480#64) s2 := by
    have hf := hc (3476, 0x140000fb#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s2 _ _ _
      (by simpa [s2, s1, state_simp_rules] using he)
      (show read_pc s2 = base + 3476#64 by simp [s2, state_simp_rules])
      (by simpa [fetch_inst, s2, s1, state_simp_rules] using (fetch_inst_from_program.trans hf)) rfl]
    simp [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, s2, BitVec.add_assoc]
  change stepi (stepi (stepi s)) = _
  rw [h1, h2, h3]
  simp [smallWidthPrepared, s2, s1, w, write_base_pc, write_base_gpr]

/-- Complete Small-descriptor width check, before any input byte is read. -/
theorem small_descriptor (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 1972#64) (he : read_err s = .None)
    (hsmall : read_mem_bytes 8 (r (.GPR 1) s + 8#64) s = 0#64) :
    let t := w .PC (base + 3468#64) (widthLoaded s)
    run 8 s = w .PC
      (if read_mem_bytes 8 (r (.GPR 1) s + 16#64) s = r (.GPR 3) s
       then base + 4492#64 else base + 4544#64)
      (widthJoined (widthXored (smallWidthPrepared t base))) := by
  let t := w .PC (base + 3468#64) (widthLoaded s)
  have ht : run 2 s = t := by
    simpa only [t, hsmall, ↓reduceIte] using width_branch s base hc hp he
  have htc : CodeAt t base := by
    simpa [t, widthLoaded, CodeAt, state_simp_rules] using hc
  have hte : read_err t = .None := by
    simpa [t, widthLoaded, state_simp_rules] using he
  have htp : read_pc t = base + 3468#64 := by simp [t, state_simp_rules]
  have hu : run 5 s = smallWidthPrepared t base := by
    rw [show 5 = 2 + 3 by decide, run_plus, ht, small_width t base htc htp hte]
  have huc : CodeAt (smallWidthPrepared t base) base := by
    simpa [smallWidthPrepared, CodeAt, state_simp_rules] using htc
  have hue : read_err (smallWidthPrepared t base) = .None := by
    simpa [smallWidthPrepared, state_simp_rules] using hte
  have hup : read_pc (smallWidthPrepared t base) = base + 4480#64 := by
    simp [smallWidthPrepared, state_simp_rules]
  dsimp only
  conv => lhs; change run (5 + 3) s
  rw [run_plus, hu,
    width_comparison (smallWidthPrepared t base) base huc hup hue]
  simp (config := {decide := true}) [smallWidthPrepared, t, widthLoaded, state_simp_rules]

end SszArm.ByteView.Vector

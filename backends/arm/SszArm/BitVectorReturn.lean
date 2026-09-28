import SszArm.BitVectorMemory

namespace SszArm.BitVector

open BoolCodec
open Delimited (Protected MemoryFrame)

/-- Execute the actual common six-pair epilogue, ADD SP and RET from this body
image. The summary is shared with the other codec proofs. -/
theorem epilogue (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (pc : read_pc s = base + 4732#64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    run 8 s = BoolCodec.returned s := by
  let sp := r (.GPR 31#5) s
  let s1 := w .PC (base + 4736#64)
    (w (.GPR 19#5) (read_mem_bytes 8 (sp + 360#64) s)
      (w (.GPR 20#5) (read_mem_bytes 8 (sp + 352#64) s) s))
  let s2 := w .PC (base + 4740#64)
    (w (.GPR 21#5) (read_mem_bytes 8 (sp + 344#64) s)
      (w (.GPR 22#5) (read_mem_bytes 8 (sp + 336#64) s) s1))
  let s3 := w .PC (base + 4744#64)
    (w (.GPR 23#5) (read_mem_bytes 8 (sp + 328#64) s)
      (w (.GPR 24#5) (read_mem_bytes 8 (sp + 320#64) s) s2))
  let s4 := w .PC (base + 4748#64)
    (w (.GPR 25#5) (read_mem_bytes 8 (sp + 312#64) s)
      (w (.GPR 26#5) (read_mem_bytes 8 (sp + 304#64) s) s3))
  let s5 := w .PC (base + 4752#64)
    (w (.GPR 27#5) (read_mem_bytes 8 (sp + 296#64) s)
      (w (.GPR 28#5) (read_mem_bytes 8 (sp + 288#64) s) s4))
  let s6 := w .PC (base + 4756#64)
    (w (.GPR 30#5) (read_mem_bytes 8 (sp + 280#64) s)
      (w (.GPR 29#5) (read_mem_bytes 8 (sp + 272#64) s) s5))
  let s7 := w .PC (base + 4760#64) (w (.GPR 31#5) (sp + 368#64) s6)
  have hpc : r .PC s = base + 4732#64 := pc
  have h1 : stepi s = s1 := by
    have fetched := code (4732, 0xa9564ff4#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s1, sp, hpc, aligned, BitVec.add_assoc]
  have h2 : stepi s1 = s2 := by
    have fetched := code (4736, 0xa95557f6#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s1 _ _ _
      (by simpa [s1, state_simp_rules] using error)
      (show read_pc s1 = base + 4736#64 by simp [s1, state_simp_rules])
      (by simpa [fetch_inst, s1, state_simp_rules] using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s2, s1, sp, aligned, BitVec.add_assoc]
  have h3 : stepi s2 = s3 := by
    have fetched := code (4740, 0xa9545ff8#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s2 _ _ _
      (by simpa [s2, s1, state_simp_rules] using error)
      (show read_pc s2 = base + 4740#64 by simp [s2, state_simp_rules])
      (by simpa [fetch_inst, s2, s1, state_simp_rules] using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s3, s2, s1, sp, aligned, BitVec.add_assoc]
  have h4 : stepi s3 = s4 := by
    have fetched := code (4744, 0xa95367fa#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s3 _ _ _
      (by simpa [s3, s2, s1, state_simp_rules] using error)
      (show read_pc s3 = base + 4744#64 by simp [s3, state_simp_rules])
      (by simpa [fetch_inst, s3, s2, s1, state_simp_rules] using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s4, s3, s2, s1, sp, aligned, BitVec.add_assoc]
  have h5 : stepi s4 = s5 := by
    have fetched := code (4748, 0xa9526ffc#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s4 _ _ _
      (by simpa [s4, s3, s2, s1, state_simp_rules] using error)
      (show read_pc s4 = base + 4748#64 by simp [s4, state_simp_rules])
      (by simpa [fetch_inst, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s5, s4, s3, s2, s1, sp, aligned, BitVec.add_assoc]
  have h6 : stepi s5 = s6 := by
    have fetched := code (4752, 0xa9517bfd#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s5 _ _ _
      (by simpa [s5, s4, s3, s2, s1, state_simp_rules] using error)
      (show read_pc s5 = base + 4752#64 by simp [s5, state_simp_rules])
      (by simpa [fetch_inst, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pair_read_low, pair_read_high, s6, s5, s4, s3, s2, s1, sp, aligned, BitVec.add_assoc]
  have h7 : stepi s6 = s7 := by
    have fetched := code (4756, 0x9105c3ff#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s6 _ _ _
      (by simpa [s6, s5, s4, s3, s2, s1, state_simp_rules] using error)
      (show read_pc s6 = base + 4756#64 by simp [s6, state_simp_rules])
      (by simpa [fetch_inst, s6, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       s7, s6, s5, s4, s3, s2, s1, sp, BitVec.add_assoc]
    simp only [w, write_base_pc, write_base_gpr]
  have h8 : stepi s7 = BoolCodec.returned s := by
    have fetched := code (4760, 0xd65f03c0#32) (by decide)
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s7 _ _ _
      (by simpa [s7, s6, s5, s4, s3, s2, s1, state_simp_rules] using error)
      (show read_pc s7 = base + 4760#64 by simp [s7, state_simp_rules])
      (by simpa [fetch_inst, s7, s6, s5, s4, s3, s2, s1, state_simp_rules]
        using (fetch_inst_from_program.trans fetched)) rfl]
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.returned, s7, s6, s5, s4, s3, s2, s1, sp]
    simp only [w, write_base_pc, write_base_gpr]
  change stepi (stepi (stepi (stepi (stepi (stepi (stepi (stepi s))))))) = _
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

end SszArm.BitVector

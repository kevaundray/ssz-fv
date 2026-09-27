import SszArm.BoolImpl
import SszArm.Udivti3Arithmetic

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The comparison changes only flags and PC. -/
def lengthCompared (s : ArmState) : ArmState :=
  Udivti3.compare (r (.GPR 3) s) 1#64 s

theorem length_cmp (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 604#64) (he : read_err s = .None) :
    stepi s = lengthCompared s := by
  have hf := hc (604, 0xf100047f#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, lengthCompared, Udivti3.compare, Udivti3.next,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]

theorem length_jne (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 608#64) (he : read_err s = .None) :
    stepi s = w .PC (if r (.FLAG .Z) s = 1#1 then base + 612#64 else base + 2084#64) s := by
  have hf := hc (608, 0x54002e21#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = base + 608#64 at hp
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     hp, BitVec.add_assoc, apply_ite]
  split <;> simp_all

/-- Both actual CMP/B.NE instructions, for every 64-bit length. No data memory
is read; non-unit lengths go directly to the scope-error stores. -/
theorem length_branch (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 604#64) (he : read_err s = .None) :
    run 2 s = w .PC (if r (.GPR 3) s = 1#64 then base + 612#64 else base + 2084#64)
      (lengthCompared s) := by
  have hc' : CodeAt (lengthCompared s) base := by
    simpa [CodeAt, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using hc
  have hp' : read_pc (lengthCompared s) = base + 608#64 := by
    have hpc : r .PC s = base + 604#64 := hp
    simp [lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]
  have he' : read_err (lengthCompared s) = .None := by
    simpa [lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules] using he
  change stepi (stepi s) = _
  rw [length_cmp s base hc hp he, length_jne (lengthCompared s) base hc' hp' he']
  simp [lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules]

def byteLoaded (s : ArmState) : ArmState :=
  w (.GPR 8) ((read_mem_bytes 1 (r (.GPR 2) s) s).setWidth 64)
    (w .PC (read_pc s + 4#64) s)

def byteCompared (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry ((r (.GPR 8) s).setWidth 32) (~~~1#32) 1#1).2
    (w .PC (read_pc s + 4#64) s)

/-- The actual byte load occurs only after the length-one branch. -/
theorem byte_load (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 612#64) (he : read_err s = .None) :
    stepi s = byteLoaded s := by
  have hf := hc (612, 0x39400048#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, byteLoaded, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq]
  apply w_of_w_commute <;> decide

theorem byte_cbz (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 616#64) (he : read_err s = .None) :
    stepi s = w .PC
      (if (r (.GPR 8) s).setWidth 32 = 0#32 then base + 4084#64 else base + 620#64) s := by
  have hf := hc (616, 0x34006c68#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = base + 616#64 at hp
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     hp, BitVec.add_assoc]

theorem byte_cmp (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 620#64) (he : read_err s = .None) :
    stepi s = byteCompared s := by
  have hf := hc (620, 0x7100051f#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, byteCompared, state_simp_rules, bitvec_rules, minimal_theory]

theorem byte_jne (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 624#64) (he : read_err s = .None) :
    stepi s = w .PC (if r (.FLAG .Z) s = 1#1 then base + 628#64 else base + 4144#64) s := by
  have hf := hc (624, 0x54006e01#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = base + 624#64 at hp
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     hp, BitVec.add_assoc, apply_ite]
  split <;> simp_all

private theorem loaded_zero (s : ArmState) :
    (r (.GPR 8) (byteLoaded s)).setWidth 32 = 0#32 ↔
      read_mem_bytes 1 (r (.GPR 2) s) s = 0#8 := by
  simp only [byteLoaded, state_simp_rules]
  bv_omega

private theorem carry_zero {n : Nat} (a b : BitVec n) (carry : BitVec 1) :
    (AddWithCarry a b carry).2.z =
      (if (AddWithCarry a b carry).1 = 0#n then 1#1 else 0#1) := by
  rfl

private theorem compared_zero (s : ArmState) :
    r (.FLAG .Z) (byteCompared s) = 1#1 ↔ (r (.GPR 8) s).setWidth 32 = 1#32 := by
  simp (config := {decide := true}) only [byteCompared, state_simp_rules]
  rw [carry_zero, fst_AddWithCarry_eq_sub_neg]
  simp only [BitVec.not_not]
  have hz : (r (.GPR 8) s).setWidth 32 - 1#32 = 0#32 ↔
      (r (.GPR 8) s).setWidth 32 = 1#32 := by bv_omega
  simpa using hz

/-- LDRB/CBZ uses exactly the observed byte, not any prior high register bits. -/
theorem byte_zero_branch (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 612#64) (he : read_err s = .None) :
    run 2 s = w .PC
      (if read_mem_bytes 1 (r (.GPR 2) s) s = 0#8 then base + 4084#64 else base + 620#64)
      (byteLoaded s) := by
  have hc' : CodeAt (byteLoaded s) base := by
    simpa [CodeAt, byteLoaded, state_simp_rules] using hc
  have hp' : read_pc (byteLoaded s) = base + 616#64 := by
    have hpc : r .PC s = base + 612#64 := hp
    simp [byteLoaded, state_simp_rules, hpc, BitVec.add_assoc]
  have he' : read_err (byteLoaded s) = .None := by
    simpa [byteLoaded, state_simp_rules] using he
  change stepi (stepi s) = _
  rw [byte_load s base hc hp he, byte_cbz (byteLoaded s) base hc' hp' he']
  simp only [loaded_zero]

theorem byte_one_branch (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 620#64) (he : read_err s = .None) :
    run 2 s = w .PC
      (if (r (.GPR 8) s).setWidth 32 = 1#32 then base + 628#64 else base + 4144#64)
      (byteCompared s) := by
  have hc' : CodeAt (byteCompared s) base := by
    simpa [CodeAt, byteCompared, state_simp_rules] using hc
  have hp' : read_pc (byteCompared s) = base + 624#64 := by
    have hpc : r .PC s = base + 620#64 := hp
    simp [byteCompared, state_simp_rules, hpc, BitVec.add_assoc]
  have he' : read_err (byteCompared s) = .None := by
    simpa [byteCompared, state_simp_rules] using he
  change stepi (stepi s) = _
  rw [byte_cmp s base hc hp he, byte_jne (byteCompared s) base hc' hp' he']
  simp only [compared_zero s]

end SszArm.BoolCodec

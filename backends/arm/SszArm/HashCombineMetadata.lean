import SszArm.HashCombineControl

namespace SszArm.Hash.Combine

def metadataOps : List Op :=
  [.p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112, .p116, .p120, .p124, .p128]
def resetOps : List Op :=
  [.p268, .p272, .p276, .p280, .p284, .p288, .p292, .p296, .p300, .p304]
def rightGuardOps : List Op := [.p308, .p312]

@[irreducible] def metadata (s : ArmState) : ArmState := block metadataOps s
@[irreducible] def reset (s : ArmState) : ArmState := block resetOps s
@[irreducible] def rightGuard (s : ArmState) : ArmState := block rightGuardOps s

private theorem stack16_cancel (value : BitVec 64) :
    value - 16#64 + 16#64 = value := by
  bv_omega

theorem metadata_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 80#64) : run 13 s = metadata s := by
  have lowAligned : Aligned (r (.GPR 31#5) s - 16#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Aligned,
      ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  have follows : Follows base metadataOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Follows, metadataOps, Op.row, Op.effect, put, store, load, next, compare,
        state_simp_rules, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
        pc, BitVec.add_assoc] at aligned lowAligned ⊢
    exact ⟨aligned, lowAligned, by simpa only [stack16_cancel] using aligned⟩
  rw [metadata]
  exact runs metadataOps s base code error follows

@[simp] theorem metadata_program (s : ArmState) : (metadata s).program = s.program := by
  simp only [metadata, block_program]

@[simp] theorem metadata_error (s : ArmState) : read_err (metadata s) = read_err s := by
  simp only [metadata, block_error]

@[simp] theorem metadata_sp (s : ArmState) : r (.GPR 31#5) (metadata s) = r (.GPR 31#5) s := by
  simp [metadata, metadataOps, block, Op.effect, put, store, load, next,
    compare, branch, state_simp_rules, stack16_cancel]

@[simp] theorem metadata_register (s : ArmState) (reg : BitVec 5)
    (notSP : reg ≠ 31#5) (not9 : reg ≠ 9#5) (not10 : reg ≠ 10#5) :
    r (.GPR reg) (metadata s) = r (.GPR reg) s := by
  simp [metadata, metadataOps, block, Op.effect, put, store, load, next,
    compare, branch, state_simp_rules, notSP, not9, not10]

@[simp] theorem metadata_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (metadata s) = r (.SFP reg) s := by
  simp [metadata, metadataOps, block, Op.effect, put, store, load, next,
    compare, branch, state_simp_rules]

def metadataMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s + 104#64) (r (.GPR 22#5) s)
    (write_mem_bytes 8 (r (.GPR 31#5) s + 96#64) 0#64
      (write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR 10#5) s)
        (write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s)))

private theorem store8_memory (s : ArmState) (address value : BitVec 64) :
    (write_mem_bytes 8 address value s).mem =
      Memory.write_bytes 8 address value s.mem := by
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes]

theorem metadata_memory (s : ArmState) : (metadata s).mem = (metadataMemory s).mem := by
  simp [metadata, metadataOps, block, Op.effect, put, store, load, next,
    compare, branch, metadataMemory, state_simp_rules, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  simp only [store8_memory, ArmState.mem_w_eq_mem]

theorem metadata_fields (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) (metadata s) = 0#64 ∧
    read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) (metadata s) = r (.GPR 22#5) s := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (metadata_memory s)
  rw [reads 8, reads 8]
  simp only [metadataMemory]
  simp (disch := bv_omega) only [BoolCodec.read_mem_bytes_write_mem_bytes_same,
    BoolCodec.read_mem_bytes_write_mem_bytes_disjoint, and_self]

theorem metadata_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 80#64) :
    read_pc (metadata s) = if 64 ≤ (r (.GPR 22#5) s).toNat then base + 132#64 else base + 160#64 := by
  change r .PC s = _ at pc
  by_cases enough : 64 ≤ (r (.GPR 22#5) s).toNat
  · have carry := (Udivti3.cmp_carry (r (.GPR 22#5) s) 64#64).mpr enough
    rw [show ~~~64#64 = 18446744073709551551#64 by decide] at carry
    simp (config := {decide := true, instances := true})
      [metadata, metadataOps, block, Op.effect, put, store, load, next, compare, branch,
        state_simp_rules, pc, BitVec.add_assoc, carry, enough]
  · have carry : (AddWithCarry (r (.GPR 22#5) s) (~~~64#64) 1#1).2.c ≠ 1#1 := by
      intro h
      exact enough ((Udivti3.cmp_carry (r (.GPR 22#5) s) 64#64).mp h)
    rw [show ~~~64#64 = 18446744073709551551#64 by decide] at carry
    simp (config := {decide := true, instances := true})
      [metadata, metadataOps, block, Op.effect, put, store, load, next, compare, branch,
        state_simp_rules, pc, BitVec.add_assoc, carry, enough]

theorem reset_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 268#64) : run 10 s = reset s := by
  have lowAligned : Aligned (r (.GPR 31#5) s - 16#64) 4 := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Aligned,
      ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  have follows : Follows base resetOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Follows, resetOps, Op.row, Op.effect, put, store, load, next,
        state_simp_rules, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
        pc, BitVec.add_assoc] at aligned lowAligned ⊢
    exact ⟨aligned, lowAligned⟩
  rw [reset]
  exact runs resetOps s base code error follows

@[simp] theorem reset_sp (s : ArmState) : r (.GPR 31#5) (reset s) = r (.GPR 31#5) s := by
  simp [reset, resetOps, block, Op.effect, put, store, load, next,
    state_simp_rules, stack16_cancel]

@[simp] theorem reset_pc (s : ArmState) : read_pc (reset s) = read_pc s + 40#64 := by
  simp [reset, resetOps, block, Op.effect, put, store, load, next,
    state_simp_rules, BitVec.add_assoc]

theorem rightGuard_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 308#64) : run 2 s = rightGuard s := by
  have follows : Follows base rightGuardOps s := by
    change r .PC s = _ at pc
    simp [Follows, rightGuardOps, Op.row, Op.effect, compare, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [rightGuard]
  exact runs rightGuardOps s base code error follows

end SszArm.Hash.Combine

import SszArm.HashCombineCalls
import SszArm.HashCopyState
import SszArm.HashCombineReturn

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

def bodySP (s : ArmState) : BitVec 64 := r (.GPR 31#5) s - 304#64

def saveOps : List Op := [.p0, .p4, .p8, .p12, .p16, .p20]
def initializeOps : List Op :=
  [.p24, .p28, .p32, .p36, .p40, .p44, .p48, .p52, .p56, .p60, .p64, .p68, .p72]

@[irreducible] def saveEntry (s : ArmState) : ArmState := block saveOps s
@[irreducible] def initializeState (s : ArmState) : ArmState := block initializeOps s

@[simp] theorem saveEntry_sp (s : ArmState) : r (.GPR 31#5) (saveEntry s) = bodySP s := by
  simp [saveEntry, saveOps, block, Op.effect, put, store, save, next, bodySP, state_simp_rules]

@[simp] theorem saveEntry_register (s : ArmState) (reg : BitVec 5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (saveEntry s) = r (.GPR reg) s := by
  simp [saveEntry, saveOps, block, Op.effect, put, store, save, next, state_simp_rules, notSP]

@[simp] theorem saveEntry_pc (s : ArmState) : read_pc (saveEntry s) = read_pc s + 24#64 := by
  simp [saveEntry, saveOps, block, Op.effect, put, store, save, next,
    state_simp_rules, BitVec.add_assoc]

@[simp] theorem saveEntry_program (s : ArmState) : (saveEntry s).program = s.program := by
  simp only [saveEntry, block_program]

@[simp] theorem saveEntry_error (s : ArmState) : read_err (saveEntry s) = read_err s := by
  simp only [saveEntry, block_error]

theorem bodySP_aligned (s : ArmState) (aligned : CheckSPAlignment s) : Aligned (bodySP s) 4 := by
  simp (config := {decide := true}) [CheckSPAlignment, read_gpr, bodySP, Aligned,
    ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

theorem saveEntry_aligned (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (saveEntry s) :=
  CheckSPAlignment_of_r_sp_aligned (saveEntry_sp s) (bodySP_aligned s aligned)

theorem saveEntry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 6 s = saveEntry s := by
  have afterSP := bodySP_aligned s aligned
  have follows : Follows base saveOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Follows, saveOps, Op.row, Op.effect, put, store, save, next,
        state_simp_rules, CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
        bodySP, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  rw [saveEntry]
  exact runs saveOps s base code error follows

theorem initialize_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 24#64) : run 13 s = initializeState s := by
  have follows : Follows base initializeOps s := by
    change r .PC s = _ at pc
    simp [Follows, initializeOps, Op.row, Op.effect, put, next,
      state_simp_rules, aligned, pc, BitVec.add_assoc]
  rw [initializeState]
  exact runs initializeOps s base code error follows

@[simp] theorem initialize_program (s : ArmState) : (initializeState s).program = s.program := by
  simp only [initializeState, block_program]

@[simp] theorem initialize_error (s : ArmState) : read_err (initializeState s) = read_err s := by
  simp only [initializeState, block_error]

/-- The actual linked ADR at combine+48 is PC-relative, not an ADRP
substitution and not an arbitrary initial-table address. -/
theorem initialize_arguments (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 24#64) :
    read_pc (initializeState s) = base + 76#64 ∧
    r (.GPR 0#5) (initializeState s) = r (.GPR 31#5) s + 64#64 ∧
    r (.GPR 1#5) (initializeState s) = base + initialOffset ∧
    r (.GPR 2#5) (initializeState s) = 32#64 ∧
    r (.GPR 19#5) (initializeState s) = r (.GPR 0#5) s ∧
    r (.GPR 20#5) (initializeState s) = r (.GPR 4#5) s ∧
    r (.GPR 21#5) (initializeState s) = r (.GPR 3#5) s ∧
    r (.GPR 22#5) (initializeState s) = r (.GPR 2#5) s ∧
    r (.GPR 23#5) (initializeState s) = r (.GPR 1#5) s ∧
    r (.GPR 24#5) (initializeState s) = r (.GPR 31#5) s := by
  change r .PC s = _ at pc
  simp [initializeState, initializeOps, block, Op.effect, put, next,
    state_simp_rules, initialOffset, pc, BitVec.add_assoc]

private theorem store32_memory (s : ArmState) (address : BitVec 64) (value : BitVec 256) :
    (write_mem_bytes 32 address value s).mem =
      Memory.write_bytes 32 address value s.mem := by
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes]

theorem initialize_memory (s : ArmState) :
    (initializeState s).mem =
      (write_mem_bytes 32 (r (.GPR 31#5) s + 32#64) 0#256
        (write_mem_bytes 32 (r (.GPR 31#5) s) 0#256 s)).mem := by
  simp [initializeState, initializeOps, block, Op.effect, put, next, state_simp_rules]
  simp only [store32_memory, ArmState.mem_w_eq_mem]

theorem initialize_buffer (s : ArmState) (physical : (r (.GPR 31#5) s).toNat + 64 ≤ 2^64) :
    BytesAt (initializeState s) (r (.GPR 31#5) s) ⟨SszNative.HashStream.new.buffer.toArray⟩ := by
  intro i
  have index : i.val < 64 := by simpa only [vectorByteArray_size] using i.isLt
  have newByte :
      (ByteArray.mk SszNative.HashStream.new.buffer.toArray)[i.val].toBitVec = 0#8 := by
    change (Array.replicate 64 (0 : UInt8))[i.val].toBitVec = 0#8
    simp only [Array.getElem_replicate]
    decide
  have at32 : (r (.GPR 31#5) s + 32#64).toNat = (r (.GPR 31#5) s).toNat + 32 := by bv_omega
  have atIndex : (r (.GPR 31#5) s + BitVec.ofNat 64 i.val).toNat =
      (r (.GPR 31#5) s).toNat + i.val := by bv_omega
  rw [initialize_memory]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes]
  by_cases first : i.val < 32
  · rw [Memory.write_bytes_eq_of_le (by rw [atIndex, at32]; omega) (by rw [at32]; omega)]
    rw [Memory.write_bytes_eq_extractLsByte (by rw [atIndex]; omega)
      (by rw [atIndex]; omega) (by omega)]
    rw [BitVec.extractLsByte_zero]
    exact newByte.symm
  · rw [Memory.write_bytes_eq_extractLsByte (by rw [atIndex, at32]; omega)
      (by rw [atIndex, at32]; omega) (by rw [at32]; omega)]
    rw [BitVec.extractLsByte_zero]
    exact newByte.symm

end SszArm.Hash.Combine

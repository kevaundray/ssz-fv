import SszArm.IndicesLinkedElementType
import SszArm.CodecStorageTypes
import SszArm.BoolMemory

set_option autoImplicit false

namespace SszArm.Indices.ElementType

/-- The actual first store saves LR and x19, before either input tag is read. -/
def saved (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
    (w .PC (read_pc s + 4#64)
      (write_mem_bytes 16 (r (.GPR 31#5) s - 16#64)
        (r (.GPR 19#5) s ++ r (.GPR 30#5) s) s))

def loadDescriptor (s : ArmState) : ArmState :=
  w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s)
    (w .PC (read_pc s + 4#64) s)

def loadStep (s : ArmState) : ArmState :=
  w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 2#5) s) s)
    (w .PC (read_pc s + 4#64) s)

def entered (s : ArmState) : ArmState := loadStep (loadDescriptor (saved s))

theorem save_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : stepi s = saved s := by
  have fetched := Linked.ElementType.chunk0_codeAt code (0, 0xa9bf4ffe#32) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at fetched
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [saved, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem descriptor_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 4#64) :
    stepi s = loadDescriptor s := by
  have fetched := Linked.ElementType.chunk0_codeAt code (4, 0xf9400028#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [loadDescriptor, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem path_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 8#64) :
    stepi s = loadStep s := by
  have fetched := Linked.ElementType.chunk0_codeAt code (8, 0xf9400049#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [loadStep, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem saved_program (s : ArmState) : (saved s).program = s.program := by
  simp [saved, state_simp_rules]

@[simp] theorem loadDescriptor_program (s : ArmState) :
    (loadDescriptor s).program = s.program := by
  simp [loadDescriptor, state_simp_rules]

@[simp] theorem entered_program (s : ArmState) : (entered s).program = s.program := by
  simp [entered, loadStep, state_simp_rules]

@[simp] theorem entered_error (s : ArmState) : read_err (entered s) = read_err s := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules]

@[simp] theorem entered_pc (s : ArmState) : read_pc (entered s) = read_pc s + 12#64 := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules, BitVec.add_assoc]

@[simp] theorem entered_sp (s : ArmState) :
    r (.GPR 31#5) (entered s) = r (.GPR 31#5) s - 16#64 := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules]

/-- This starts at the original ELF entry and executes the real paired save and
both physical tag loads. No preloaded descriptor or path-register premise is used. -/
theorem entry_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : run 3 s = entered s := by
  have first := save_step s base code error aligned pc
  have second := descriptor_step (saved s) base
    (Codec.Linked.WordsAt.preserve code (saved_program s))
    (by simpa [saved, state_simp_rules] using error)
    (by simpa [saved, state_simp_rules] using congrArg (fun p => p + 4#64) pc)
  have third := path_step (loadDescriptor (saved s)) base
    (Codec.Linked.WordsAt.preserve code (by simp))
    (by simpa [loadDescriptor, saved, state_simp_rules] using error)
    (by simp [loadDescriptor, saved, state_simp_rules, pc, BitVec.add_assoc])
  change stepi (stepi (stepi s)) = entered s
  rw [first, second, third]
  rfl

/-- Only the actual 16-byte save is writable in this entry segment. -/
def entryWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16)]

theorem entered_memory (s : ArmState) :
    (entered s).mem = (write_mem_bytes 16 (r (.GPR 31#5) s - 16#64)
      (r (.GPR 19#5) s ++ r (.GPR 30#5) s) s).mem := by
  simp [entered, saved, loadDescriptor, loadStep, state_simp_rules]

theorem entered_frame (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame (entryWrites s) s (entered s) := by
  have pointer : (r (.GPR 31#5) s - 16#64).toNat =
      (r (.GPR 31#5) s).toNat - 16 := by
    have bound := (r (.GPR 31#5) s).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [entryWrites])
  simp only [Prod.fst, Prod.snd] at apart
  rw [entered_memory]
  apply BoolCodec.write_mem_bytes_frame
  · rw [pointer]
    have bound := (r (.GPR 31#5) s).isLt
    omega
  · simpa only [pointer] using apart

theorem descriptor_preserved {s : ArmState} {address : Nat} {shape : SszNative.Codec.Desc}
    (input : Codec.Storage.DescOwned (entryWrites s) s address shape)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Codec.Storage.DescOwned (entryWrites s) (entered s) address shape :=
  Codec.Storage.desc_preserved input (entered_frame s low)

end SszArm.Indices.ElementType

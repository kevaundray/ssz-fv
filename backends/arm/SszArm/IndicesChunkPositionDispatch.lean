import SszArm.IndicesLinkedChunkPosition
import SszArm.BoolMemory

set_option autoImplicit false

namespace SszArm.Indices.ChunkPosition

/-- The first continuation reads the actual element_type Result at SP+152.
The reason at +64 is tested before the descriptor discriminant is interpreted. -/
def loadElementPair (s : ArmState) : ArmState :=
  w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) s)
    (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 152#64) s)
      (w .PC (read_pc s + 4#64) s))

def loadElementReason (s : ArmState) : ArmState :=
  w (.GPR 9#5) ((read_mem_bytes 4 (r (.GPR 31#5) s + 216#64) s).zeroExtend 64)
    (w .PC (read_pc s + 4#64) s)

def loadElementPayload (s : ArmState) : ArmState :=
  w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 168#64) s)
    (w .PC (read_pc s + 4#64) s)

def branchElementReason (s : ArmState) : ArmState :=
  w .PC (if (r (.GPR 9#5) s).extractLsb' 0 32 = 0#32 then
    read_pc s + 48#64 else read_pc s + 4#64) s

def elementDispatched (s : ArmState) : ArmState :=
  branchElementReason (loadElementPayload (loadElementReason (loadElementPair s)))

theorem loadElementPair_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 48#64) :
    stepi s = loadElementPair s := by
  have fetched := Linked.ChunkPosition.chunk0_codeAt code (48, 0xa949d3e8#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [loadElementPair, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem loadElementReason_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 52#64) :
    stepi s = loadElementReason s := by
  have fetched := Linked.ChunkPosition.chunk0_codeAt code (52, 0xb940dbe9#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [loadElementReason, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem loadElementPayload_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 56#64) :
    stepi s = loadElementPayload s := by
  have fetched := Linked.ChunkPosition.chunk0_codeAt code (56, 0xf94057f5#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [loadElementPayload, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem branchElementReason_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 60#64) : stepi s = branchElementReason s := by
  have fetched := Linked.ChunkPosition.chunk0_codeAt code (60, 0x34000189#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [branchElementReason, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

/-- A legal internal cut: no element_type execution or logical postcondition is
assumed. Every loaded value is read from this continuation's concrete memory. -/
theorem element_dispatch_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 48#64) :
    run 4 s = elementDispatched s := by
  have a := loadElementPair_step s base code error aligned pc
  have b := loadElementReason_step (loadElementPair s) base
    (Codec.Linked.WordsAt.preserve code (by simp [loadElementPair, state_simp_rules]))
    (by simpa [loadElementPair, state_simp_rules] using error)
    (by simpa [loadElementPair, CheckSPAlignment, state_simp_rules] using aligned)
    (by simp [loadElementPair, state_simp_rules, pc, BitVec.add_assoc])
  have c := loadElementPayload_step (loadElementReason (loadElementPair s)) base
    (Codec.Linked.WordsAt.preserve code
      (by simp [loadElementPair, loadElementReason, state_simp_rules]))
    (by simpa [loadElementPair, loadElementReason, state_simp_rules] using error)
    (by simpa [loadElementPair, loadElementReason, CheckSPAlignment, state_simp_rules] using aligned)
    (by simp [loadElementPair, loadElementReason, state_simp_rules, pc, BitVec.add_assoc])
  have d := branchElementReason_step
    (loadElementPayload (loadElementReason (loadElementPair s))) base
    (Codec.Linked.WordsAt.preserve code
      (by simp [loadElementPair, loadElementReason, loadElementPayload, state_simp_rules]))
    (by simpa [loadElementPair, loadElementReason, loadElementPayload, state_simp_rules] using error)
    (by simp [loadElementPair, loadElementReason, loadElementPayload,
      state_simp_rules, pc, BitVec.add_assoc])
  change stepi (stepi (stepi (stepi s))) = _
  rw [a, b, c, d]
  rfl

theorem elementDispatched_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 48#64) :
    read_pc (elementDispatched s) =
      if read_mem_bytes 4 (r (.GPR 31#5) s + 216#64) s = 0#32 then
        base + 108#64 else base + 64#64 := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules, bitvec_rules, pc, BitVec.add_assoc]

@[simp] theorem elementDispatched_memory (s : ArmState) :
    (elementDispatched s).mem = s.mem := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules]

@[simp] theorem elementDispatched_program (s : ArmState) :
    (elementDispatched s).program = s.program := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules]

@[simp] theorem elementDispatched_error (s : ArmState) :
    read_err (elementDispatched s) = read_err s := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules]

@[simp] theorem elementDispatched_sp (s : ArmState) :
    r (.GPR 31#5) (elementDispatched s) = r (.GPR 31#5) s := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules]

@[simp] theorem elementDispatched_reason (s : ArmState) :
    r (.GPR 9#5) (elementDispatched s) =
      (read_mem_bytes 4 (r (.GPR 31#5) s + 216#64) s).zeroExtend 64 := by
  simp [elementDispatched, branchElementReason, loadElementPayload, loadElementReason,
    loadElementPair, state_simp_rules]

end SszArm.Indices.ChunkPosition

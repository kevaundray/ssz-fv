import SszArm.IndicesLinkedChunkPosition
import SszArm.BoolMemory
import SszArm.IndicesStorage

set_option autoImplicit false

namespace SszArm.Indices.ChunkPosition

inductive RestorePair where
  | x20x19 | x22x21 | x24x23 | x26x25 | x29x30
  deriving DecidableEq

def RestorePair.offset : RestorePair → Nat
  | .x20x19 => 572
  | .x22x21 => 576
  | .x24x23 => 580
  | .x26x25 => 584
  | .x29x30 => 588

def RestorePair.stackOffset : RestorePair → BitVec 64
  | .x20x19 => 304#64
  | .x22x21 => 288#64
  | .x24x23 => 272#64
  | .x26x25 => 256#64
  | .x29x30 => 240#64

def RestorePair.low : RestorePair → BitVec 5
  | .x20x19 => 20#5
  | .x22x21 => 22#5
  | .x24x23 => 24#5
  | .x26x25 => 26#5
  | .x29x30 => 29#5

def RestorePair.high : RestorePair → BitVec 5
  | .x20x19 => 19#5
  | .x22x21 => 21#5
  | .x24x23 => 23#5
  | .x26x25 => 25#5
  | .x29x30 => 30#5

def RestorePair.word : RestorePair → BitVec 32
  | .x20x19 => 0xa9534ff4#32
  | .x22x21 => 0xa95257f6#32
  | .x24x23 => 0xa9515ff8#32
  | .x26x25 => 0xa95067fa#32
  | .x29x30 => 0xa94f7bfd#32

def restorePair (pair : RestorePair) (s : ArmState) : ArmState :=
  w (.GPR pair.high)
    (read_mem_bytes 8 (r (.GPR 31#5) s + pair.stackOffset + 8#64) s)
    (w (.GPR pair.low)
      (read_mem_bytes 8 (r (.GPR 31#5) s + pair.stackOffset) s)
      (w .PC (read_pc s + 4#64) s))

theorem restorePair_step (pair : RestorePair) (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 pair.offset) :
    stepi s = restorePair pair s := by
  have member : (pair.offset, pair.word) ∈ Linked.ChunkPosition.chunk2 := by
    cases pair <;> decide
  have fetched := Linked.ChunkPosition.chunk2_codeAt code _ member
  cases pair <;>
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl] <;>
    simp (config := {decide := true, instances := true})
      [restorePair, RestorePair.high, RestorePair.low, RestorePair.stackOffset,
        exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem restorePair_program (pair : RestorePair) (s : ArmState) :
    (restorePair pair s).program = s.program := by
  simp [restorePair, state_simp_rules]

@[simp] theorem restorePair_error (pair : RestorePair) (s : ArmState) :
    read_err (restorePair pair s) = read_err s := by
  simp [restorePair, state_simp_rules]

@[simp] theorem restorePair_pc (pair : RestorePair) (s : ArmState) :
    read_pc (restorePair pair s) = read_pc s + 4#64 := by
  simp [restorePair, state_simp_rules]

@[simp] theorem restorePair_sp (pair : RestorePair) (s : ArmState) :
    r (.GPR 31#5) (restorePair pair s) = r (.GPR 31#5) s := by
  cases pair <;> simp [restorePair, RestorePair.high, RestorePair.low, state_simp_rules]

@[simp] theorem restorePair_aligned (pair : RestorePair) (s : ArmState) :
    CheckSPAlignment (restorePair pair s) = CheckSPAlignment s := by
  simp [CheckSPAlignment, state_simp_rules]

def restoreAll (s : ArmState) : ArmState :=
  restorePair .x29x30 (restorePair .x26x25 (restorePair .x24x23
    (restorePair .x22x21 (restorePair .x20x19 s))))

def releaseStack (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s + 320#64) (w .PC (read_pc s + 4#64) s)

def returned (s : ArmState) : ArmState :=
  w .PC (r (.GPR 30#5) (restoreAll s)) (releaseStack (restoreAll s))

theorem releaseStack_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 592#64) : stepi s = releaseStack s := by
  have fetched := Linked.ChunkPosition.chunk2_codeAt code (592, 0x910503ff#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [releaseStack, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem ret_step (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 596#64) : stepi s = w .PC (r (.GPR 30#5) s) s := by
  have fetched := Linked.ChunkPosition.chunk2_codeAt code (596, 0xd65f03c0#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

/-- The common physical continuation shared by every success and error exit. -/
theorem return_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ChunkPosition.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 572#64) :
    run 7 s = returned s := by
  have a := restorePair_step .x20x19 s base code error aligned pc
  have b := restorePair_step .x22x21 (restorePair .x20x19 s) base
    (Codec.Linked.WordsAt.preserve code (by simp)) (by simpa using error)
    (by simpa using aligned) (by simp [RestorePair.offset, pc, BitVec.add_assoc])
  have c := restorePair_step .x24x23 (restorePair .x22x21 (restorePair .x20x19 s)) base
    (Codec.Linked.WordsAt.preserve code (by simp)) (by simpa using error)
    (by simpa using aligned) (by simp [RestorePair.offset, pc, BitVec.add_assoc])
  have d := restorePair_step .x26x25
    (restorePair .x24x23 (restorePair .x22x21 (restorePair .x20x19 s))) base
    (Codec.Linked.WordsAt.preserve code (by simp)) (by simpa using error)
    (by simpa using aligned) (by simp [RestorePair.offset, pc, BitVec.add_assoc])
  have e := restorePair_step .x29x30
    (restorePair .x26x25 (restorePair .x24x23
      (restorePair .x22x21 (restorePair .x20x19 s)))) base
    (Codec.Linked.WordsAt.preserve code (by simp)) (by simpa using error)
    (by simpa using aligned) (by simp [RestorePair.offset, pc, BitVec.add_assoc])
  have f := releaseStack_step (restoreAll s) base
    (Codec.Linked.WordsAt.preserve code (by simp [restoreAll]))
    (by simpa [restoreAll] using error) (by simp [restoreAll, pc, BitVec.add_assoc])
  have g := ret_step (releaseStack (restoreAll s)) base
    (Codec.Linked.WordsAt.preserve code (by simp [releaseStack, restoreAll, state_simp_rules]))
    (by simpa [releaseStack, restoreAll, state_simp_rules] using error)
    (by simp [releaseStack, restoreAll, state_simp_rules, pc, BitVec.add_assoc])
  change stepi (stepi (stepi (stepi (stepi (stepi (stepi s)))))) = _
  rw [a, b, c, d, e]
  change stepi (stepi (restoreAll s)) = _
  rw [f, g]
  simp [returned, releaseStack, state_simp_rules]

@[simp] theorem returned_memory (s : ArmState) : (returned s).mem = s.mem := by
  simp [returned, releaseStack, restoreAll, restorePair, state_simp_rules]

@[simp] theorem returned_program (s : ArmState) : (returned s).program = s.program := by
  simp [returned, releaseStack, restoreAll, restorePair, state_simp_rules]

@[simp] theorem returned_error (s : ArmState) : read_err (returned s) = read_err s := by
  simp [returned, releaseStack, restoreAll, restorePair, state_simp_rules]

@[simp] theorem returned_pc (s : ArmState) :
    read_pc (returned s) = read_mem_bytes 8 (r (.GPR 31#5) s + 248#64) s := by
  simp [returned, releaseStack, restoreAll, restorePair, RestorePair.high,
    RestorePair.low, RestorePair.stackOffset, state_simp_rules, BitVec.add_assoc]

@[simp] theorem returned_sp (s : ArmState) :
    r (.GPR 31#5) (returned s) = r (.GPR 31#5) s + 320#64 := by
  simp [returned, releaseStack, restoreAll, state_simp_rules]

@[simp] theorem returned_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (returned s) = r (.SFP reg) s := by
  simp [returned, releaseStack, restoreAll, restorePair, state_simp_rules]

end SszArm.Indices.ChunkPosition

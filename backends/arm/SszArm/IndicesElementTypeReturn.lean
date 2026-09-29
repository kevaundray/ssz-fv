import SszArm.IndicesLinkedElementType
import SszArm.BoolMemory

set_option autoImplicit false

namespace SszArm.Indices.ElementType

inductive ReturnSite where
  | boolean | byte | sequence | notSteppable | field | noSuchField
  deriving DecidableEq

def ReturnSite.offset : ReturnSite → Nat
  | .boolean => 136
  | .byte => 244
  | .sequence => 364
  | .notSteppable => 604
  | .field => 792
  | .noSuchField => 972

/-- All six exits restore the actual saved LR/x19 pair and then execute RET. -/
def restored (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
    (w (.GPR 19#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s)
      (w (.GPR 30#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s)
        (w .PC (read_pc s + 4#64) s)))

def returned (s : ArmState) : ArmState :=
  w .PC (read_mem_bytes 8 (r (.GPR 31#5) s) s) (restored s)

private theorem restore_fetch (site : ReturnSite) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) :
    s.program.find? (base + BitVec.ofNat 64 site.offset) = some 0xa8c14ffe#32 := by
  cases site
  · exact Linked.ElementType.chunk0_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk0_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk1_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk2_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk3_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk3_codeAt code _ (by decide)

private theorem ret_fetch (site : ReturnSite) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) :
    s.program.find? (base + BitVec.ofNat 64 (site.offset + 4)) = some 0xd65f03c0#32 := by
  cases site
  · exact Linked.ElementType.chunk0_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk0_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk1_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk2_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk3_codeAt code _ (by decide)
  · exact Linked.ElementType.chunk3_codeAt code _ (by decide)

theorem restore_step (site : ReturnSite) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = restored s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans (restore_fetch site s base code)) rfl]
  simp (config := {decide := true, instances := true})
    [restored, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem return_step (site : ReturnSite) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.offset + 4)) :
    stepi s = w .PC (r (.GPR 30#5) s) s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans (ret_fetch site s base code)) rfl]
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem return_run (site : ReturnSite) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    run 2 s = returned s := by
  have first := restore_step site s base code error aligned pc
  have second := return_step site (restored s) base
    (Codec.Linked.WordsAt.preserve code (by simp [restored, state_simp_rules]))
    (by simpa [restored, state_simp_rules] using error)
    (by simp [restored, state_simp_rules, pc, BitVec.ofNat_add, BitVec.add_assoc])
  change stepi (stepi s) = returned s
  rw [first, second]
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_pc (s : ArmState) :
    read_pc (returned s) = read_mem_bytes 8 (r (.GPR 31#5) s) s := by
  simp [returned, state_simp_rules]

@[simp] theorem returned_sp (s : ArmState) :
    r (.GPR 31#5) (returned s) = r (.GPR 31#5) s + 16#64 := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_x19 (s : ArmState) :
    r (.GPR 19#5) (returned s) = read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_lr (s : ArmState) :
    r (.GPR 30#5) (returned s) = read_mem_bytes 8 (r (.GPR 31#5) s) s := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_memory (s : ArmState) : (returned s).mem = s.mem := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_program (s : ArmState) : (returned s).program = s.program := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_error (s : ArmState) : read_err (returned s) = read_err s := by
  simp [returned, restored, state_simp_rules]

@[simp] theorem returned_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (returned s) = r (.SFP reg) s := by
  simp [returned, restored, state_simp_rules]

theorem returned_register (s : ArmState) (reg : BitVec 5)
    (notSP : reg ≠ 31#5) (notSaved : reg ≠ 19#5) (notLR : reg ≠ 30#5) :
    r (.GPR reg) (returned s) = r (.GPR reg) s := by
  simp [returned, restored, state_simp_rules, notSP, notSaved, notLR]

end SszArm.Indices.ElementType

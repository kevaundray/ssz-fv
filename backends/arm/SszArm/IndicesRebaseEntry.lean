import SszArm.IndicesLinkedRebase
import SszArm.Udivti3Arithmetic

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Entry

/-- AND X8,X4,X5 is the original entry's checked-u128-increment guard. -/
def mask (s : ArmState) : ArmState :=
  w (.GPR 8#5) (r (.GPR 4#5) s &&& r (.GPR 5#5) s)
    (w .PC (read_pc s + 4#64) s)

/-- CMN X8,#1 preserves the actual PSTATE used by the following B.EQ. -/
def compare (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry (r (.GPR 8#5) s) 1#64 0#1).2
    (w .PC (read_pc s + 4#64) s)

def select (s : ArmState) : ArmState :=
  w .PC (if r (.FLAG .Z) s = 1#1 then read_pc s + 96#64 else read_pc s + 4#64) s

def prefix (s : ArmState) : ArmState := select (compare (mask s))

theorem mask_step (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base) : stepi s = mask s := by
  have fetched := Linked.Rebase.chunk0_codeAt code (0, 0x8a050088#32) (by decide)
  simp only [BitVec.add_zero] at fetched
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [mask, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem compare_step (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base + 4#64) : stepi s = compare s := by
  have fetched := Linked.Rebase.chunk0_codeAt code (4, 0xb100051f#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [compare, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem select_step (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base + 8#64) : stepi s = select s := by
  have fetched := Linked.Rebase.chunk0_codeAt code (8, 0x54000300#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [select, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

/-- Actual original-entry execution of the first checked-add guard. No later
helper execution, result, ownership, or frame is assumed in this theorem. -/
theorem original_entry (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base) : run 3 s = prefix s := by
  have maskCode : Linked.Rebase.CodeAt (mask s) base := by
    simpa only [Linked.Rebase.CodeAt, Codec.Linked.WordsAt, mask, state_simp_rules] using code
  have maskError : read_err (mask s) = .None := by
    simpa [mask, state_simp_rules] using error
  have maskPC : read_pc (mask s) = base + 4#64 := by
    simp [mask, state_simp_rules, entry]
  have compareCode : Linked.Rebase.CodeAt (compare (mask s)) base := by
    simpa only [Linked.Rebase.CodeAt, Codec.Linked.WordsAt, compare, mask, state_simp_rules] using code
  have compareError : read_err (compare (mask s)) = .None := by
    simpa [compare, mask, state_simp_rules] using error
  have comparePC : read_pc (compare (mask s)) = base + 8#64 := by
    simp [compare, mask, state_simp_rules, entry, BitVec.add_assoc]
  change run 2 (stepi s) = _
  rw [mask_step s base code error entry]
  change run 1 (stepi (mask s)) = _
  rw [compare_step _ base maskCode maskError maskPC]
  change stepi (compare (mask s)) = _
  exact select_step _ base compareCode compareError comparePC

theorem prefix_pc (s : ArmState) (base : BitVec 64) (entry : read_pc s = base) :
    read_pc (prefix s) =
      if (AddWithCarry (r (.GPR 4#5) s &&& r (.GPR 5#5) s) 1#64 0#1).2.z = 1#1 then
        base + 104#64 else base + 12#64 := by
  simp [prefix, select, compare, mask, state_simp_rules, entry, BitVec.add_assoc]

theorem prefix_frame (s : ArmState) :
    (prefix s).program = s.program ∧ read_err (prefix s) = read_err s ∧
    (prefix s).mem = s.mem ∧
    (∀ reg : BitVec 5, reg ≠ 8#5 → r (.GPR reg) (prefix s) = r (.GPR reg) s) ∧
    (∀ reg : BitVec 5, r (.SFP reg) (prefix s) = r (.SFP reg) s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [prefix, select, compare, mask, state_simp_rules]
  · simp [prefix, select, compare, mask, state_simp_rules]
  · simp [prefix, select, compare, mask, state_simp_rules]
  · intro reg different
    simp [prefix, select, compare, mask, state_simp_rules, different]
  · intro reg
    simp [prefix, select, compare, mask, state_simp_rules]

end SszArm.Indices.Rebase.Entry

import Arm.Exec

namespace SszArm.Codec.Linked

/-- Every listed word is fetched from the actual LNSym program map. -/
def WordsAt (program : List (Nat × BitVec 32)) (s : ArmState)
    (base : BitVec 64) : Prop :=
  ∀ row ∈ program, s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2

/-- A decoded instruction is executed by LNSym itself; there is no call oracle
or fallback instruction in this interface. -/
theorem step_word (s : ArmState) (base : BitVec 64)
    (program : List (Nat × BitVec 32)) (pc : Nat) (word : BitVec 32)
    (inst : ArmInst) (code : WordsAt program s base)
    (member : (pc, word) ∈ program) (error : read_err s = .None)
    (entry : read_pc s = base + BitVec.ofNat 64 pc)
    (decoded : decode_raw_inst word = some inst) :
    stepi s = exec_inst inst s := by
  exact stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans (code (pc, word) member)) decoded

theorem WordsAt.append {left right : List (Nat × BitVec 32)}
    {s : ArmState} {base : BitVec 64} :
    WordsAt (left ++ right) s base ↔ WordsAt left s base ∧ WordsAt right s base := by
  simp only [WordsAt, List.mem_append, forall_and, or_imp]

/-- Program equality transports bindings without any assumptions about execution. -/
theorem WordsAt.preserve {program : List (Nat × BitVec 32)}
    {s t : ArmState} {base : BitVec 64} (code : WordsAt program s base)
    (same : t.program = s.program) : WordsAt program t base := by
  intro row member
  rw [same]
  exact code row member

end SszArm.Codec.Linked

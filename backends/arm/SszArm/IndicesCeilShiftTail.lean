import SszArm.IndicesLinkedCeilShift
import SszArm.IndicesLinkedBranches
import SszArm.IndicesNatShrClzWord

set_option autoImplicit false

namespace SszArm.Indices.CeilShift.Tail

/-- The original tail block, not a synthetic callable helper. -/
def lowShift (s : ArmState) : ArmState :=
  w (.GPR 4#5) (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (r (.GPR 3#5) s)))
    (w .PC (read_pc s + 4#64) s)

def highShift (s : ArmState) : ArmState :=
  w (.GPR 5#5) 0#64 (w .PC (read_pc s + 4#64) s)

def target (s : ArmState) (bias : BitVec 64) : ArmState :=
  w .PC (bias + 2265780#64) (highShift (lowShift s))

theorem low_step (s : ArmState) (base : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base + 264#64) : stepi s = lowShift s := by
  have fetched := Linked.CeilShift.chunk1_codeAt code (264, 0x2a0303e4#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [lowShift, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem high_step (s : ArmState) (base : BitVec 64)
    (code : Linked.CeilShift.CodeAt s base) (error : read_err s = .None)
    (entry : read_pc s = base + 268#64) : stepi s = highShift s := by
  have fetched := Linked.CeilShift.chunk1_codeAt code (268, 0xaa1f03e5#32) (by decide)
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [highShift, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

/-- The certified B leaves LR untouched: Nat::shr returns directly to the
original ceil_shift caller. No execution of Nat::shr is assumed here. -/
theorem run_tail (s : ArmState) (bias : BitVec 64)
    (code : Linked.CeilShift.CodeAt s (bias + 2263988#64))
    (error : read_err s = .None) (entry : read_pc s = bias + 2264252#64) :
    run 3 s = target s bias := by
  have lowCode : Linked.CeilShift.CodeAt (lowShift s) (bias + 2263988#64) := by
    simpa only [Linked.CeilShift.CodeAt, Codec.Linked.WordsAt, lowShift, state_simp_rules] using code
  have lowError : read_err (lowShift s) = .None := by
    simpa [lowShift, state_simp_rules] using error
  have lowPC : read_pc (lowShift s) = (bias + 2263988#64) + 268#64 := by
    simp [lowShift, state_simp_rules, entry, BitVec.add_assoc]
  have highCode : Linked.CeilShift.CodeAt (highShift (lowShift s)) (bias + 2263988#64) := by
    simpa only [Linked.CeilShift.CodeAt, Codec.Linked.WordsAt, highShift, state_simp_rules] using lowCode
  have highError : read_err (highShift (lowShift s)) = .None := by
    simpa [highShift, state_simp_rules] using lowError
  have highPC : read_pc (highShift (lowShift s)) = bias + 2264260#64 := by
    simp [highShift, lowShift, state_simp_rules, entry, BitVec.add_assoc]
  have fetched := Linked.CeilShift.chunk1_codeAt highCode (272, 0x1400017c#32) (by decide)
  simp only [BitVec.add_assoc] at fetched
  change run 2 (stepi s) = _
  rw [low_step s _ code error (by simpa only [BitVec.add_assoc] using entry)]
  change run 1 (stepi (lowShift s)) = _
  rw [high_step _ _ lowCode lowError lowPC]
  change stepi (highShift (lowShift s)) = _
  exact Linked.Branches.ceil_shift_p272 _ bias highError highPC fetched

theorem target_frame (s : ArmState) (bias : BitVec 64) :
    (target s bias).program = s.program ∧ read_err (target s bias) = read_err s ∧
    (target s bias).mem = s.mem ∧
    (∀ reg : BitVec 5, reg ≠ 4#5 → reg ≠ 5#5 →
      r (.GPR reg) (target s bias) = r (.GPR reg) s) ∧
    (∀ reg : BitVec 5, r (.SFP reg) (target s bias) = r (.SFP reg) s) ∧
    (∀ flag, r (.FLAG flag) (target s bias) = r (.FLAG flag) s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [target, highShift, lowShift, state_simp_rules]
  · simp [target, highShift, lowShift, state_simp_rules]
  · simp [target, highShift, lowShift, state_simp_rules]
  · intro reg notLow notHigh
    simp [target, highShift, lowShift, state_simp_rules, notLow, notHigh]
  · intro reg
    simp [target, highShift, lowShift, state_simp_rules]
  · intro flag
    simp [target, highShift, lowShift, state_simp_rules]

theorem target_arguments (s : ArmState) (bias : BitVec 64) :
    read_pc (target s bias) = bias + 2265780#64 ∧
    r (.GPR 4#5) (target s bias) =
      BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (r (.GPR 3#5) s)) ∧
    r (.GPR 5#5) (target s bias) = 0#64 ∧
    r (.GPR 6#5) (target s bias) = r (.GPR 6#5) s ∧
    r (.GPR 30#5) (target s bias) = r (.GPR 30#5) s := by
  simp [target, highShift, lowShift, state_simp_rules]

end SszArm.Indices.CeilShift.Tail

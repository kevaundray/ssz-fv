import SszArm.MeasureScalarVectorReady
import SszArm.MeasureScalarTransition
import SszArm.Memcmp

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)
open SszNative.Serialize (Value)

@[irreducible] def wrongReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3924#64)
    (write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~2#32) 1#1).2 s)

private theorem wrong_tag_zero (tag : BitVec 32) (different : tag ≠ 2#32) :
    (AddWithCarry tag (~~~2#32) 1#1).2.z = 0#1 := by
  have equality := Memcmp.sub_equal tag 2#32
  have bounded := (AddWithCarry tag (~~~2#32) 1#1).2.z.isLt
  have notOne : (AddWithCarry tag (~~~2#32) 1#1).2.z ≠ 1#1 :=
    fun same => different (equality.mp same)
  bv_omega

private def wrongCompareOp : Kind → Op
  | .vector => p1156 | .list => p776

private def wrongBranchOp : Kind → Op
  | .vector => p1160 | .list => p780

private theorem wrong_compare_effect (kind : Kind) (s : ArmState) :
    (wrongCompareOp kind).effect s = write_pstate
      (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~2#32) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  cases kind <;>
    change exec_inst (.DPI (.Add_sub_imm
      { sf := 0, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 8, Rd := 31 })) s = _
  all_goals simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem wrong_branch_effect (kind : Kind) (s : ArmState) (zero : r (.FLAG .Z) s = 0#1) :
    (wrongBranchOp kind).effect s = w .PC
      (r .PC s + BitVec.ofNat 64 (match kind with | .vector => 2764 | .list => 3144)) s := by
  cases kind with
  | vector =>
    change exec_inst (.BR (.Cond_branch_imm { imm19 := 691, o0 := 0, cond := 1 })) s = _
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]
  | list =>
    change exec_inst (.BR (.Cond_branch_imm { imm19 := 786, o0 := 0, cond := 1 })) s = _
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

private theorem wrong_flags_pc (s : ArmState) (flags : PState) (pc : BitVec 64) :
    write_pstate flags (w .PC pc s) = w .PC pc (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

@[irreducible] private def wrongCompared (kind : Kind) (s : ArmState) (base : BitVec 64)
    (flags : PState) : ArmState :=
  w .PC (base + BitVec.ofNat 64 kind.entry + 4#64) (write_pstate flags s)

private theorem wrong_compared_step (kind : Kind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    (wrongCompareOp kind).effect s = wrongCompared kind s base
      (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~2#32) 1#1).2 := by
  change r .PC s = _ at pc
  rw [wrong_compare_effect, wrong_flags_pc, pc]
  simp only [wrongCompared]

private theorem wrong_compared_error (kind : Kind) (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_err (wrongCompared kind s base flags) = read_err s := by
  simp [wrongCompared, state_simp_rules]

private theorem wrong_compared_pc (kind : Kind) (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_pc (wrongCompared kind s base flags) = base + BitVec.ofNat 64 (wrongBranchOp kind).offset := by
  cases kind <;> simp [wrongCompared, wrongBranchOp, Kind.entry, p1160, p780, state_simp_rules, BitVec.add_assoc]

private theorem wrong_branched_step (kind : Kind) (s : ArmState) (base : BitVec 64)
    (flags : PState) (zero : flags.z = 0#1) :
    (wrongBranchOp kind).effect (wrongCompared kind s base flags) =
      w .PC (base + 3924#64) (write_pstate flags s) := by
  have zeroState : r (.FLAG .Z) (wrongCompared kind s base flags) = 0#1 := by
    simpa [wrongCompared, state_simp_rules] using zero
  rw [wrong_branch_effect kind _ zeroState]
  have pc : r .PC (wrongCompared kind s base flags) = base + BitVec.ofNat 64 kind.entry + 4#64 := by
    simp only [wrongCompared, r_of_w_same]
  rw [pc]
  cases kind <;> simp [Kind.entry, BitVec.add_assoc, wrongCompared, w_of_w_shadow]

private theorem wrong_two_effects (first second : Op) (s t u : ArmState)
    (hfirst : first.effect s = t) (hsecond : second.effect t = u) : effect [first, second] s = u := by
  change second.effect (first.effect s) = u
  exact (congrArg second.effect hfirst).trans hsecond


theorem wrong_entry_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 ≠ 2#32) : run 2 s = wrongReady s base := by
  let flags := (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~2#32) 1#1).2
  have zero : flags.z = 0#1 := wrong_tag_zero _ tag
  have first : (wrongCompareOp kind).effect s = wrongCompared kind s base flags :=
    wrong_compared_step kind s base pc
  have follows : Follows base [wrongCompareOp kind, wrongBranchOp kind] s := by
    refine ⟨error, ?_, ?_, ?_, trivial⟩
    · cases kind <;> simpa [wrongCompareOp, Kind.entry, p1156, p776] using pc
    · rw [first]; exact (wrong_compared_error kind s base flags).trans error
    · rw [first]; exact wrong_compared_pc kind s base flags
  rw [show 2 = [wrongCompareOp kind, wrongBranchOp kind].length by rfl,
    runs _ s base code follows]
  have complete := wrong_two_effects (wrongCompareOp kind) (wrongBranchOp kind) s
    (wrongCompared kind s base flags) (w .PC (base + 3924#64) (write_pstate flags s))
    first (wrong_branched_step kind s base flags zero)
  simpa only [wrongReady] using complete


theorem wrong_entry_body (kind : Kind) (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (value : Value)
    (owned : Owned s args (kind.desc cap) value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 ≠ 2#32)
    (semantic : outcome s args (kind.desc cap) value =
      SszNative.Serialize.unchanged (arenaOf s args).used (.error .wrongType)) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (kind.desc cap) value base := by
  let u := wrongReady s base
  have hu : run 2 s = u := wrong_entry_run kind s base code error pc tag
  have up : u.program = s.program := by simp [u, wrongReady, state_simp_rules]
  have ue : read_err u = .None := by simpa [u, wrongReady, state_simp_rules] using error
  have ua : CheckSPAlignment u := by
    simpa [u, wrongReady, CheckSPAlignment, state_simp_rules] using aligned
  have uo : r (.GPR 19#5) u = args.result := by
    simpa [u, wrongReady, state_simp_rules] using registers.result
  have us : r (.GPR 31#5) u = args.bodySP := by
    simpa [u, wrongReady, state_simp_rules] using registers.stack
  have own : Owned u args (kind.desc cap) value := owned.of_local_frame (by
    intro address outside; simp [u, wrongReady, state_simp_rules])
  have measured : outcome u args (kind.desc cap) value =
      SszNative.Serialize.unchanged (arenaOf u args).used (.error .wrongType) := by
    simpa [u, wrongReady, outcome, arenaOf, state_simp_rules] using semantic
  have post := Result.wrong_produced base own uo us
    (by rw [measured]; rfl) (by rw [measured]; rfl) (by rw [measured]; rfl) ue
  refine ⟨50, Result.wrongResult u base, ?_, Scalar.prepend_pure post up ?_ ?_ ?_⟩
  · rw [show 50 = 2 + 48 by decide, run_plus, hu]
    exact Result.wrong_run u base (code.congr up) ue ua
      (by simp [u, wrongReady, state_simp_rules])
  · simp [u, wrongReady, state_simp_rules]
  · intro reg member; simp [u, wrongReady, state_simp_rules]
  · intro reg low high; simp [u, wrongReady, state_simp_rules]

end SszArm.Measure.Scalar.Bytes

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem byteVector_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (value : Value)
    (owned : Owned s args (.byteVector cap) value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1156#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.byteVector cap) value base := by
  cases value with
  | bytes bytes =>
    exact Scalar.Bytes.vector_bytes_body s base args cap bytes owned registers code error aligned pc
      descriptor (by simp [tag, Emit.valueTag])
  | bool flag | uint flag | bits flag | seq flag =>
    exact Scalar.Bytes.wrong_entry_body .vector s base args cap _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)
  | union selector content =>
    exact Scalar.Bytes.wrong_entry_body .vector s base args cap _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)

end SszArm.Measure

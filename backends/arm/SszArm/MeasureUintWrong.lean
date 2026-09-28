import SszArm.MeasureUintProduced

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem compare32_zero (left right : BitVec 32) :
    (AddWithCarry left (~~~right) 1#1).2.z = 1#1 ↔ left = right := by
  have difference : (AddWithCarry left (~~~right) 1#1).1 = left - right := by
    simp only [fst_AddWithCarry_eq_sub_neg, BitVec.not_not]
  change (if (AddWithCarry left (~~~right) 1#1).1 = 0#32 then 1#1 else 0#1) = 1#1 ↔ _
  rw [difference]
  by_cases same : left = right
  · simp [same]
  · have nonzero : left - right ≠ 0#32 := by bv_omega
    simp [same, nonzero]

def valueCheckOps : List ValueOp := [.p348, .p352]

theorem value_check (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 348#64) :
    let t := valueBlock base valueCheckOps s
    run 2 s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = if (r (.GPR 8#5) s).setWidth 32 = 1#32
        then base + 356#64 else base + 3924#64 := by
  have pc' : r .PC s = base + 348#64 := pc
  have follows : ValueFollows base valueCheckOps s := by
    simp [valueCheckOps, ValueFollows, ValueOp.row, ValueOp.effect, compare32,
      Emit.Dispatch.compare32, Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  refine ⟨value_run base valueCheckOps s code error aligned follows,
    value_pure_frame base _ s (by decide), ?_⟩
  have zero : (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) 4294967294#32 1#1).2.z = 1#1 ↔
      (r (.GPR 8#5) s).setWidth 32 = 1#32 :=
    compare32_zero ((r (.GPR 8#5) s).setWidth 32) 1#32
  simp [valueCheckOps, valueBlock, ValueOp.effect, compare32, next,
    Emit.Dispatch.compare32, Emit.Dispatch.next, state_simp_rules, zero]

/-- Wrong Value constructors traverse the original tag test and the complete
wrong-type writer. No arena validity or successful expected-size premise. -/
theorem wrong_type_body (s : ArmState) (args : Args) (uintCap : NatOperand) (value : Value)
    (base : BitVec 64) (owned : Owned s args (.uint uintCap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 348#64) (registers : BodyRegisters s args)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64)
    (notUint : ∀ number, value ≠ .uint number) :
    ∃ t, run 50 s = t ∧ Produced s t args (.uint uintCap) value base := by
  have wrongTag : (r (.GPR 8#5) s).setWidth 32 ≠ 1#32 := by
    rw [tag]
    cases value with
    | uint number => exact False.elim (notUint number rfl)
    | bool flag => simp only [Emit.valueTag]; decide
    | bytes bytes => simp only [Emit.valueTag]; decide
    | bits bits => simp only [Emit.valueTag]; decide
    | seq values => simp only [Emit.valueTag]; decide
    | union index value => simp only [Emit.valueTag]; decide
  have measured : outcome s args (.uint uintCap) value =
      SszNative.Serialize.unchanged (arenaOf s args).used (.error .wrongType) := by
    cases value with
    | uint number => exact False.elim (notUint number rfl)
    | bool flag => rfl
    | bytes bytes => rfl
    | bits bits => rfl
    | seq values => rfl
    | union index value => rfl
  let u := valueBlock base valueCheckOps s
  obtain ⟨executed, frame, nextPC⟩ := value_check s base code error aligned pc
  have localFrame := scan_local_frame owned registers.stack frame
  have nextOwned := owned.of_local_frame localFrame
  have sameArena := arenaOf_eq_of_local_frame owned localFrame
  have sameOutcome : outcome u args (.uint uintCap) value = outcome s args (.uint uintCap) value :=
    outcome_eq_of_arena_eq sameArena
  have nextError : read_err u = .None := frame.error.trans error
  have nextResult : r (.GPR 19#5) u = args.result :=
    (frame.registers 19#5 (by decide)).trans registers.result
  have nextStack : r (.GPR 31#5) u = args.bodySP := frame.sp.trans registers.stack
  let t := Result.wrongResult u base
  have writerRun : run 48 u = t := Result.wrong_run u base (code.congr frame.program)
    nextError (frame.aligned aligned) (by simpa [wrongTag] using nextPC)
  have after : Produced u t args (.uint uintCap) value base := Result.wrong_produced base
    nextOwned nextResult nextStack
    (by simp [sameOutcome, measured, SszNative.Serialize.unchanged])
    (by simp [sameOutcome, measured, SszNative.Serialize.unchanged])
    (by
      simp only [sameOutcome, measured, SszNative.Serialize.unchanged]
      rw [show arenaOf u args = arenaOf s args from sameArena]) nextError
  refine ⟨t, ?_, produced_prepend_scan owned registers.stack frame after⟩
  rw [show 50 = 2 + 48 by decide, run_plus, executed, writerRun]

end SszArm.Measure.Uint

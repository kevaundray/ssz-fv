import SszArm.MeasureUintNumber
import SszArm.MeasureUintHeader
import SszArm.MeasureUintWrong

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem width_body_owned {s : ArmState} {args : Args} {uintCap number : NatOperand}
    (owned : Owned s args (.uint uintCap) (.uint number)) :
    NatDivision.OperandOwned (bodyWrites args (outcome s args (.uint uintCap) (.uint number))) uintCap := by
  have borrowed := owned.operandOwned uintCap (by simp [Emit.descriptorOperands, Emit.valueOperands])
  cases uintCap with
  | small limbWord => trivial
  | large pointer words =>
    rcases borrowed with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (bodyWrites_subset _ _ span member))

/-- Matching Uint Value, including uintFits rejection, reaches the real common
epilogue after writing either the ORIGINAL width Nat or the full WrongType. -/
theorem number_body (s : ArmState) (args : Args) (uintCap number : NatOperand)
    (base : BitVec 64) (owned : Owned s args (.uint uintCap) (.uint number))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 356#64) (registers : BodyRegisters s args)
    (descriptor : r (.GPR 1#5) s = args.descriptor) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.uint uintCap) (.uint number) base := by
  obtain ⟨numberFuel, v, numberRun, numberFrame, numberPC, required⟩ :=
    number_required s args uintCap number base owned code error aligned pc registers
  have ownedV := owned.of_local_frame (scan_local_frame owned registers.stack numberFrame)
  have stackV : r (.GPR 31#5) v = args.bodySP := numberFrame.sp.trans registers.stack
  have outputV : r (.GPR 19#5) v = args.result :=
    (numberFrame.registers 19#5 (by decide)).trans registers.result
  have descriptorV : r (.GPR 1#5) v = args.descriptor :=
    (numberFrame.registers 1#5 (by decide)).trans descriptor
  let u := widthHeader v base
  have headerRun : run 1 v = u := width_header_run v base (code.congr numberFrame.program)
    (numberFrame.error.trans error) (numberFrame.aligned aligned) numberPC
  have ownedU : Owned u args (.uint uintCap) (.uint number) := width_header_owned ownedV base
  have programU : u.program = s.program := (width_header_program v base).trans numberFrame.program
  have errorU : read_err u = .None := (width_header_error v base).trans (numberFrame.error.trans error)
  have alignedU : CheckSPAlignment u := WidthOp.aligned .p2736 base v (numberFrame.aligned aligned)
  have stackU : r (.GPR 31#5) u = args.bodySP :=
    (width_header_register v base 31#5 (by decide) (by decide)).trans stackV
  have outputU : r (.GPR 19#5) u = args.result :=
    (width_header_register v base 19#5 (by decide) (by decide)).trans outputV
  obtain ⟨pointerU, payloadU⟩ := width_header_pair ownedV base descriptorV
  have pcU : read_pc u = base + 2740#64 := by
    have numberPC' : r .PC v = base + 2736#64 := numberPC
    simp [u, widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, numberPC', BitVec.add_assoc]
  have requiredU : pairValue (r (.GPR 8#5) u) (r (.GPR 9#5) u) =
      SszNative.Serialize.requiredBytes number.value := by
    simpa [u, width_header_register v base 8#5 (by decide) (by decide),
      width_header_register v base 9#5 (by decide) (by decide)] using required
  obtain ⟨selectFuel, w, selectRun, selectFrame, selectPC⟩ := width_select u args uintCap number base
    ownedU (code.congr programU) errorU alignedU pcU stackU pointerU payloadU requiredU
  have ownedW := ownedU.of_local_frame (scan_local_frame ownedU stackU selectFrame)
  have stackW : r (.GPR 31#5) w = args.bodySP := selectFrame.sp.trans stackU
  have outputW : r (.GPR 19#5) w = args.result :=
    (selectFrame.registers 19#5 (by decide)).trans outputU
  have programW : w.program = s.program := selectFrame.program.trans programU
  have errorW : read_err w = .None := selectFrame.error.trans errorU
  have alignedW : CheckSPAlignment w := selectFrame.aligned alignedU
  have noCalls : (outcome w args (.uint uintCap) (.uint number)).calls = [] := by
    by_cases fits : SszNative.Serialize.uintFits uintCap number <;>
      simp [outcome, SszNative.Serialize.measure, SszNative.Serialize.unchanged, fits]
  have used : (outcome w args (.uint uintCap) (.uint number)).used = (arenaOf w args).used := by
    by_cases fits : SszNative.Serialize.uintFits uintCap number <;>
      simp [outcome, SszNative.Serialize.measure, SszNative.Serialize.unchanged, fits]
  by_cases fits : SszNative.Serialize.uintFits uintCap number
  · let t := Result.successResult w base
    have writerRun : run 33 w = t := Result.success_run w base (code.congr programW)
      errorW alignedW (by simpa [fits] using selectPC)
    have success : (outcome w args (.uint uintCap) (.uint number)).result = .ok uintCap := by
      simp [outcome, SszNative.Serialize.measure, SszNative.Serialize.unchanged, fits]
    have after : Produced w t args (.uint uintCap) (.uint number) base :=
      Result.success_produced base ownedW outputW stackW uintCap success noCalls used
        ((selectFrame.registers 21#5 (by decide)).trans pointerU)
        ((selectFrame.registers 20#5 (by decide)).trans payloadU)
        (ownedW.operand_at uintCap (by simp [Emit.descriptorOperands, Emit.valueOperands]))
        (width_body_owned ownedW) errorW
    have headerProduced := produced_prepend_scan ownedU stackU selectFrame after
    have beforeHeader : Produced v t args (.uint uintCap) (.uint number) base :=
      produced_prepend_header headerProduced
    refine ⟨numberFuel + 1 + selectFuel + 33, t, ?_,
      produced_prepend_scan owned registers.stack numberFrame beforeHeader⟩
    rw [run_plus, run_plus, run_plus, numberRun, headerRun, selectRun, writerRun]
  · let t := Result.wrongResult w base
    have writerRun : run 48 w = t := Result.wrong_run w base (code.congr programW)
      errorW alignedW (by simpa [fits] using selectPC)
    have wrong : (outcome w args (.uint uintCap) (.uint number)).result = .error .wrongType := by
      simp [outcome, SszNative.Serialize.measure, SszNative.Serialize.unchanged, fits]
    have after : Produced w t args (.uint uintCap) (.uint number) base :=
      Result.wrong_produced base ownedW outputW stackW wrong noCalls used errorW
    have headerProduced := produced_prepend_scan ownedU stackU selectFrame after
    have beforeHeader : Produced v t args (.uint uintCap) (.uint number) base :=
      produced_prepend_header headerProduced
    refine ⟨numberFuel + 1 + selectFuel + 48, t, ?_,
      produced_prepend_scan owned registers.stack numberFrame beforeHeader⟩
    rw [run_plus, run_plus, run_plus, numberRun, headerRun, selectRun, writerRun]

/-- Complete Uint leaf at its original routed entry, for every Value constructor
and every Small/Large representation. There is no expectedSize-success premise. -/
theorem uint_body (s : ArmState) (args : Args) (uintCap : NatOperand) (value : Value)
    (base : BitVec 64) (owned : Owned s args (.uint uintCap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 348#64) (registers : BodyRegisters s args)
    (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.uint uintCap) value base := by
  cases value with
  | uint number =>
    let u := valueBlock base valueCheckOps s
    obtain ⟨executed, frame, nextPC⟩ := value_check s base code error aligned pc
    have nextOwned := owned.of_local_frame (scan_local_frame owned registers.stack frame)
    have nextRegisters : BodyRegisters u args :=
      ⟨(frame.registers 19#5 (by decide)).trans registers.result,
       (frame.registers 20#5 (by decide)).trans registers.arena,
       (frame.registers 21#5 (by decide)).trans registers.value,
       frame.sp.trans registers.stack⟩
    have nextDescriptor : r (.GPR 1#5) u = args.descriptor :=
      (frame.registers 1#5 (by decide)).trans descriptor
    obtain ⟨fuel, t, bodyRun, produced⟩ := number_body u args uintCap number base nextOwned
      (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
      (by simpa [tag, Emit.valueTag] using nextPC) nextRegisters nextDescriptor
    refine ⟨2 + fuel, t, ?_, produced_prepend_scan owned registers.stack frame produced⟩
    rw [run_plus, executed, bodyRun]
  | bool flag =>
    obtain ⟨t, executed, produced⟩ := wrong_type_body s args uintCap (.bool flag) base owned
      code error aligned pc registers tag (by intro number; simp)
    exact ⟨50, t, executed, produced⟩
  | bytes bytes =>
    obtain ⟨t, executed, produced⟩ := wrong_type_body s args uintCap (.bytes bytes) base owned
      code error aligned pc registers tag (by intro number; simp)
    exact ⟨50, t, executed, produced⟩
  | bits bits =>
    obtain ⟨t, executed, produced⟩ := wrong_type_body s args uintCap (.bits bits) base owned
      code error aligned pc registers tag (by intro number; simp)
    exact ⟨50, t, executed, produced⟩
  | seq values =>
    obtain ⟨t, executed, produced⟩ := wrong_type_body s args uintCap (.seq values) base owned
      code error aligned pc registers tag (by intro number; simp)
    exact ⟨50, t, executed, produced⟩
  | union index value =>
    obtain ⟨t, executed, produced⟩ := wrong_type_body s args uintCap (.union index value) base owned
      code error aligned pc registers tag (by intro number; simp)
    exact ⟨50, t, executed, produced⟩

end SszArm.Measure.Uint

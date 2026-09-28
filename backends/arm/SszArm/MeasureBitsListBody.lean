import SszArm.MeasureBitsListCountBody
import SszArm.MeasureBitsListEntry
import SszArm.MeasureResultProduced

namespace SszArm.Measure.Bits.List

open SszNative.Serialize (Packed Value)

theorem bits_executes (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.entry)
    (registers : BodyRegisters s args) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag (.bits bits)).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  have tagBits : (r (.GPR 8#5) s).setWidth 32 = 3#32 := by rw [tag]; rfl
  have firstRun := entry_executes schema s base code error pc tagBits
  have sp := entered_register schema s base 31#5 (by decide)
  have uAligned : CheckSPAlignment (entered schema s base) := by
    simpa only [CheckSPAlignment, state_simp_rules, sp] using aligned
  obtain ⟨fuel, t, restRun, post⟩ := count_executes schema (entered schema s base) args bits base
    (entered_owned schema s args bits base owned) (code.congr (entered_program schema s base))
    ((entered_error schema s base).trans error) uAligned
    (entered_work schema s args bits base owned registers descriptor)
    (entered_pc schema s args bits base owned registers)
  refine ⟨2 + (ListEntry.loadOps schema.kind).length + fuel, t,
    by rw [run_plus, firstRun, restRun], ?_⟩
  apply post.prepend_stack owned (fun address _ => congrFun (entered_memory schema s base) address)
    (entered_program schema s base)
  · intro reg member
    apply entered_register schema s base reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro reg low high
    exact congrArg (fun wordValue : BitVec 128 => wordValue.setWidth 64) (entered_vector schema s base reg)

theorem wrong_executes (schema : Schema) (s : ArmState) (args : Args) (value : Value)
    (base : BitVec 64) (owned : Owned s args schema.descriptor value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.entry)
    (registers : BodyRegisters s args)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64)
    (notBits : ∀ bits, value ≠ .bits bits) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args schema.descriptor value base := by
  let u := ListEntry.gated schema.kind s base
  have firstRun : run 2 s = u := ListEntry.gate_run schema.kind s base code error pc
  have program : u.program = s.program := ListEntry.gated_program schema.kind s base
  have uError : read_err u = .None := (ListEntry.gated_error schema.kind s base).trans error
  have uSP : r (.GPR 31#5) u = r (.GPR 31#5) s := ListEntry.gated_register schema.kind s base 31#5
  have uAligned : CheckSPAlignment u := by
    simpa only [CheckSPAlignment, state_simp_rules, uSP] using aligned
  have memory : u.mem = s.mem := ListEntry.gated_memory schema.kind s base
  have own : Owned u args schema.descriptor value := owned.of_local_frame (fun address _ => congrFun memory address)
  have measured : outcome u args schema.descriptor value =
      SszNative.Serialize.unchanged (arenaOf u args).used (.error .wrongType) := by
    cases value with
    | bits bits => exact False.elim (notBits bits rfl)
    | bool payload | uint payload | bytes payload | seq payload => cases schema <;> rfl
    | union selector payload => cases schema <;> rfl
  have post := Result.wrong_produced base own
    ((ListEntry.gated_register schema.kind s base 19#5).trans registers.result)
    (uSP.trans registers.stack) (by rw [measured]; rfl) (by rw [measured]; rfl)
    (by rw [measured]; rfl) uError
  refine ⟨50, Result.wrongResult u base, ?_, ?_⟩
  · rw [show 50 = 2 + 48 by decide, run_plus, firstRun]
    exact Result.wrong_run u base (code.congr program) uError uAligned
      (ListEntry.gated_pc_wrong schema.kind s base value tag notBits)
  · apply post.prepend_stack owned (fun address _ => congrFun memory address) program
    · intro reg member
      exact ListEntry.gated_register schema.kind s base reg
    · intro reg low high
      exact congrArg (fun wordValue : BitVec 128 => wordValue.setWidth 64)
        (ListEntry.gated_vector schema.kind s base reg)

theorem body_executes (schema : Schema) (s : ArmState) (args : Args) (value : Value)
    (base : BitVec 64) (owned : Owned s args schema.descriptor value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.entry)
    (registers : BodyRegisters s args) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args schema.descriptor value base := by
  cases value with
  | bits bits => exact bits_executes schema s args bits base owned code error aligned pc registers descriptor tag
  | bool payload | uint payload | bytes payload | seq payload =>
    exact wrong_executes schema s args _ base owned code error aligned pc registers tag (by intro bits clash; cases clash)
  | union selector payload =>
    exact wrong_executes schema s args _ base owned code error aligned pc registers tag (by intro bits clash; cases clash)

end SszArm.Measure.Bits.List

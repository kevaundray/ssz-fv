import SszArm.MeasureBitVectorCapBody
import SszArm.MeasureBitVectorWrong

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem bits_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 3#32) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  let checked := gated s base
  let u := header checked
  have gateRun : run 2 s = checked := gate_run s base code error pc
  have checkedPC : read_pc checked = base + 576#64 := gated_pc_bits s base tag
  have headerRun : run 3 checked = u := header_run checked base
    (code.congr (gated_program s base)) ((gated_error s base).trans error) checkedPC
  have program : u.program = s.program := (header_program checked).trans (gated_program s base)
  have memory : u.mem = s.mem := (header_memory checked).trans (gated_memory s base)
  have ue : read_err u = .None := (header_error checked).trans ((gated_error s base).trans error)
  have own : Owned u args (.bitVector cap) (.bits bits) := owned.of_local_frame (by
    intro address outside
    exact congrFun memory address)
  have ur : BodyRegisters u args :=
    ⟨(header_register checked 19#5 (by decide)).trans ((gated_register s base 19#5).trans registers.result),
     (header_register checked 20#5 (by decide)).trans ((gated_register s base 20#5).trans registers.arena),
     (header_register checked 21#5 (by decide)).trans ((gated_register s base 21#5).trans registers.value),
     (header_register checked 31#5 (by decide)).trans ((gated_register s base 31#5).trans registers.stack)⟩
  have sp : r (.GPR 31#5) u = r (.GPR 31#5) s :=
    (header_register checked 31#5 (by decide)).trans (gated_register s base 31#5)
  have ua : CheckSPAlignment u := by
    simpa only [CheckSPAlignment, state_simp_rules, sp] using aligned
  obtain ⟨capPointer, capPayload⟩ := cap_reads owned
  obtain ⟨countLow, countHigh⟩ := count_reads owned
  have pointerRead : read_mem_bytes 8 (r (.GPR 1#5) checked + 8#64) checked = cap.pointer := by
    simpa [checked, gated, state_simp_rules, descriptor] using capPointer
  have payloadRead : read_mem_bytes 8 (r (.GPR 1#5) checked + 16#64) checked = cap.payload := by
    simpa [checked, gated, state_simp_rules, descriptor] using capPayload
  have lowRead : read_mem_bytes 8 (r (.GPR 21#5) checked + 32#64) checked = bits.count.setWidth 64 := by
    simpa [checked, gated, state_simp_rules, registers.value] using countLow
  have highRead : read_mem_bytes 8 (r (.GPR 21#5) checked + 40#64) checked =
      (bits.count >>> 64).setWidth 64 := by
    simpa [checked, gated, state_simp_rules, registers.value] using countHigh
  have fields := header_fields checked
  have ud : r (.GPR 1#5) u = args.descriptor + 8#64 := by
    simpa only [u, checked, gated_register, descriptor] using fields.1
  have up : read_pc u = base + BitVec.ofNat 64 (if cap.pointer = 0#64 then 3268 else 588) := by
    simpa only [pointerRead] using header_pc checked base checkedPC
  obtain ⟨fuel, t, after, post⟩ := cap_body u base args cap bits own ur (code.congr program) ue ua up ud
    (fields.2.1.trans pointerRead) (fields.2.2.1.trans payloadRead)
    (fields.2.2.2.1.trans lowRead) (fields.2.2.2.2.trans highRead)
  refine ⟨2 + 3 + fuel, t, by rw [run_plus, run_plus, gateRun, headerRun, after],
    Scalar.prepend_pure post program memory ?_ ?_⟩
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact (header_register checked _ (by decide)).trans (gated_register s base _)
  · intro reg low high
    rw [header_vector, gated_vector]

end SszArm.Measure.BitVector

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Value)

/-- The original BitVector leaf, with actual Small/Large cap conversion,
comparison, conditional error allocation, and every native error continuation. -/
theorem bitVector_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (value : Value)
    (owned : Owned s args (.bitVector cap) value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) value base := by
  cases value with
  | bits bits =>
    exact BitVector.bits_body s base args cap bits owned registers code error aligned pc descriptor
      (by simp [tag, Emit.valueTag])
  | bool flag | uint flag | bytes flag | seq flag =>
    exact BitVector.wrong_body s base args cap _ owned registers code error aligned pc tag
      (by intro bits impossible; cases impossible)
  | union selector content =>
    exact BitVector.wrong_body s base args cap _ owned registers code error aligned pc tag
      (by intro bits impossible; cases impossible)

end SszArm.Measure

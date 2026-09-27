import SszArm.NatAddWidth
import SszArm.NatAddBorrowTrim
import SszArm.NatAddReturnValues
import SszNatOperandNormalization

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Prefix observations needed to compose a zero-operand return. All memory
writes are the real output/lowering intervals; the arena is never changed. -/
structure ZeroFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  out : r (.GPR 0#5) t = r (.GPR 0#5) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  memory : MemoryFrame (localWrites s) s t

theorem ZeroFrame.of_scan {s t : ArmState} (frame : NatCompare.Frame s t)
    (out : r (.GPR 0#5) t = r (.GPR 0#5) s)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : ZeroFrame s t := by
  refine ⟨frame.program, frame.error, out, frame.sp, ?_, ?_, scan_memory frame stack⟩
  · intro reg low high
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat constructor <;> bv_omega
  · intro reg low high
    rw [frame.vectors]

theorem ZeroFrame.writes {s t : ArmState} (frame : ZeroFrame s t) :
    localWrites t = localWrites s := by
  simp only [localWrites, frame.out, frame.sp]

theorem ZeroFrame.aligned {s t : ArmState} (frame : ZeroFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using ha

theorem ZeroFrame.code {s t : ArmState} (frame : ZeroFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, frame.program] using hc

theorem ZeroFrame.owned {s t : ArmState} (frame : ZeroFrame s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [frame.sp] using owned.stack
  · simpa only [frame.out] using owned.output
  · simpa only [frame.out, frame.sp] using owned.separate

theorem ZeroFrame.returned {s u t : ArmState} (frame : ZeroFrame s u)
    (returned : Returned u t) : Returned s t := by
  refine ⟨returned.pc.trans (frame.registers 30#5 (by decide) (by decide)),
    returned.error, returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg low high
    exact (returned.registers reg low high).trans (frame.registers reg low high)
  · intro reg low high
    exact (returned.vectors reg low high).trans (frame.vectors reg low high)

/-- A proved actual return, retained independently of which zero branch selected it. -/
def ZeroRun (s : ArmState) (operand : SszNative.NatOperand) : Prop :=
  ∃ fuel state, run fuel s = state ∧ Returned s state ∧
    MemoryFrame (localWrites s) s state ∧
    SszNative.NatArithmetic.AddResultAt (widthLoad state) (r (.GPR 0#5) s).toNat (.ok operand)

theorem ZeroRun.prepend {s u : ArmState} {operand : SszNative.NatOperand}
    (fuel : Nat) (execution : run fuel s = u) (frame : ZeroFrame s u)
    (finished : ZeroRun u operand) : ZeroRun s operand := by
  obtain ⟨steps, state, ran, returned, memory, result⟩ := finished
  refine ⟨fuel + steps, state, ?_, frame.returned returned, frame.memory.trans ?_, ?_⟩
  · rw [run_plus, execution, ran]
  · simpa only [frame.writes] using memory
  · simpa only [frame.out] using result

theorem value_zero_run (path : StatusPath) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (valueStart path))
    (owned : ReturnOwned s) (operand : SszNative.NatOperand)
    (pointer : valuePointer path s = operand.pointer)
    (payload : valuePayload path s = operand.payload)
    (input : operand.At (widthLoad s)) (borrowed : OperandOwned (localWrites s) operand) :
    ZeroRun s operand := by
  have memory := value_local_frame path s base owned
  have header := value_header_image path s base owned
  refine ⟨(valueOps path).length + 11, valueResult path base s,
    value_run path s base hc he ha hp, value_returned path s base he, memory,
    ⟨⟨?_, ?_, operand_at_preserved memory operand input borrowed⟩, ?_⟩⟩
  · simpa only [pointer] using header.1
  · simpa only [payload] using header.2
  · simpa only [valueResult, value_body_out] using
      status_image path (valueBody path base s) base (value_body_owned path s base owned)

/-- Static arena separation proves cursor preservation for every allocation-free
return, even when the initial cursor exceeds capacity. -/
theorem ZeroRun.post {s : ArmState} {left right operand : SszNative.NatOperand}
    (owned : Owned s left right) (finished : ZeroRun s operand)
    (model : outcome s left right = SszNative.NatArithmetic.unchanged (arenaOf s).used (.ok operand)) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  obtain ⟨fuel, state, execution, returned, memory, result⟩ := finished
  refine ⟨fuel, state, execution, ?_⟩
  apply post_of_frame s state left right owned returned
  · simpa only [model, SszNative.NatArithmetic.unchanged] using result
  · intro reservation allocated
    simp only [model, SszNative.NatArithmetic.unchanged] at allocated
    cases allocated
  · have bound := owned.arenaBound
    have address : (r (.GPR 5#5) s + 16#64).toNat = (r (.GPR 5#5) s).toNat + 16 := by
      bv_omega
    have same := memory.read (r (.GPR 5#5) s + 16#64) 8
      (by rw [address]; omega)
      (by rw [address]; exact owned.arenaLocal.subspan 16 8 (by decide))
    simpa only [model, SszNative.NatArithmetic.unchanged, arenaOf] using congrArg BitVec.toNat same
  · simpa only [model, SszNative.NatArithmetic.unchanged, writesFor] using memory

end SszArm.NatAdd

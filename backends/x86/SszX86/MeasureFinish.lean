import SszX86.MeasureNoAlloc
import SszX86.MeasureOutput

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

/-- A shared publication bridge derives all original observations from BodyOwned.
Its current-state equalities describe the already-proved read-only branch prefix. -/
theorem success_body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (operand : NatOperand)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) =
      unchanged used.toNat (.ok operand))
    (memory : t.dmem = s.dmem) (outReg : t.regs.rbx = s.regs.rbx)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (pointer : t.regs.rcx.toBitVec = operand.pointer)
    (payload : t.regs.rax.toBitVec = operand.payload)
    (borrowed : ∀ a, Emit.NatBorrowed operand a → BodyBorrowed s desc value buffer a)
    (original : operand.At (widthLoad s.dmem)) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc value buffer address capacity used u.1)
      (t, base + 3052) := by
  have hm : OutputMapped t := by simpa only [OutputMapped, memory, outReg] using owned.resultMapped
  apply success_cps e base hc t hm
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  have frame : MemoryFrame s.dmem
      (planMem t.dmem t.regs.rbx.toBitVec t.regs.rcx.toBitVec t.regs.rax.toBitVec)
      (ResultWrites s.regs.rbx.toBitVec (unchanged used.toNat (.ok operand))) := by
    change MemoryFrame s.dmem
      (planMem t.dmem t.regs.rbx.toBitVec t.regs.rcx.toBitVec t.regs.rax.toBitVec)
      (fun a => InSpan a s.regs.rbx.toBitVec 40 ∨ InSpan a (s.regs.rbx.toBitVec + 64) 4)
    simpa only [memory, outReg, pointer, payload] using
      plan_frame s.dmem s.regs.rbx.toBitVec operand.pointer operand.payload
  apply noalloc_body_post s
    ({t with dmem := planMem t.dmem t.regs.rbx.toBitVec t.regs.rcx.toBitVec t.regs.rax.toBitVec})
    desc value buffer address capacity used (.ok operand) owned model stack vectors
  · have kept := owned.publication_operand _ (unchanged used.toNat (.ok operand)) operand
      frame borrowed original
    have observed := plan_reads s.dmem s.regs.rbx.toBitVec operand
      (by simpa only [memory, outReg, pointer, payload] using kept)
    simpa only [ResultAt, memory, outReg, pointer, payload, UInt64.toNat_toBitVec] using observed
  · exact frame

theorem small_success_body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used limb : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) =
      unchanged used.toNat (.ok (.small limb)))
    (memory : t.dmem = s.dmem) (outReg : t.regs.rbx = s.regs.rbx)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (payload : t.regs.rax.toBitVec = limb) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc value buffer address capacity used u.1)
      (t, base + 3050) := by
  measure_step 435 using hc
  constructor <;>
    apply success_body_cps e base hc s _ desc value buffer address capacity used (.small limb)
  all_goals first
    | exact owned
    | exact model
    | exact memory
    | exact outReg
    | exact stack
    | exact vectors
    | exact payload
    | rfl
    | exact fun _ impossible => False.elim impossible
    | trivial

theorem wrong_type_body_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) =
      unchanged used.toNat (.error .wrongType))
    (memory : t.dmem = s.dmem) (outReg : t.regs.rbx = s.regs.rbx)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc value buffer address capacity used u.1)
      (t, base + 3265) := by
  have hm : OutputMapped t := by simpa only [OutputMapped, memory, outReg] using owned.resultMapped
  apply wrong_type_cps e base hc t hm
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  apply noalloc_body_post s
    ({t with dmem := wrongTypeMem t.dmem t.regs.rbx.toBitVec})
    desc value buffer address capacity used (.error .wrongType) owned model stack vectors
  · simpa only [memory, outReg, ResultAt, UInt64.toNat_toBitVec] using
      wrong_type_reads s.dmem s.regs.rbx.toBitVec
  · change MemoryFrame s.dmem (wrongTypeMem t.dmem t.regs.rbx.toBitVec)
      (fun a => InSpan a s.regs.rbx.toBitVec 68 ∨ (0 : Nat) = 2 ∧ InSpan a (s.regs.rbx.toBitVec + 68) 4)
    simpa only [memory, outReg, show ¬ (0 : Nat) = 2 by decide, false_and, or_false] using
      wrong_type_frame s.dmem s.regs.rbx.toBitVec

end SszX86.Measure

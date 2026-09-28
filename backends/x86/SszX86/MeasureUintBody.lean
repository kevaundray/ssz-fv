import SszX86.MeasureUintOwned
import SszX86.MeasureOutput

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

namespace Uint

/-- Common publication is entered with the original represented width, even
when either operand has redundant high zeros. Failure publishes WrongType. -/
theorem publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s current : MachineData) (logicalWidth number : NatOperand)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.uint logicalWidth) (.uint number) buffer address capacity used)
    (memoryMapped : OutputMapped current)
    (stack : current.regs.rsp = s.regs.rsp)
    (result : current.regs.rbx = s.regs.rbx)
    (vectors : current.zmms = s.zmms)
    (frame : MemoryFrame s.dmem current.dmem (Scratch s))
    (pointer : current.regs.rcx.toBitVec = logicalWidth.pointer)
    (payload : current.regs.rax.toBitVec = logicalWidth.payload) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.uint logicalWidth) (.uint number) buffer address capacity used t.1)
      (current, if uintFits logicalWidth number then base + 3052 else base + 3265) := by
  by_cases fits : uintFits logicalWidth number
  · rw [ite_eq_left fits]
    apply success_cps e base hc current memoryMapped
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    have publication : MemoryFrame current.dmem
        (planMem current.dmem current.regs.rbx.toBitVec current.regs.rcx.toBitVec current.regs.rax.toBitVec)
        (ResultWrites s.regs.rbx.toBitVec (unchanged used.toNat (.ok logicalWidth))) := by
      intro a outside
      apply plan_frame current.dmem current.regs.rbx.toBitVec
        current.regs.rcx.toBitVec current.regs.rax.toBitVec a
      simpa only [result, ResultWrites, unchanged] using outside
    have combined := finish_frame s _ _ (unchanged used.toNat (.ok logicalWidth)) frame publication
    apply finish_post s _ (.uint logicalWidth) (.uint number) buffer address capacity used (.ok logicalWidth) owned
    · simp only [Serialize.measure, fits, ↓reduceIte, arenaState]
    · exact stack
    · exact vectors
    · change PlanAt _ _ logicalWidth
      have operand := finish_operand owned _ (unchanged used.toNat (.ok logicalWidth)) combined
      rw [pointer, payload] at operand ⊢
      simpa only [result, UInt64.toNat_toBitVec] using
        plan_reads current.dmem current.regs.rbx.toBitVec logicalWidth operand
    · exact combined
  · rw [ite_eq_right fits]
    apply wrong_type_cps e base hc current memoryMapped
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    have publication : MemoryFrame current.dmem (wrongTypeMem current.dmem current.regs.rbx.toBitVec)
        (ResultWrites s.regs.rbx.toBitVec (unchanged used.toNat (.error .wrongType))) := by
      intro a outside
      apply wrong_type_frame current.dmem current.regs.rbx.toBitVec a
      simpa [result, ResultWrites, unchanged] using outside
    have combined := finish_frame s _ _ (unchanged used.toNat (.error .wrongType)) frame publication
    apply finish_post s _ (.uint logicalWidth) (.uint number) buffer address capacity used
      (.error .wrongType) owned
    · simp only [Serialize.measure, fits, ↓reduceIte, arenaState]
    · exact stack
    · exact vectors
    · simpa only [ResultAt, result, UInt64.toNat_toBitVec] using
        wrong_type_reads current.dmem current.regs.rbx.toBitVec
    · exact combined

/-- Non-Uint values take the original entry tag branch without reading Nat payloads. -/
theorem wrong_value_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (logicalWidth : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.uint logicalWidth) value buffer address capacity used)
    (tag : s.regs.rax.toBitVec.setWidth 8 ≠ 1#8)
    (model : Serialize.measure (.uint logicalWidth) value (arenaState address capacity used) =
      unchanged used.toNat (.error .wrongType)) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.uint logicalWidth) value buffer address capacity used t.1)
      (s, base + 795) := by
  apply tag_cps e base hc
  intro flags
  rw [ite_eq_right tag]
  apply wrong_type_cps e base hc ({s with status := flags}) owned.resultMapped
  apply Eventually.done
  refine ⟨rfl, ?_⟩
  apply noalloc_body_post s ({s with status := flags, dmem := wrongTypeMem s.dmem s.regs.rbx.toBitVec})
    (.uint logicalWidth) value buffer address capacity used (.error .wrongType) owned model rfl rfl
  · simpa only [ResultAt, UInt64.toNat_toBitVec] using wrong_type_reads s.dmem s.regs.rbx.toBitVec
  · intro a outside
    apply wrong_type_frame s.dmem s.regs.rbx.toBitVec a
    simpa [ResultWrites, unchanged] using outside

/-- Actual Uint branch entry795 through the common pre-epilogue3335. Every
original value and semantic outcome is admitted. All reads, mapped writes, and
BSR restoration are derived from the initial BodyOwned, never an execution premise. -/
theorem body_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (logicalWidth : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.uint logicalWidth) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.uint logicalWidth) value buffer address capacity used t.1)
      (s, base + 795) := by
  cases value with
  | uint number =>
    apply tag_cps e base hc
    intro flags
    have tag : s.regs.rax.toBitVec.setWidth 8 = 1#8 := owned.tag
    rw [ite_eq_left tag]
    apply number_cps e base hc ({s with status := flags}) number owned.valueStored.2
    · intro i hi
      exact owned.localMapped i (by omega)
    · intro measured ready
      have initialReady : NumberReady s measured number :=
        ⟨ready.memory, ready.stack, ready.result, ready.descriptor,
          ready.valuePointer, ready.vectors, ready.required⟩
      apply width_cps e base hc measured logicalWidth (number_descriptor owned initialReady)
      intro checked widthReady
      have requirement : measured.regs.rdx.toNat * 2 ^ 64 + measured.regs.rdi.toNat =
          requiredBytes number.value := by
        have computed := initialReady.required
        change measured.regs.rdi.toNat + 2 ^ 64 * measured.regs.rdx.toNat = _ at computed
        omega
      rw [requirement]
      change Eventually (step e) _
        (checked, if uintFits logicalWidth number then base + 3052 else base + 3265)
      apply publish_cps e base hc s checked logicalWidth number buffer address capacity used owned
      · unfold OutputMapped
        rw [widthReady.frame.memory, widthReady.frame.result, initialReady.result]
        exact number_mapped initialReady s.regs.rbx.toBitVec 72 owned.resultMapped
      · exact widthReady.frame.stack.trans initialReady.stack
      · exact widthReady.frame.result.trans initialReady.result
      · exact widthReady.frame.vectors.trans initialReady.vectors
      · rw [widthReady.frame.memory]
        exact number_frame initialReady
      · exact widthReady.pointer
      · exact widthReady.payload
  | bool boolean =>
    apply wrong_value_cps e base hc s logicalWidth (.bool boolean) buffer address capacity used owned
    · rw [owned.tag]
      change 0#8 ≠ 1#8
      decide
    · rfl
  | bytes bytes =>
    apply wrong_value_cps e base hc s logicalWidth (.bytes bytes) buffer address capacity used owned
    · rw [owned.tag]
      change 2#8 ≠ 1#8
      decide
    · rfl
  | bits bits =>
    apply wrong_value_cps e base hc s logicalWidth (.bits bits) buffer address capacity used owned
    · rw [owned.tag]
      change 3#8 ≠ 1#8
      decide
    · rfl
  | seq values =>
    apply wrong_value_cps e base hc s logicalWidth (.seq values) buffer address capacity used owned
    · rw [owned.tag]
      change 4#8 ≠ 1#8
      decide
    · rfl
  | union selector value =>
    apply wrong_value_cps e base hc s logicalWidth (.union selector value) buffer address capacity used owned
    · rw [owned.tag]
      change 5#8 ≠ 1#8
      decide
    · rfl

end Uint

/-- The constructor-indexed branch theorem consumed by original-entry composition. -/
theorem uint_body_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (logicalWidth : NatOperand) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.uint logicalWidth) value buffer address capacity used) :
    Eventually (step e)
      (fun t => t.2 = base + 3335 ∧
        BodyPost s (.uint logicalWidth) value buffer address capacity used t.1)
      (s, base + Int64.ofNat (bodyEntry (.uint logicalWidth))) :=
  Uint.body_runs e base hc s logicalWidth value buffer address capacity used owned

end SszX86.Measure

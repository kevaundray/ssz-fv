import SszX86.SerializeBranches

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

theorem sized_runs (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (operand : NatOperand)
    (measured : (SszNative.Serialize.measure desc value (arenaState address capacity used)).result = .ok operand)
    (host : operand.value < 2 ^ 64) (length : t.regs.r9.toNat = operand.value)
    (fits : t.regs.r9.toNat ≤ s.regs.r8.toNat) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 388) := by
  have valid := measured_valid desc value address capacity used operand owned.physical measured host
  have fitsValue : operand.value ≤ s.regs.r8.toNat := by rwa [length] at fits
  apply emit_runs e base closure s t desc value buffer address capacity used ra owned before
  · simpa only [length] using valid
  · exact fits
  · exact ⟨operand, measured⟩
  · simp only [written, SszNative.Serialize.serialize, encodedSize, SszNative.Serialize.bind,
      measured, hostSize, host, ↓reduceIte, unchanged, fitsValue, length]
  · simp only [written, SszNative.Serialize.serialize, encodedSize, SszNative.Serialize.bind,
      measured, hostSize, host, ↓reduceIte, unchanged, fitsValue]

theorem capacity_runs (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (operand : NatOperand)
    (measured : (SszNative.Serialize.measure desc value (arenaState address capacity used)).result = .ok operand)
    (host : operand.value < 2 ^ 64) (length : t.regs.r9.toNat = operand.value) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 308) := by
  apply capacity_cps e base closure.wrapper t
  · intro fits flags
    apply sized_runs e base closure s _ desc value buffer address capacity used ra owned
      (before.status flags) operand measured host length
    simpa only [before.anchors.r13] using fits
  · intro short flags
    have notFits : ¬ operand.value ≤ s.regs.r8.toNat := by
      rw [before.anchors.r13, length] at short
      omega
    apply too_small_runs e base closure.wrapper s _ desc value buffer address capacity used ra
      owned (before.status flags) operand measured _ false
    simp only [written, SszNative.Serialize.serialize, encodedSize, SszNative.Serialize.bind,
      measured, hostSize, host, ↓reduceIte, unchanged, notFits]

theorem AtWrapper.copied {s t : MachineData} (anchors : AtWrapper s t)
    (image : Publish.Image) (flags : StatusFlags) :
    AtWrapper s (Publish.copied t image flags) := by
  exact ⟨anchors.stack, anchors.rbx, anchors.rbp, anchors.r12, anchors.r13,
    anchors.r14, anchors.r15, anchors.vectors⟩

/-- PC47 consumes the actual measurement result, including its uninitialized
padding observations, and follows exactly one of error/host/capacity/emit paths. -/
theorem after_measure_runs (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (observed : Measure.ResultAt (widthLoad t.dmem) (t.regs.rsp.toBitVec + 24).toNat
      (SszNative.Serialize.measure desc value (arenaState address capacity used)).result) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 47) := by
  have stack := before.stack_mapped owned
  have bound := before.anchors.stack_bound owned
  have planMapped : Large.Mapped t.dmem (t.regs.rsp.toBitVec + 24) 72 :=
    Delimited.Reservation.mapped_subrange t.dmem t.regs.rsp.toBitVec 96 24 72 stack (by decide)
  obtain ⟨image, stored⟩ := Publish.mapped_image t.dmem (t.regs.rsp.toBitVec + 24) planMapped
  cases measured : (SszNative.Serialize.measure desc value (arenaState address capacity used)).result with
  | error reason =>
    have error : Measure.ErrorAt (widthLoad t.dmem) (t.regs.rsp.toBitVec + 24).toNat reason := by
      simpa only [measured, Measure.ResultAt] using observed
    have tag := Publish.image_error_tag t.dmem _ image reason stored error
    have apart : Large.Disjoint t.regs.rsp.toBitVec t.regs.rbx.toBitVec 96 80 := by
      intro i hi j hj equal
      apply owned.resultStack j hj (288 + i) (by omega)
      have sp : t.regs.rsp.toBitVec = stackBase s + 288 := by
        rw [before.anchors.stack]
        simp only [wrapperSP, stackBase]
        bv_omega
      rw [before.anchors.rbx, sp] at equal
      simpa only [BitVec.ofNat_add, BitVec.add_assoc,
        show (288 : BitVec 64) = 288#64 by decide] using equal.symm
    apply Publish.failure_cps e base closure.wrapper t image stack (before.result_mapped owned)
      bound apart stored tag
    intro flags
    apply finish_runs e base closure.wrapper s (Publish.copied t image flags) desc value
      buffer address capacity used ra owned (before.anchors.copied image flags)
    have failure : (written s desc value address capacity used).outcome.result = .error reason := by
      simp only [written, SszNative.Serialize.serialize, encodedSize, SszNative.Serialize.bind, measured]
    refine failure_finish (u := Publish.copied t image flags) owned before (n := 72)
      (by decide) ?_ ?_ failure ?_
    · intro a outside
      apply Publish.copied_frame t image flags a
      intro writes
      rcases writes with result | scratch
      · exact outside (Or.inl (by simpa only [before.anchors.rbx] using result))
      · exact outside (Or.inr (wrapper_local_span s t before.anchors 16 (by decide) a scratch))
    · intro a inside
      simpa only [ResultWrites, measured] using inside
    · have resultBound : t.regs.rbx.toNat + 80 ≤ 2 ^ 64 := by
        simpa only [before.anchors.rbx] using owned.resultBound
      have copied := Publish.copied_error t image flags reason stored resultBound error (by
        intro a borrowed writes
        apply owned.result_borrows_safe a (by
          simpa only [measured, ResultBorrows] using borrowed)
        rcases writes with ⟨i, hi, equal⟩ | scratch
        · exact Or.inl ⟨i, by omega, by simpa only [before.anchors.rbx] using equal⟩
        · exact Or.inr (Or.inr (wrapper_local_span s t before.anchors 16 (by decide) a scratch)))
      simpa only [before.anchors.rbx] using copied
  | ok operand =>
    have plan : Measure.PlanAt (widthLoad t.dmem) (t.regs.rsp.toBitVec + 24).toNat operand := by
      simpa only [measured, Measure.ResultAt] using observed
    have imagePlan := Publish.image_plan t.dmem _ image operand stored plan
    apply Publish.success_cps e base closure.wrapper t image stack bound stored imagePlan.1
    intro flags
    have preparation := Publish.prepared_plan t image flags operand bound stored plan (by
      intro a borrowed scratch
      apply owned.result_borrows_safe a (by
        simpa only [measured, ResultBorrows] using borrowed)
      exact Or.inr (Or.inr (wrapper_local_span s t before.anchors 56 (by decide) a scratch)))
    have prepared := before.prepared owned image flags
    apply host_cps e base closure.wrapper (Publish.prepared t image flags) operand
      preparation.2.1 preparation.2.2 preparation.1.2.2.1.2.2
    · intro tooLarge u frame
      have host : ¬ operand.value < 2 ^ 64 := by omega
      apply too_small_runs e base closure.wrapper s u desc value buffer address capacity used ra
        owned (prepared.host frame) operand measured _ true
      simp only [written, SszNative.Serialize.serialize, encodedSize, SszNative.Serialize.bind,
        measured, hostSize, host, ↓reduceIte, unchanged]
    · intro host u frame length
      exact capacity_runs e base closure s u desc value buffer address capacity used ra
        owned (prepared.host frame) operand measured host length
    · intro zero u frame length fits
      have host : operand.value < 2 ^ 64 := by rw [zero]; decide
      have lengthNat : u.regs.r9.toNat = operand.value := by
        change u.regs.r9.toBitVec.toNat = operand.value
        rw [length, zero]
        rfl
      apply sized_runs e base closure s u desc value buffer address capacity used ra
        owned (prepared.host frame) operand measured host lengthNat
      rw [lengthNat]
      simpa only [(prepared.host frame).anchors.r13] using fits

end SszX86.Serialize

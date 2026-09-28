import SszX86.SerializeEmit
import SszX86.SerializeProvenance
import SszX86.SerializeMeasured

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

theorem AtWrapper.stack_bound {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra) (anchors : AtWrapper s t) :
    t.regs.rsp.toNat + 96 ≤ 2 ^ 64 := by
  have low := owned.stackLow
  have bound := owned.returnBound
  have sp := anchors.stack
  simp only [wrapperSP, ← UInt64.toNat_toBitVec] at low bound sp ⊢
  bv_omega

theorem wrapper_local_span (s t : MachineData) (anchors : AtWrapper s t)
    (n : Nat) (small : n ≤ 56) (a : BitVec 64)
    (inside : InSpan a (t.regs.rsp.toBitVec + 8) n) : InSpan a (stackBase s) 384 := by
  obtain ⟨i, hi, equal⟩ := inside
  refine ⟨296 + i, by omega, ?_⟩
  rw [equal, anchors.stack]
  simp only [wrapperSP, stackBase]
  bv_omega

theorem BeforeEmit.lower_stack {s t u : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (anchors : AtWrapper s u)
    (frame : MemoryFrame t.dmem u.dmem (fun a => InSpan a (stackBase s) 384))
    (mapping : BitVector.Mapping.Extends t.dmem u.dmem) :
    BeforeEmit s base desc value buffer address capacity used ra u := by
  refine ⟨anchors, before.resources.transport owned (fun a outside =>
    frame a (fun inside => outside (Or.inr (Or.inr inside)))), before.mapped.trans mapping, ?_, ?_⟩
  · intro i hi
    rw [frame]
    · exact before.output i hi
    · rintro ⟨j, hj, equal⟩
      exact owned.outputStack i hi j (by omega) equal
  · intro a outside
    rw [frame a (fun inside => outside (Or.inr (Or.inr (Or.inr (Or.inr (by
      obtain ⟨i, hi, equal⟩ := inside
      exact ⟨i, by omega, equal⟩))))))]
    exact before.frame a outside

theorem BeforeEmit.host {s t u : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (frame : HostFrame t u) : BeforeEmit s base desc value buffer address capacity used ra u := by
  refine ⟨before.anchors.host frame, ?_, ?_, ?_, ?_⟩
  · simpa only [frame.memory] using before.resources
  · simpa only [frame.memory] using before.mapped
  · simpa only [frame.memory] using before.output
  · simpa only [frame.memory] using before.frame

theorem BeforeEmit.status {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (flags : StatusFlags) : BeforeEmit s base desc value buffer address capacity used ra
      {t with status := flags} := before.host (host_status_frame t flags)

theorem AtWrapper.prepared {s t : MachineData} (anchors : AtWrapper s t)
    (image : Publish.Image) (flags : StatusFlags) :
    AtWrapper s (Publish.prepared t image flags) := by
  exact ⟨anchors.stack, anchors.rbx, anchors.rbp, anchors.r12, anchors.r13,
    anchors.r14, anchors.r15, anchors.vectors⟩

theorem AtWrapper.capacityFailed {s t : MachineData} (anchors : AtWrapper s t) :
    AtWrapper s (Publish.capacityFailed t) := by
  exact ⟨anchors.stack, anchors.rbx, anchors.rbp, anchors.r12, anchors.r13,
    anchors.r14, anchors.r15, anchors.vectors⟩

theorem AtWrapper.hostFailed {s t : MachineData} (anchors : AtWrapper s t) :
    AtWrapper s (Publish.hostFailed t) := by
  exact ⟨anchors.stack, anchors.rbx, anchors.rbp, anchors.r12, anchors.r13,
    anchors.r14, anchors.r15, anchors.vectors⟩

theorem BeforeEmit.prepared {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (image : Publish.Image) (flags : StatusFlags) :
    BeforeEmit s base desc value buffer address capacity used ra (Publish.prepared t image flags) := by
  apply before.lower_stack owned
  · exact before.anchors.prepared image flags
  · intro a outside
    exact Publish.prepared_state_frame t image flags a
      (fun inside => outside (wrapper_local_span s t before.anchors 56 (by decide) a inside))
  · exact Publish.prepared_state_mapping t image flags

theorem BeforeEmit.stack_mapped {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t) :
    Large.Mapped t.dmem t.regs.rsp.toBitVec 96 := by
  have hm := before.mapped _ _ owned.stackMapped
  have pointer : t.regs.rsp.toBitVec = stackBase s + 288 := by
    rw [before.anchors.stack]
    simp only [wrapperSP, stackBase]
    bv_omega
  rw [pointer]
  exact Delimited.Reservation.mapped_subrange t.dmem (stackBase s) 424 288 96 hm (by decide)

theorem BeforeEmit.result_mapped {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t) :
    Large.Mapped t.dmem t.regs.rbx.toBitVec 80 := by
  rw [before.anchors.rbx]
  exact before.mapped _ _ owned.resultMapped

theorem failure_finish {s t u : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {reason : Error} {n : Nat}
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (countBound : n ≤ 80)
    (frame : MemoryFrame t.dmem u.dmem (fun a =>
      InSpan a s.regs.rdi.toBitVec n ∨ InSpan a (stackBase s) 384))
    (writes : ∀ a, InSpan a s.regs.rdi.toBitVec n →
      ResultWrites s.regs.rdi.toBitVec
        (SszNative.Serialize.measure desc value (arenaState address capacity used))
        (written s desc value address capacity used).outcome.result a)
    (failure : (written s desc value address capacity used).outcome.result = .error reason)
    (observed : Measure.ErrorAt (widthLoad u.dmem) s.regs.rdi.toNat reason) :
    FinishMemory s base desc value buffer address capacity used ra u.dmem := by
  refine {
    resources := before.resources.transport owned (fun a outside => frame a (by
      intro changed
      rcases changed with ⟨i, hi, equal⟩ | scratch
      · exact outside (Or.inl ⟨i, by omega, equal⟩)
      · exact outside (Or.inr (Or.inr scratch))))
    observed := by simpa only [failure, ResultAt] using observed
    outputFrame := ?_
    frame := ?_ }
  · have empty := serialize_failure_writes desc value s.regs.r8.toNat
      (arenaState address capacity used) reason failure
    intro i hi
    rw [show (written s desc value address capacity used).writes = #[] from empty,
      applyWrites_empty]
    rw [frame]
    · exact before.output i hi
    · intro changed
      rcases changed with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · exact owned.outputResult i hi j (by omega) equal
      · exact owned.outputStack i hi j (by omega) equal
  · intro a outside
    rw [frame a (by
      intro changed
      rcases changed with result | ⟨i, hi, equal⟩
      · exact outside (Or.inl (writes a result))
      · exact outside (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, equal⟩)))))]
    exact before.frame a outside

/-- The two OutputTooSmall arms publish the same semantic record, but their
actual stores and entry PCs are retained in the execution proofs. -/
theorem too_small_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra)
    (before : BeforeEmit s base desc value buffer address capacity used ra t)
    (operand : NatOperand)
    (measured : (SszNative.Serialize.measure desc value (arenaState address capacity used)).result = .ok operand)
    (failure : (written s desc value address capacity used).outcome.result = .error .outputTooSmall)
    (host : Bool) :
    Eventually (step e) (Post s desc value buffer address capacity used ra)
      (t, base + (if host then 235 else 313)) := by
  have bound : t.regs.rbx.toNat + 80 ≤ 2 ^ 64 := by
    simpa only [before.anchors.rbx] using owned.resultBound
  have resultWrites (a : BitVec 64) (inside : InSpan a s.regs.rdi.toBitVec 68) :
      ResultWrites s.regs.rdi.toBitVec
        (SszNative.Serialize.measure desc value (arenaState address capacity used))
        (written s desc value address capacity used).outcome.result a := by
    simpa only [ResultWrites, measured, failure] using inside
  cases host with
  | false =>
    apply Publish.capacity_cps e base hc t (before.result_mapped owned)
    apply finish_runs e base hc s (Publish.capacityFailed t) desc value
      buffer address capacity used ra owned before.anchors.capacityFailed
    refine failure_finish (u := Publish.capacityFailed t) owned before (n := 68)
      (by decide) ?_ resultWrites failure ?_
    · intro a outside
      exact Publish.capacity_frame t.dmem t.regs.rbx.toBitVec a (fun inside =>
        outside (Or.inl (by simpa only [before.anchors.rbx] using inside)))
    · simpa only [Publish.capacityFailed, before.anchors.rbx, UInt64.toNat_toBitVec] using
        (Publish.capacity_fields t.dmem t.regs.rbx.toBitVec bound).observed
  | true =>
    apply Publish.host_cps e base hc t (before.result_mapped owned)
    apply finish_runs e base hc s (Publish.hostFailed t) desc value
      buffer address capacity used ra owned before.anchors.hostFailed
    refine failure_finish (u := Publish.hostFailed t) owned before (n := 68)
      (by decide) ?_ resultWrites failure ?_
    · intro a outside
      exact Publish.host_frame t.dmem t.regs.rbx.toBitVec a (fun inside =>
        outside (Or.inl (by simpa only [before.anchors.rbx] using inside)))
    · simpa only [Publish.hostFailed, before.anchors.rbx, UInt64.toNat_toBitVec] using
        (Publish.host_fields t.dmem t.regs.rbx.toBitVec bound).observed

end SszX86.Serialize

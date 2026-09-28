import SszX86.MeasureUintNumber
import SszX86.MeasureUintWidth
import SszX86.MeasureNoAlloc

namespace SszX86.Measure.Uint
open SszNative SszNative.Serialize UintCodec

/-- Only the actual BSR lowering's sixteen private stack bytes can be touched
before publication; this is narrower than the common 232-byte body frame. -/
def Scratch (s : MachineData) (a : BitVec 64) : Prop :=
  InSpan a (s.regs.rsp.toBitVec - 16) 16

def FinishWrites (s : MachineData) (outcome : Outcome NatOperand) (a : BitVec 64) : Prop :=
  ResultWrites s.regs.rbx.toBitVec outcome a ∨ Scratch s a

theorem scratch_body (s : MachineData) (a : BitVec 64) (inside : Scratch s a) :
    InSpan a (s.regs.rsp.toBitVec - 16) 232 := by
  obtain ⟨i, hi, equal⟩ := inside
  exact ⟨i, by omega, equal⟩

theorem number_frame {s t : MachineData} {number : NatOperand}
    (ready : NumberReady s t number) : MemoryFrame s.dmem t.dmem (Scratch s) := by
  rcases ready.memory with same | saved
  · rw [same]
    intro a outside
    rfl
  · rw [saved]
    exact bsr_memory_frame s

theorem number_mapped {s t : MachineData} {number : NatOperand}
    (ready : NumberReady s t number) (pointer : BitVec 64) (count : Nat)
    (memoryMapped : Large.Mapped s.dmem pointer count) : Large.Mapped t.dmem pointer count := by
  rcases ready.memory with same | saved
  · rw [same]
    exact memoryMapped
  · rw [saved]
    unfold bsrMem Delimited.bitSaveMem
    apply Large.mapped_store
    exact Large.mapped_store _ _ _ _ _ _ memoryMapped

theorem finish_frame (s : MachineData) (m n : DataMem) (outcome : Outcome NatOperand)
    (first : MemoryFrame s.dmem m (Scratch s))
    (last : MemoryFrame m n (ResultWrites s.regs.rbx.toBitVec outcome)) :
    MemoryFrame s.dmem n (FinishWrites s outcome) := by
  intro a outside
  exact (last a (fun written => outside (Or.inl written))).trans
    (first a (fun written => outside (Or.inr written)))

theorem borrowed_finish_safe {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (outcome : Outcome NatOperand) (a : BitVec 64)
    (borrowed : BodyBorrowed s desc value buffer a) : ¬ FinishWrites s outcome a := by
  intro written
  rcases written with result | stack
  · exact owned.readonly a borrowed (Or.inl (resultWrites_span _ _ _ result))
  · exact owned.readonly a borrowed (Or.inr (Or.inr (Or.inr (scratch_body s a stack))))

/-- Padded descriptor limbs are re-derived after BSR from the original readonly ownership. -/
theorem number_descriptor {s t : MachineData} {logicalWidth number : NatOperand}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s (.uint logicalWidth) (.uint number) buffer address capacity used)
    (ready : NumberReady s t number) :
    NatAt t.dmem (t.regs.rsi.toBitVec + 8) logicalWidth := by
  rw [ready.descriptor]
  apply Emit.natAt_frame s.dmem t.dmem (Scratch s) (number_frame ready)
  · intro a inside written
    exact owned.readonly a (Or.inl (Or.inr inside))
      (Or.inr (Or.inr (Or.inr (scratch_body s a written))))
  · intro a inside written
    exact owned.readonly a (Or.inr (Or.inr (Or.inl inside)))
      (Or.inr (Or.inr (Or.inr (scratch_body s a written))))
  · exact owned.descriptor.2

/-- Original arena words are separated from both the result and real lowering activation. -/
theorem finish_header {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand)
    (frame : MemoryFrame s.dmem m (FinishWrites s outcome)) :
    ArenaAt m s.regs.rcx.toBitVec address capacity used := by
  have fields (off : Nat) (bound : off + 8 ≤ 24) :
      widthLoad m (s.regs.rcx.toNat + off) 8 =
        widthLoad s.dmem (s.regs.rcx.toNat + off) 8 := by
    unfold widthLoad
    rw [← UInt64.toNat_toBitVec, width_address]
    congr 1
    apply frame_load s.dmem m _ frame
    intro i hi written
    rcases written with result | stack
    · obtain ⟨j, hj, equal⟩ := resultWrites_span _ _ _ result
      apply owned.resultHeader j hj (off + i) (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact equal.symm
    · obtain ⟨j, hj, equal⟩ := stack
      apply owned.headerStack (off + i) (by omega) j (by omega)
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact equal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using (fields 0 (by decide)).trans owned.arena.1
  · exact (fields 8 (by decide)).trans owned.arena.2.1
  · exact (fields 16 (by decide)).trans owned.arena.2.2

/-- Wrapper-usable returned width ownership is transported through both write phases. -/
theorem finish_operand {s : MachineData} {logicalWidth : NatOperand} {value : Value}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s (.uint logicalWidth) value buffer address capacity used)
    (m : DataMem) (outcome : Outcome NatOperand)
    (frame : MemoryFrame s.dmem m (FinishWrites s outcome)) :
    logicalWidth.At (widthLoad m) := by
  apply operand_frame s.dmem m _ frame logicalWidth
  · intro a inside
    exact borrowed_finish_safe owned outcome a (Or.inr (Or.inr (Or.inl inside)))
  · exact owned.descriptor.2.2.2

/-- Complete shared BodyPost, derived from original BodyOwned and the exact
no-allocation result, with the real BSR stack footprint retained. -/
theorem finish_post (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64) (result : Except Error NatOperand)
    (owned : BodyOwned s desc value buffer address capacity used)
    (model : measure desc value (arenaState address capacity used) = unchanged used.toNat result)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (observed : ResultAt (widthLoad t.dmem) s.regs.rbx.toNat result)
    (frame : MemoryFrame s.dmem t.dmem (FinishWrites s (unchanged used.toNat result))) :
    BodyPost s desc value buffer address capacity used t := by
  have header := finish_header owned t.dmem (unchanged used.toNat result) frame
  refine ⟨stack, ?_, ?_, ⟨header.1, header.2.1⟩, ?_, ?_, ?_, ?_, vectors⟩
  · simpa only [model, unchanged] using observed
  · simpa only [model, unchanged, UInt64.toNat_toBitVec] using header.2.2
  · simp only [model, unchanged, CallsAt, List.not_mem_nil, false_implies, implies_true]
  · apply descriptor_frame s.dmem t.dmem _ frame _ desc _ owned.descriptor
    intro a borrowed
    rcases borrowed with live | limbs
    · exact borrowed_finish_safe owned _ a (Or.inl live)
    · exact borrowed_finish_safe owned _ a (Or.inr (Or.inr (Or.inl limbs)))
  · apply value_frame s.dmem t.dmem _ frame _ buffer value _ owned.valueStored
    intro a borrowed
    rcases borrowed with live | bytes
    · exact borrowed_finish_safe owned _ a (Or.inr (Or.inl live))
    · exact borrowed_finish_safe owned _ a (Or.inr (Or.inr (Or.inr bytes)))
  · intro a outside
    apply frame a
    intro written
    rcases written with result | stack
    · exact outside (Or.inl (by simpa only [model] using result))
    · exact outside (Or.inr (Or.inr (Or.inr (scratch_body s a stack))))

end SszX86.Measure.Uint

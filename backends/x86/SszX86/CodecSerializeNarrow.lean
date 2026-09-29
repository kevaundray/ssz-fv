import SszX86.CodecSerializePublish
import SszX86.SerializeCall

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- The actual wrapper cuts after host narrowing: a returned-resource-error
publication at PC410, or the real emitter entry after CALL405 has pushed PC410.
The emitted slice is the measured size, not the caller's full output capacity. -/
def NarrowPost (s : MachineData) (base : Int64) (size : NatOperand)
    (t : MachineState) : Prop :=
  (∃ current, Serialize.HostFrame s current ∧
    ((2 ^ 64 ≤ size.value ∧ t = (Serialize.Publish.hostFailed current, base + 410)) ∨
     (size.value < 2 ^ 64 ∧ s.regs.r13.toNat < size.value ∧
       t = (Serialize.Publish.capacityFailed current, base + 410)))) ∨
  (∃ current, Serialize.HostFrame s current ∧
    current.regs.r9.toNat = size.value ∧ size.value ≤ s.regs.r13.toNat ∧
    t = (Serialize.callState (Serialize.emitArguments current) (base + 410).toBitVec,
      base + Int64.ofInt emitOffset))

private theorem capacity_preserved {s t : MachineData} (frame : Serialize.HostFrame s t) :
    t.regs.r13.toNat = s.regs.r13.toNat := by
  exact congrArg BitVec.toNat (frame.registers .r13 (by decide) (by decide) (by decide))

private theorem result_mapping {s t : MachineData} (frame : Serialize.HostFrame s t)
    (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 72) :
    Large.Mapped t.dmem t.regs.rbx.toBitVec 72 := by
  have pointer := frame.registers .rbx (by decide) (by decide) (by decide)
  change t.regs.rbx.toBitVec = s.regs.rbx.toBitVec at pointer
  rw [frame.memory, pointer]
  exact hmap

private theorem call_mapping {s t : MachineData} (frame : Serialize.HostFrame s t)
    (hmap : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8) :
    Large.Mapped t.dmem (t.regs.rsp.toBitVec - 8) 8 := by
  have pointer := frame.registers .rsp (by decide) (by decide) (by decide)
  change t.regs.rsp.toBitVec = s.regs.rsp.toBitVec at pointer
  rw [frame.memory, pointer]
  exact hmap

private theorem measured_emit_entry (e : Executable) (base : Int64) (code : CodeAt e base)
    (s current : MachineData) (size : NatOperand)
    (frame : Serialize.HostFrame s current)
    (amount : current.regs.r9.toNat = size.value)
    (fits : size.value ≤ s.regs.r13.toNat)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8) :
    Eventually (step e) (NarrowPost s base size) (current, base + 388) := by
  apply Serialize.emit_arguments_cps e base code.wrapper current
  apply Serialize.call405_runs e base code.wrapper (Serialize.emitArguments current)
  · exact call_mapping frame stack
  · apply Eventually.done
    exact Or.inr ⟨current, frame, amount, fits, rfl⟩

/-- PC196 through all host conversion and capacity paths, including raw Large[]
and redundant zero limbs. No successful-size premise or promised future emitter
execution is present: failure publication and the actual CALL are both proved. -/
theorem narrow_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (size : NatOperand)
    (pointer : s.regs.rax.toBitVec = size.pointer)
    (payload : s.regs.r9.toBitVec = size.payload)
    (stored : size.At (widthLoad s.dmem))
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8) :
    Eventually (step e) (NarrowPost s base size) (s, base + 196) := by
  apply Serialize.host_cps e base code.wrapper s size pointer payload stored
  · intro overflow current frame
    apply Publish.host_cps e base code current (result_mapping frame result)
    exact Eventually.done _ (Or.inl ⟨current, frame, Or.inl ⟨overflow, rfl⟩⟩)
  · intro representable current frame amount
    apply Serialize.capacity_cps e base code.wrapper current
    · intro fits flags
      have frame' := frame.trans (Serialize.host_status_frame current flags)
      apply measured_emit_entry e base code s _ size frame' amount
      · rw [← amount, ← capacity_preserved frame]
        exact fits
      · exact stack
    · intro shortage flags
      have frame' := frame.trans (Serialize.host_status_frame current flags)
      apply Publish.capacity_cps e base code _ (result_mapping frame' result)
      apply Eventually.done
      refine Or.inl ⟨_, frame', Or.inr ⟨representable, ?_, rfl⟩⟩
      rw [← amount, ← capacity_preserved frame]
      exact shortage
  · intro empty current frame zero fits
    apply measured_emit_entry e base code s current size frame
    · change current.regs.r9.toBitVec.toNat = size.value
      rw [zero, empty]
      rfl
    · rw [← capacity_preserved frame]
      exact fits
    · exact stack

end SszX86.CodecSerialize

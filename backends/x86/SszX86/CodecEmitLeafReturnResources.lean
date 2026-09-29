import SszX86.CodecEmitLeafResources
import SszX86.EmitFinishResources

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

variable {s body final : MachineData} {base : Int64} {shape : Serialize.Desc}
  {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
  {r : SszX86.Codec.Footprint} {ra : BitVec 64}

private theorem saved_address (anchors : Emit.AtBody s body) (i : Nat) :
    body.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes (.primitive shape)) +
        BitVec.ofNat 64 (stackBytes (.primitive shape) - 48 + i) := by
  have enough := stackBytes_min (.primitive shape)
  rw [anchors.stack]
  bv_omega

theorem saved_protected (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra) :
    ∀ i < 56, ¬ Emit.BodyWritable body owned.call.measured.size.value
      (body.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i) := by
  intro i hi inside
  have enough := stackBytes_min (.primitive shape)
  rcases inside with output | result | scratch
  · obtain ⟨j, hj, equal⟩ := output
    apply owned.outputStack j (Nat.lt_of_lt_of_le hj owned.call.fits)
      (stackBytes (.primitive shape) - 48 + i) (by omega)
    rw [← anchors.output, ← saved_address anchors i]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := result
    apply owned.resultStack j (by omega) (stackBytes (.primitive shape) - 48 + i) (by omega)
    rw [← anchors.result, ← saved_address anchors i]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := scratch
    bv_omega

theorem status_protected (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra) :
    ∀ i < 4, ¬ Emit.BodyWritable body owned.call.measured.size.value
      (body.regs.rbx.toBitVec + 64 + BitVec.ofNat 64 i) := by
  intro i hi inside
  rcases inside with output | result | scratch
  · obtain ⟨j, hj, equal⟩ := output
    apply owned.outputResult j (Nat.lt_of_lt_of_le hj owned.call.fits) (64 + i) (by omega)
    rw [← anchors.output, ← anchors.result, BitVec.ofNat_add]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal.symm
  · obtain ⟨j, hj, equal⟩ := result
    bv_omega
  · have inside := body_stack_sub (desc := .primitive shape) anchors _ scratch
    obtain ⟨j, hj, equal⟩ := inside
    apply owned.resultStack (64 + i) (by omega) j (by omega)
    rw [← anchors.result, BitVec.ofNat_add]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal

theorem saved_current (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    Emit.SavedAt final.dmem final.regs.rsp.toBitVec (Emit.saved s ra) := by
  rw [post.stack]
  have initial : Emit.SavedAt body.dmem body.regs.rsp.toBitVec (Emit.saved s ra) := by
    rw [anchors.memory, anchors.stack]
    exact Emit.saved_at s ra owned.returnSlot
  apply Emit.savedAt_frame body.dmem final.dmem body.regs.rsp.toBitVec (Emit.saved s ra)
    (Emit.BodyWritable body (Serialize.emit shape value.toPrimitive).size) post.frame
  · simpa only [owned.call.primitive_valid.emitted_size] using saved_protected anchors owned
  · exact initial

theorem status_current (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    Large.Mapped final.dmem (final.regs.rbx.toBitVec + 64) 4 := by
  rw [post.result]
  apply Emit.frame_mapped body.dmem final.dmem
    (Emit.BodyWritable body (Serialize.emit shape value.toPrimitive).size) post.frame
  · simpa only [owned.call.primitive_valid.emitted_size] using status_protected anchors owned
  · rw [anchors.memory, anchors.result]
    exact Dispatch.saved_mapped s _ _ owned.statusMapped

theorem saved_status_apart (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    ∀ i < 56, ∀ j < 4,
      final.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i ≠
        final.regs.rbx.toBitVec + 64 + BitVec.ofNat 64 j := by
  intro i hi j hj equal
  have enough := stackBytes_min (.primitive shape)
  apply owned.resultStack (64 + j) (by omega)
    (stackBytes (.primitive shape) - 48 + i) (by omega)
  rw [← saved_address anchors i, ← anchors.result, BitVec.ofNat_add]
  simpa only [post.stack, post.result, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal.symm

theorem saved_success (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    Emit.SavedAt (Emit.successState final).dmem (Emit.successState final).regs.rsp.toBitVec
      (Emit.saved s ra) := by
  apply Emit.savedAt_frame final.dmem (Emit.successState final).dmem final.regs.rsp.toBitVec
    (Emit.saved s ra) (fun a => Emit.InSpan a (final.regs.rbx.toBitVec + 64) 4)
  · exact Emit.Bits.store_frame _ _ _ _
  · intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    exact saved_status_apart anchors owned post i hi j hj equal
  · exact saved_current anchors owned post

end SszX86.CodecEmit

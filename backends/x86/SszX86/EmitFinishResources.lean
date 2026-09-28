import SszX86.EmitBodyOwned

namespace SszX86.Emit
open SszNative.Serialize UintCodec BoolCodec

variable {s body final : MachineData} {base : Int64} {desc : Desc} {value : Value}
  {buffer ra : BitVec 64} {written : Nat}

theorem AtBody.saved_address (h : AtBody s body) (i : Nat) :
    body.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - 160 + BitVec.ofNat 64 (112 + i) := by
  rw [h.stack]
  bv_omega

theorem AtBody.saved_protected (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written) :
    ∀ i < 56, ¬ BodyWritable body written
      (body.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i) := by
  intro i hi inside
  rcases inside with output | result | scratch
  · obtain ⟨j, hj, equal⟩ := output
    apply owned.outputStack j hj (112 + i) (by omega)
    rw [← h.output, ← h.saved_address i]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := result
    apply owned.resultStack j (by omega) (112 + i) (by omega)
    rw [← h.result, ← h.saved_address i]
    exact equal.symm
  · obtain ⟨j, hj, equal⟩ := scratch
    bv_omega

theorem AtBody.status_protected (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written) :
    ∀ i < 4, ¬ BodyWritable body written (body.regs.rbx.toBitVec + 64 + BitVec.ofNat 64 i) := by
  intro i hi inside
  rcases inside with output | result | scratch
  · obtain ⟨j, hj, equal⟩ := output
    apply owned.outputResult j hj (64 + i) (by omega)
    rw [← h.output, ← h.result]
    rw [BitVec.ofNat_add]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal.symm
  · obtain ⟨j, hj, equal⟩ := result
    bv_omega
  · obtain ⟨j, hj, equal⟩ := scratch
    apply owned.resultStack (64 + i) (by omega) j (by omega)
    rw [← h.result, ← h.local_base]
    rw [BitVec.ofNat_add]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal

theorem AtBody.saved_current (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    SavedAt final.dmem final.regs.rsp.toBitVec (saved s ra) := by
  rw [post.stack]
  have initial : SavedAt body.dmem body.regs.rsp.toBitVec (saved s ra) := by
    rw [h.memory, h.stack]
    exact saved_at s ra owned.returnSlot
  apply savedAt_frame body.dmem final.dmem body.regs.rsp.toBitVec (saved s ra)
    (BodyWritable body (emit desc value).size) post.frame
  · simpa only [owned.valid.emitted_size] using h.saved_protected owned
  · exact initial

theorem AtBody.status_current (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    Large.Mapped final.dmem (final.regs.rbx.toBitVec + 64) 4 := by
  rw [post.result]
  apply frame_mapped body.dmem final.dmem (BodyWritable body (emit desc value).size) post.frame
  · simpa only [owned.valid.emitted_size] using h.status_protected owned
  · rw [h.memory, h.result]
    exact Dispatch.saved_mapped s _ _ owned.statusMapped

theorem AtBody.saved_status_apart (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    ∀ i < 56, ∀ j < 4,
      final.regs.rsp.toBitVec + 104 + BitVec.ofNat 64 i ≠
        final.regs.rbx.toBitVec + 64 + BitVec.ofNat 64 j := by
  intro i hi j hj equal
  apply owned.resultStack (64 + j) (by omega) (112 + i) (by omega)
  rw [← h.saved_address i, ← h.result]
  rw [BitVec.ofNat_add]
  simpa only [post.stack, post.result, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using equal.symm

theorem AtBody.saved_success (h : AtBody s body)
    (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    SavedAt (successState final).dmem (successState final).regs.rsp.toBitVec (saved s ra) := by
  apply savedAt_frame final.dmem (successState final).dmem final.regs.rsp.toBitVec (saved s ra)
    (fun a => InSpan a (final.regs.rbx.toBitVec + 64) 4)
  · intro a outside
    apply memmove_store_lookup_outside
    intro i hi equal
    exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩
  · intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    exact h.saved_status_apart owned post i hi j hj equal
  · exact h.saved_current owned post

end SszX86.Emit

import SszX86.CodecSerializeMemory
import SszX86.SerializeEdges

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec
open SszX86.Serialize.Publish

private theorem copied_saved (s original : MachineData) (image : Image)
    (flags : StatusFlags)
    (apart : Large.Disjoint s.regs.rbx.toBitVec s.regs.rsp.toBitVec 72 144)
    (saved : Serialize.SavedAt s.dmem s.regs.rsp.toBitVec original) :
    Serialize.SavedAt (copied s image flags).dmem s.regs.rsp.toBitVec original := by
  apply Serialize.savedAt_congr s.dmem _ s.regs.rsp.toBitVec original _ saved
  intro i hi
  apply copied_frame s image flags
  rintro (⟨j,hj,equal⟩ | ⟨j,hj,equal⟩)
  · apply apart j hj (96 + i) (by omega)
    bv_omega
  · bv_omega

private theorem copied_return (s : MachineData) (image : Image) (flags : StatusFlags)
    (ra : BitVec 64)
    (apart : Large.Disjoint s.regs.rbx.toBitVec s.regs.rsp.toBitVec 72 144)
    (returned : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 136) 8 =
      some (Int.ofBytes (wordBytes ra))) :
    Mem.loadInt (copied s image flags).dmem (s.regs.rsp.toBitVec + 136) 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  rw [Emit.frame_load s.dmem _ _ (copied_frame s image flags)]
  · exact returned
  · intro i hi
    rintro (⟨j,hj,equal⟩ | ⟨j,hj,equal⟩)
    · apply apart j hj (136 + i) (by omega)
      bv_omega
    · bv_omega

/-- The measurement-error arm executes the original copy and original RET. The
premises are observations at the actual measure-return cut, not a callee-exit
execution oracle. Original-entry composition supplies them from measurement. -/
theorem failure_return (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s original : MachineData) (image : Image) (reason : SszNative.Codec.Error)
    (ra : BitVec 64)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (stackBound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (resultBound : s.regs.rbx.toNat + 72 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rbx.toBitVec s.regs.rsp.toBitVec 72 144)
    (source : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (error : Codec.ErrorAt (widthLoad s.dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat reason)
    (safe : ∀ a, Codec.ErrorBorrows reason a →
      ¬ (Emit.InSpan a s.regs.rbx.toBitVec 72 ∨
        Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 16))
    (saved : Serialize.SavedAt s.dmem s.regs.rsp.toBitVec original)
    (returned : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 136) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (sp : s.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (rbp : s.regs.rbp = original.regs.rbp) (vectors : s.zmms = original.zmms) :
    Eventually (step e) (fun t =>
      Measure.ABI original ra t ∧
      Codec.ErrorAt (widthLoad t.1.dmem) s.regs.rbx.toNat reason ∧
      Emit.MemoryFrame s.dmem t.1.dmem (fun a =>
        Emit.InSpan a s.regs.rbx.toBitVec 72 ∨
        Emit.InSpan a (s.regs.rsp.toBitVec + 8#64) 16)) (s, base + 47) := by
  have localApart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 72 := by
    intro i hi j hj equal
    exact apart j hj i (by omega) equal.symm
  apply failure_cps e base code s image stack result stackBound localApart source
    (Codec.ErrorAt.image_nonzero source error)
  intro flags
  apply Serialize.epilogue_cps e base code.wrapper (copied s image flags) original ra
  · exact copied_saved s original image flags apart saved
  · exact copied_return s image flags ra apart returned
  · apply Eventually.done
    have anchors := Serialize.returnedState_abi (copied s image flags) original sp rbp
    rcases anchors with ⟨stackReturn, rbxReturn, r12Return, r13Return, r14Return,
      r15Return, rbpReturn⟩
    refine ⟨⟨rfl, stackReturn, rbxReturn, rbpReturn, r12Return, r13Return,
      r14Return, r15Return, vectors⟩, ?_, ?_⟩
    · exact copied_error s image flags reason source resultBound error safe
    · exact copied_frame s image flags

end SszX86.CodecSerialize.Publish

import SszArm.NatMulLargeReserve

namespace SszArm.NatMul

open Delimited (MemoryFrame Protected)
open SszNative (NatOperand NatArithmetic)
open UintCodec (widthLoad)

theorem large_failure_return (path : ReturnErrorPath) (s u v : ArmState) (base : BitVec 64)
    (left right : NatOperand) (owned : Owned s left right)
    (entry : EntryFrame s u) (middle : ArmState)
    (sizeFrame : ReserveSizeFrame u middle) (checksFrame : ReserveFrame middle v)
    (memory : MemoryFrame [((r (.GPR 31#5) u).toNat - 16, 16)] u v)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc v = base + BitVec.ofNat 64 path.start)
    (model : outcome s left right = NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)) :
    ∃ fuel t, run fuel v = t ∧ Post s t left right := by
  have sp := checksFrame.sp.trans sizeFrame.sp
  have output : r (.GPR 0#5) v = r (.GPR 0#5) s :=
    (checksFrame.registers _ (by decide)).trans ((sizeFrame.registers _ (by decide)).trans entry.output)
  have slotProtected : Protected [((r (.GPR 31#5) u).toNat - 16, 16)]
      (r (.GPR 31#5) u).toNat 96 := by
    have stack := (ReturnSpace.of_owned owned entry.saved).stack
    right
    intro span member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst span
    simp only [Prod.fst, Prod.snd]
    omega
  have saved := large_saved_frame owned entry.saved memory slotProtected sp
    ((checksFrame.registers _ (by decide)).trans (sizeFrame.registers _ (by decide)))
    (by intro reg low high; rw [checksFrame.vectors, sizeFrame.vectors])
  have space : ReturnSpace v (r (.GPR 0#5) v) := by
    rw [output]
    exact ReturnSpace.of_owned owned saved
  obtain ⟨execution, returned, image, tailFrame⟩ := error_return_run path s v base
    (checksFrame.code base (sizeFrame.code base (entry.code code)))
    (checksFrame.error.trans (sizeFrame.error.trans (entry.error.trans error)))
    (checksFrame.aligned (sizeFrame.aligned (entry.aligned aligned))) pc saved space
  have slotCover := (large_local_cover s (outcome s left right)).trans
    (large_slot_cover owned entry.sp 16 (by decide))
  have tailCover := (large_local_cover s (outcome s left right)).trans
    (large_error_cover owned saved.sp (r (.GPR 0#5) v) output (by rw [model]; rfl))
  have frame := (entry.memoryFor (outcome s left right)).trans
    ((slotCover.frame memory).trans (tailCover.frame tailFrame))
  have localArena : Protected (writesFor s (outcome s left right)) (r (.GPR 5#5) s).toNat 24 := by
    simpa only [writesFor, model, NatArithmetic.unchanged] using owned.arenaLocal
  have header := large_header_read owned frame localArena
  refine ⟨path.ops.length + 7, errorReturned path v base, execution, ?_⟩
  refine ⟨returned, ?_, ?_, ?_, frame,
    NatAdd.operand_preserved frame left owned.leftAt owned.leftOwned,
    NatAdd.operand_preserved frame right owned.rightAt owned.rightOwned, ?_, ?_⟩
  · simpa only [model, NatArithmetic.unchanged, output] using image
  · simp only [NatAdd.WrittenAt, model, NatArithmetic.unchanged]
    intro reservation impossible
    cases impossible
  · rw [header 16 (by decide), model]
    rfl
  · simpa only [BitVec.add_zero] using header 0 (by decide)
  · exact header 8 (by decide)

end SszArm.NatMul

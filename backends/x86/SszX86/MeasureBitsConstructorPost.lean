import SszX86.MeasureBitsConstructorResources
import SszX86.MeasureBitsPost
import SszX86.MeasureBitsOutputMemory

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem ConstructorResources.published {s before after : MachineData} {desc : Desc} {bits : Packed}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : ConstructorResources s bits address capacity used before)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (sp : after.regs.rsp = s.regs.rsp) (vectors : after.zmms = s.zmms)
    (observed : ResultAt (widthLoad after.dmem) s.regs.rbx.toNat
      (measure desc (.bits bits) (arenaState address capacity used)).result)
    (published : MemoryFrame before.dmem after.dmem
      (ResultWrites s.regs.rbx.toBitVec (measure desc (.bits bits) (arenaState address capacity used)))) :
    BodyPost s desc (.bits bits) buffer address capacity used after := by
  have fullPub := frame_mono _ _ _ _ published
    (resultWrites_span s.regs.rbx.toBitVec (measure desc (.bits bits) (arenaState address capacity used)))
  apply body_post_of_resources s after desc (.bits bits) buffer address capacity used owned sp vectors observed
  · rw [model, publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 16 (by decide)]
    exact resources.cursor
  · constructor
    · have same := publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 0 (by decide)
      simpa only [Nat.add_zero] using same.trans resources.header.1
    · rw [publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 8 (by decide)]
      exact resources.header.2
  · rw [model]
    exact publication_calls s desc (.bits bits) buffer address capacity used owned _ _ _
      (two_call_geometry bits address capacity used) resources.calls fullPub
  · intro a safe
    exact (published a (fun writes => safe (Or.inl writes))).trans
      (resources.frame a (by
        intro writes
        apply safe
        rw [model]
        exact Or.inr writes))
  · rw [model]
    exact two_call_geometry bits address capacity used

theorem constructor_plan_post (s before after : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64) (actual : NatOperand)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : ConstructorResources s bits address capacity used before)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (success : (encodedCall bits address capacity used).result = .ok actual)
    (memory : after.dmem = planMem before.dmem s.regs.rbx.toBitVec actual.pointer actual.payload)
    (sp : after.regs.rsp = s.regs.rsp) (vectors : after.zmms = s.zmms) :
    BodyPost s desc (.bits bits) buffer address capacity used after := by
  have published : MemoryFrame before.dmem after.dmem
      (ResultWrites s.regs.rbx.toBitVec (measure desc (.bits bits) (arenaState address capacity used))) := by
    rw [memory, model]
    intro a outside
    apply plan_frame before.dmem s.regs.rbx.toBitVec actual.pointer actual.payload a
    simpa only [ResultWrites, success, Except.mapError] using outside
  have fullPub := frame_mono _ _ _ _ published
    (resultWrites_span s.regs.rbx.toBitVec (measure desc (.bits bits) (arenaState address capacity used)))
  have observed := resources.observed
  rw [success] at observed
  have actualAfter := publication_operand s desc (.bits bits) buffer address capacity used owned
    before.dmem after.dmem (listCalls bits address capacity used)
    (two_call_geometry bits address capacity used) actual (by
      intro a borrowed
      have success' : (NatArithmetic.fromWide address.toNat capacity.toNat
          (countUsed bits address capacity used).toNat (encodedWide bits.count)).result = .ok actual := by
        simpa only [encoded_call_eq] using success
      obtain ⟨call, member, r, allocated, inside⟩ := from_wide_borrowed address capacity
        (countUsed bits address capacity used) (encodedWide bits.count) actual success' a borrowed
      have same : call = encodedCall bits address capacity used := by
        simpa only [encoded_call_eq, List.mem_singleton] using member
      subst call
      exact ⟨encodedCall bits address capacity used, by simp [listCalls], r, allocated, inside⟩)
    observed.1.2.2 fullPub
  apply resources.published owned model sp vectors _ published
  rw [model, success, Except.mapError, memory]
  exact plan_reads _ _ actual (by simpa only [memory] using actualAfter)

theorem constructor_scratch_post (s before loaded after : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64) (padding : BitVec 32)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : ConstructorResources s bits address capacity used before)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩)
    (failed : (encodedCall bits address capacity used).result = .error .scratchExhausted)
    (loadedMemory : loaded.dmem = before.dmem) (loadedOut : loaded.regs.rbx = s.regs.rbx)
    (tag : loaded.regs.rcx.toBitVec = 1) (zero : loaded.regs.rax.toBitVec = 0)
    (reason : loaded.regs.rdx.toBitVec.setWidth 32 = 32768)
    (memory : after.dmem = propagatedMem loaded (scratchTail padding))
    (sp : after.regs.rsp = s.regs.rsp) (vectors : after.zmms = s.zmms) :
    BodyPost s desc (.bits bits) buffer address capacity used after := by
  have fullPub : MemoryFrame before.dmem after.dmem (fun a => InSpan a s.regs.rbx.toBitVec 72) := by
    rw [memory, ← loadedMemory]
    simpa only [loadedOut] using propagated_frame loaded (scratchTail padding)
  have published : MemoryFrame before.dmem after.dmem
      (ResultWrites s.regs.rbx.toBitVec (measure desc (.bits bits) (arenaState address capacity used))) := by
    apply frame_mono _ _ _ _ fullPub
    rintro a ⟨i, hi, rfl⟩
    rw [model, failed]
    simp only [ResultWrites, Except.mapError, listCalls, List.length_cons, List.length_nil,
      Nat.reduceAdd, true_and]
    by_cases lower : i < 68
    · exact Or.inl ⟨i, lower, rfl⟩
    · right
      refine ⟨i - 68, by omega, ?_⟩
      bv_omega
  apply resources.published owned model sp vectors _ published
  rw [model, failed, Except.mapError, memory]
  simpa only [ResultAt, loadedOut] using propagated_scratch_reads loaded padding tag zero reason

end SszX86.Measure.Bits

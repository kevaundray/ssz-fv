import SszX86.MeasureBitsPublication
import SszX86.MeasureBitsCountCommit
import SszX86.MeasureBitsVectorNoAlloc

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem first_call_geometry (bits : Packed) (address capacity used : BitVec 64)
    (call : NatArithmetic.Outcome NatOperand)
    (member : call ∈ [countCall bits address capacity used])
    (r : Arena.Reservation) (allocated : call.allocation = some r) :
    address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 8 * call.written.length ≤ address.toNat + capacity.toNat := by
  have same : call = countCall bits address capacity used := by simpa only [List.mem_singleton] using member
  subst call
  have geometry := wide_allocation_geometry address.toNat capacity.toNat used.toNat bits.count r allocated
  rw [show (countCall bits address capacity used).written = _ from geometry.2.1]
  exact ⟨geometry.2.2.1, by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using geometry.2.2.2.1⟩

theorem CountPrefix.inputs {s t : MachineData} {desc : Desc} {bits : Packed}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t) :
    DescAt t.dmem s.regs.rsi.toBitVec desc ∧ ValueAt t.dmem s.regs.r14.toBitVec buffer (.bits bits) := by
  apply original_inputs s desc (.bits bits) buffer address capacity used owned
  apply frame_mono _ _ _ _ resources.frame
  intro a writes
  rcases writes with allocation | ⟨_, cursor⟩ | work
  · obtain ⟨call, member, r, allocated, inside⟩ := allocation
    have geometry := first_call_geometry bits address capacity used call member r allocated
    exact Or.inr (Or.inr (Or.inl (allocation_in_free address used capacity r.pointer
      (8 * call.written.length) geometry.1 geometry.2 a inside)))
  · exact Or.inr (Or.inl cursor)
  · exact Or.inr (Or.inr (Or.inr work))

theorem first_scratch_post (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨.error (.arithmetic .scratchExhausted), used.toNat, [countCall bits address capacity used]⟩)
    (unallocated : (countCall bits address capacity used).allocation = none)
    (memory : t.dmem = NatAdd.errorMem s.dmem s.regs.rbx.toBitVec)
    (sp : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms) :
    BodyPost s desc (.bits bits) buffer address capacity used t := by
  apply single_unallocated_post s t desc (.bits bits) buffer address capacity used _ _
    owned model unallocated sp vectors
  · rw [memory]
    exact NatAdd.error_reads _ _
  · rw [memory]
    exact scratch_frame _ _

/-- A failing bound retains the first successful count allocation, regardless of
logical cap padding and without constructing the encoded-width operand. -/
theorem list_limit_post (s before after : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64) (cap actual : NatOperand)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used before)
    (counted : (countCall bits address capacity used).result = .ok actual)
    (capStored : cap.At (widthLoad before.dmem))
    (capBorrowed : ∀ a, Emit.NatBorrowed cap a → BodyBorrowed s desc (.bits bits) buffer a)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨.error (.limit cap actual), (countCall bits address capacity used).used,
        [countCall bits address capacity used]⟩)
    (memory : after.dmem = limitMem before.dmem s.regs.rbx.toBitVec
      cap.pointer cap.payload actual.pointer actual.payload)
    (sp : after.regs.rsp = s.regs.rsp) (vectors : after.zmms = s.zmms) :
    BodyPost s desc (.bits bits) buffer address capacity used after := by
  have pub := limit_frame before.dmem s.regs.rbx.toBitVec cap.pointer cap.payload actual.pointer actual.payload
  have fullPub : MemoryFrame before.dmem after.dmem (fun a => InSpan a s.regs.rbx.toBitVec 72) := by
    rw [memory]
    apply frame_mono _ _ _ _ pub
    rintro a ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩
  have capAfter : cap.At (widthLoad after.dmem) := by
    apply operand_frame _ _ _ fullPub cap _ capStored
    intro a borrowed written
    exact owned.readonly a (capBorrowed a borrowed) (Or.inl written)
  have actualBefore := resources.operand owned actual counted
  have actualAfter := publication_operand s desc (.bits bits) buffer address capacity used owned
    before.dmem after.dmem [countCall bits address capacity used]
    (first_call_geometry bits address capacity used) actual
    (from_wide_borrowed address capacity used bits.count actual counted) actualBefore fullPub
  apply body_post_of_resources s after desc (.bits bits) buffer address capacity used owned sp vectors
  · rw [model, memory]
    exact limit_reads before.dmem s.regs.rbx.toBitVec cap actual
      (by simpa only [memory] using capAfter) (by simpa only [memory] using actualAfter)
  · rw [model, publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 16 (by decide)]
    simpa only [UInt64.toNat_toBitVec, count_used_nat] using resources.arena.2.2
  · constructor
    · have same := publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 0 (by decide)
      simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using same.trans resources.arena.1
    · rw [publication_header s desc (.bits bits) buffer address capacity used owned _ _ fullPub 8 (by decide)]
      exact resources.arena.2.1
  · rw [model]
    exact publication_calls s desc (.bits bits) buffer address capacity used owned _ _ _
      (first_call_geometry bits address capacity used) resources.calls fullPub
  · rw [model]
    intro a safe
    have publish : after.dmem.get? a = before.dmem.get? a := by
      rw [memory]
      apply pub a
      intro inside
      exact safe (Or.inl (Or.inl inside))
    exact publish.trans (resources.frame a (fun writes => safe (Or.inr writes)))
  · rw [model]
    exact first_call_geometry bits address capacity used

end SszX86.Measure.Bits

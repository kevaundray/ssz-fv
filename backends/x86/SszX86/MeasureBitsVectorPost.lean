import SszX86.MeasureBitsVectorAllocation
import SszX86.MeasureBitsPost
import SszX86.MeasureNoAlloc

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

private theorem output_header_load (s : MachineData) (before after : DataMem)
    (off : Nat) (within : off + 8 ≤ 24)
    (separated : Large.Disjoint s.regs.rbx.toBitVec s.regs.rcx.toBitVec 72 24)
    (frame : MemoryFrame before after (fun a => InSpan a s.regs.rbx.toBitVec 68)) :
    widthLoad after (s.regs.rcx.toNat + off) 8 = widthLoad before (s.regs.rcx.toNat + off) 8 := by
  unfold widthLoad
  rw [← UInt64.toNat_toBitVec, width_address]
  congr 1
  apply frame_load_window before after _ frame s.regs.rcx.toBitVec off 8 24 within
  intro a inside written
  obtain ⟨i, hi, equal⟩ := inside
  obtain ⟨j, hj, same⟩ := written
  exact separated j (by omega) i hi (same.symm.trans equal)

/-- A committed Scope payload owns both words of the materialized count after
publication. Neither the earlier commit nor the original expected operand is lost. -/
theorem vector_allocated_scope_post (s t : MachineData) (expected : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitVector expected) (.bits bits) buffer address capacity used)
    (mismatch : expected.value ≠ bits.count.toNat)
    (large : ¬ bits.count.toNat < 2^64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (memory : t.dmem = scopeMem (vectorCommitMem s r bits.count) s.regs.rbx.toBitVec
      expected.pointer expected.payload (BitVec.ofNat 64 r.pointer) 2#64)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms) :
    BodyPost s (.bitVector expected) (.bits bits) buffer address capacity used t := by
  let actual : NatOperand := .large (BitVec.ofNat 64 r.pointer)
    [bits.count.setWidth 64, (bits.count >>> 64).setWidth 64]
  have callModel := NatFromU128.result_model_success address capacity used bits.count large r reserved
  change NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count = _ at callModel
  have model : measure (.bitVector expected) (.bits bits) (arenaState address capacity used) =
      ⟨.error (.scope expected actual), r.used,
        [NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count]⟩ := by
    simp only [Serialize.measure, mismatch, ↓reduceIte, Serialize.bind, fromWide, arenaState, callModel,
      Except.mapError, unchanged, List.append_nil, actual]
  have geometry := reserve_geometry s _ _ buffer address capacity used owned r reserved
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
  have pub := scope_frame (vectorCommitMem s r bits.count) s.regs.rbx.toBitVec
    expected.pointer expected.payload (BitVec.ofNat 64 r.pointer) 2#64
  have actualBefore := vector_commit_operand s expected bits buffer address capacity used owned r reserved
  have actualAfter : actual.At (widthLoad t.dmem) := by
    rw [memory]
    apply operand_frame _ _ _ pub actual _ actualBefore
    intro a inside written
    have allocatedInside : InSpan a (BitVec.ofNat 64 r.pointer) 16 := by
      simpa only [actual, Emit.NatBorrowed, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using inside
    obtain ⟨i, hi, eqi⟩ := allocatedInside
    obtain ⟨j, hj, eqj⟩ := written
    have apart : Body.Apart r.pointer 16 s.regs.rbx.toNat 72 := by
      have separated := owned.freeResult
      unfold Body.Apart at separated ⊢
      omega
    have bytesApart := Body.apart_bytes (BitVec.ofNat 64 r.pointer) s.regs.rbx.toBitVec 16 72
      (by rw [pointerNat]; exact geometry.2.2.2.2.2.1) owned.resultBound
      (by simpa only [pointerNat, UInt64.toNat_toBitVec] using apart)
    exact bytesApart i hi j (by omega) (eqi.symm.trans eqj)
  have expectedBefore := (vector_commit_inputs s expected bits buffer address capacity used owned r reserved).1.2.2.2
  have expectedAfter : expected.At (widthLoad t.dmem) := by
    rw [memory]
    apply operand_frame _ _ _ pub expected _ expectedBefore
    intro a borrowed written
    apply owned.readonly a (Or.inr (Or.inr (Or.inl borrowed)))
    exact Or.inl (by obtain ⟨i, hi, rfl⟩ := written; exact ⟨i, by omega, rfl⟩)
  have header := vector_commit_arena s expected bits buffer address capacity used owned r reserved
  apply body_post_of_resources s t _ _ buffer address capacity used owned stack vectors
  · rw [model, memory]
    exact scope_reads _ _ expected actual
      (by simpa only [memory, actual, NatOperand.pointer, NatOperand.payload,
        List.length_cons, List.length_nil, Nat.reduceAdd] using expectedAfter)
      (by simpa only [memory, actual, NatOperand.pointer, NatOperand.payload,
        List.length_cons, List.length_nil, Nat.reduceAdd] using actualAfter)
  · rw [model, memory, output_header_load s _ _ 16 (by decide) owned.resultHeader pub]
    exact header.2.2
  · rw [memory]
    constructor
    · have keep := output_header_load s _ _ 0 (by decide) owned.resultHeader pub
      simpa only [Nat.add_zero] using keep.trans header.1
    · exact (output_header_load s _ _ 8 (by decide) owned.resultHeader pub).trans header.2.1
  · rw [model]
    intro call member reservation allocated
    have sameCall : call = NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count := by
      simpa only [List.mem_singleton] using member
    subst call
    rw [callModel] at allocated ⊢
    cases Option.some.inj allocated
    simpa only [pointerNat] using actualAfter.2.2.2
  · rw [memory]
    apply frame_mono _ _ _ _ (frame_trans _ _ _ _ _ (vector_commit_frame s r bits.count) pub)
    intro a written
    rw [model]
    rcases written with (cursor | allocation) | publication
    · right; right; left
      refine ⟨?_, cursor⟩
      exact ⟨NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count,
        by simp, r, by rw [callModel]⟩
    · right; left
      refine ⟨NatArithmetic.fromWide address.toNat capacity.toNat used.toNat bits.count,
        by simp, r, ?_, ?_⟩
      · rw [callModel]
      · simpa only [callModel, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using allocation
    · left
      exact Or.inl publication
  · exact vector_call_geometry expected bits (arenaState address capacity used)

end SszX86.Measure.Bits

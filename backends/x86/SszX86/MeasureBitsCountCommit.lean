import SszX86.MeasureBitsCountPrefix
import SszX86.MeasureBitsVectorAllocation
import SszX86.MeasureBitsStores

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- The shared exact commit with any previously executed local spills. -/
theorem count_prefix_committed (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (large : ¬ bits.count.toNat < 2^64) (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (m : DataMem)
    (localFrame : MemoryFrame s.dmem m (fun a => InSpan a (s.regs.rsp.toBitVec - 16) 232))
    (mapping : MappedExtension s.dmem m)
    (memory : t.dmem = vectorCommitMem {s with dmem := m} r bits.count)
    (sp : t.regs.rsp = s.regs.rsp) (outReg : t.regs.rbx = s.regs.rbx)
    (vectors : t.zmms = s.zmms) : CountPrefix s bits address capacity used t := by
  have geometry := reserve_geometry s desc (.bits bits) buffer address capacity used owned r reserved
  have model := NatFromU128.result_model_success address capacity used bits.count large r reserved
  change countCall bits address capacity used = _ at model
  have allocated : (countCall bits address capacity used).allocation = some r := by
    rw [model]
  have written : (countCall bits address capacity used).written =
      [bits.count.setWidth 64, (bits.count >>> 64).setWidth 64] := by
    rw [model]
  have usedEq : (countCall bits address capacity used).used = r.used := by
    rw [model]
  have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
  have payloadHeader : Body.Apart r.pointer 16 s.regs.rcx.toNat 24 := by
    have separated := owned.freeHeader
    unfold Body.Apart at separated ⊢
    omega
  refine ⟨?_, ?_, ?_, ?_, sp, outReg, vectors⟩
  · intro a safe
    rw [memory]
    have committed : (vectorCommitMem {s with dmem := m} r bits.count).get? a = m.get? a := by
      apply vector_commit_frame {s with dmem := m} r bits.count a
      rintro (cursor | payload)
      · exact safe (Or.inr (Or.inl ⟨⟨_, by simp only [List.mem_singleton], r, allocated⟩, cursor⟩))
      · apply safe
        left
        refine ⟨_, by simp only [List.mem_singleton], r, allocated, ?_⟩
        simpa only [written, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using payload
    exact committed.trans (localFrame a (fun inside => safe (Or.inr (Or.inr inside))))
  · rw [memory]
    intro p n hm
    unfold vectorCommitMem NatFromU128.commitMem
    repeat' first | exact mapping p n hm | apply Large.mapped_store
  · rw [memory]
    have keep (off : Nat) (within : off + 8 ≤ 16) :
        widthLoad (vectorCommitMem {s with dmem := m} r bits.count) (s.regs.rcx.toNat + off) 8 =
          widthLoad s.dmem (s.regs.rcx.toNat + off) 8 := by
      apply Eq.trans (b := widthLoad m (s.regs.rcx.toNat + off) 8)
      · apply NatFromU128.commit_width_preserved
        · have bound := owned.headerBound; omega
        · exact owned.headerBound
        · rw [pointerNat]; exact geometry.2.2.2.2.2.1
        · unfold Body.Apart
          simp only [UInt64.toNat_toBitVec]
          omega
        · rw [pointerNat]
          unfold Body.Apart at payloadHeader ⊢
          omega
      · exact local_header_keep s desc (.bits bits) buffer address capacity used owned _ _ localFrame off (by omega)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [UInt64.toNat_toBitVec, Nat.add_zero] using (keep 0 (by decide)).trans owned.arena.1
    · simpa only [UInt64.toNat_toBitVec] using (keep 8 (by decide)).trans owned.arena.2.1
    · have cursor := NatFromU128.commit_cursor m s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer)
        (BitVec.ofNat 64 r.used) (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)
        owned.headerBound (by rw [pointerNat]; exact geometry.2.2.2.2.2.1)
        (by rw [pointerNat]; exact payloadHeader.symm)
      simpa only [vectorCommitMem, count_used_nat, usedEq, UInt64.toNat_toBitVec,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt geometry.2.2.2.2.2.2] using cursor
  · intro call member r' allocated'
    have same : call = countCall bits address capacity used := by simpa only [List.mem_singleton] using member
    subst call
    have reservationEq : r' = r := by rw [allocated] at allocated'; exact Option.some.inj allocated' |>.symm
    subst r'
    rw [memory, written]
    have limbs := NatFromU128.commit_words m s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer)
      (BitVec.ofNat 64 r.used) (bits.count.setWidth 64) ((bits.count >>> 64).setWidth 64)
      (by rw [pointerNat]; exact geometry.2.2.2.2.2.1)
    simpa only [vectorCommitMem, pointerNat] using limbs

theorem CountPrefix.operand {s t : MachineData} {desc : Desc} {bits : Packed}
    {buffer address capacity used : BitVec 64}
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (actual : NatOperand) (success : (countCall bits address capacity used).result = .ok actual) :
    actual.At (widthLoad t.dmem) := by
  by_cases small : bits.count.toNat < 2^64
  · have model : countCall bits address capacity used = _ :=
      NatFromU128.result_model_small address capacity used bits.count small
    rw [model] at success
    simp only [NatArithmetic.unchanged, Except.ok.injEq] at success
    subst actual
    trivial
  cases reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 with
  | none =>
    have model : countCall bits address capacity used = _ :=
      NatFromU128.result_model_failure address capacity used bits.count small reserved
    rw [model] at success
    cases success
  | some r =>
    have model := NatFromU128.result_model_success address capacity used bits.count small r reserved
    change countCall bits address capacity used = _ at model
    rw [model] at success
    simp only [Except.ok.injEq] at success
    subst actual
    have geometry := reserve_geometry s desc (.bits bits) buffer address capacity used owned r reserved
    have pointerNat : (BitVec.ofNat 64 r.pointer).toNat = r.pointer := Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [pointerNat] using geometry.1
    · simpa only [pointerNat] using geometry.2.1
    · simpa only [pointerNat, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
        using geometry.2.2.2.2.2.1
    · have words := resources.calls (countCall bits address capacity used)
        (by simp only [List.mem_singleton]) r (by rw [model])
      simpa only [model, pointerNat] using words

end SszX86.Measure.Bits

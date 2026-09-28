import SszX86.MeasureBitsConstructorPost
import SszX86.MeasureBitsReturned
import SszX86.MeasureOutput
import SszX86.BitVectorLoad

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem stack_result_load (s t : MachineData) (off byteCount : Nat)
    (v : BitVec (8 * byteCount)) (sp : t.regs.rsp = s.regs.rsp)
    (stored : widthLoad t.dmem (s.regs.rsp.toNat + 24 + off) byteCount = some v.toNat) :
    Mem.loadInt t.dmem (t.regs.rsp.toBitVec + BitVec.ofNat 64 (24 + off)) byteCount =
      some (v.toNat : Int) := by
  have raw := widthLoad_eq t.dmem (s.regs.rsp.toNat + 24 + off) byteCount v.toNat stored
  simpa only [sp, ← UInt64.toNat_toBitVec, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_assoc] using raw

theorem encoded_result_cases (bits : Packed) (address capacity used : BitVec 64) :
    (∃ actual, (encodedCall bits address capacity used).result = .ok actual) ∨
      (encodedCall bits address capacity used).result = .error .scratchExhausted := by
  unfold encodedCall NatArithmetic.fromWide
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inr rfl
    · exact Or.inl ⟨_, rfl⟩

theorem constructor_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (desc : Desc) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc (.bits bits) buffer address capacity used)
    (resources : ConstructorResources s bits address capacity used t)
    (model : measure desc (.bits bits) (arenaState address capacity used) =
      ⟨(encodedCall bits address capacity used).result.mapError Error.arithmetic,
        (encodedCall bits address capacity used).used, listCalls bits address capacity used⟩) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s desc (.bits bits) buffer address capacity used u.1)
      (t, base + 2119) := by
  have resultMapped : OutputMapped t := by
    simpa only [OutputMapped, resources.output] using resources.mapping _ _ owned.resultMapped
  rcases encoded_result_cases bits address capacity used with ⟨actual, success⟩ | failed
  · have stored := resources.observed
    rw [success] at stored
    apply from_wide_returned_cps e base hc t 0 actual.pointer actual.payload
    · exact stack_result_load s t 64 4 0 resources.stack stored.2
    · simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat] using
        stack_result_load s t 0 8 actual.pointer resources.stack (by simpa only [Nat.add_zero] using stored.1.1)
    · exact stack_result_load s t 8 8 actual.payload resources.stack stored.1.2.1
    intro flags
    apply success_cps e base hc
    · exact resultMapped
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    apply constructor_plan_post s t _ desc bits buffer address capacity used actual owned resources model success
    · simp only [fromWideLoaded, UInt64.toBitVec_ofBitVec, resources.output]
    · exact resources.stack
    · exact resources.vectors
  · have stored := resources.observed
    rw [failed] at stored
    obtain ⟨tag, zero, w2, w3, w4, w5, w6, w7, reason⟩ := stored
    have paddingMap := resources.mapping _ _ (body_work_mapped s desc (.bits bits)
      buffer address capacity used owned 92 4 (by decide))
    have paddingRead := Large.mapped_load t.dmem (s.regs.rsp.toBitVec + 92) 4 0 4 paddingMap (by decide)
    obtain ⟨padding, paddingStored⟩ := BitVector.mapped_word t.dmem
      (s.regs.rsp.toBitVec + 92) 4 (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using paddingRead)
    apply from_wide_returned_cps e base hc t 32768 1 0
    · exact stack_result_load s t 64 4 32768 resources.stack reason
    · simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat] using
        stack_result_load s t 0 8 1 resources.stack (by with_unfolding_all exact tag)
    · exact stack_result_load s t 8 8 0 resources.stack zero
    intro flags
    apply propagate_cps e base hc _ (scratchTail padding)
    · exact resultMapped
    · intro i hi j hj equal
      apply owned.resultStack j hj (16 + i) (by omega)
      simp only [fromWideLoaded, resources.stack, resources.output] at equal
      have location : s.regs.rsp.toBitVec + BitVec.ofNat 64 i =
          s.regs.rsp.toBitVec - 16 + BitVec.ofNat 64 (16 + i) := by
        rw [BitVec.ofNat_add]
        bv_omega
      exact equal.symm.trans location
    · exact stack_result_load s t 16 8 0 resources.stack w2
    · exact stack_result_load s t 24 8 0 resources.stack w3
    · exact stack_result_load s t 32 8 0 resources.stack w4
    · exact stack_result_load s t 40 8 0 resources.stack w5
    · exact stack_result_load s t 48 8 0 resources.stack w6
    · exact stack_result_load s t 56 8 0 resources.stack w7
    · simp only [fromWideLoaded, resources.stack, scratchTail]
      with_unfolding_all exact paddingStored
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    apply constructor_scratch_post s t (fromWideLoaded t 32768 1 0 flags) _ desc bits
      buffer address capacity used padding owned resources model failed
    · rfl
    · exact resources.output
    · rfl
    · rfl
    · rfl
    · rfl
    · exact resources.stack
    · exact resources.vectors

end SszX86.Measure.Bits

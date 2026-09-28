import SszX86.MeasureBitsCompareResources

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem progressive_bound_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (cap actual : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.progressiveBitList (some cap)) (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (counted : (countCall bits address capacity used).result = .ok actual)
    (actualPointer : t.regs.r13.toBitVec = actual.pointer)
    (actualPayload : t.regs.rsi.toBitVec = actual.payload)
    (capPointer : t.regs.rbp.toBitVec = cap.pointer)
    (capPayload : t.regs.r12.toBitVec = cap.payload)
    (header : t.regs.rcx = s.regs.rcx)
    (low : t.regs.r15.toBitVec = bits.count.setWidth 64)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧
        BodyPost s (.progressiveBitList (some cap)) (.bits bits) buffer address capacity used u.1)
      (t, base + 1524) := by
  have preparedResources : CountPrefix s bits address capacity used (progressiveCompareReady t) := by
    apply resources.stack_extension owned
    · simp only [progressiveCompareReady, progressiveCompareMem, resources.stack]
      with_unfolding_all exact spill_frame s t.dmem t.regs.rcx.toBitVec t.regs.rsi.toBitVec
    · exact spill_mapped _ _ _ _
    · rfl
    · rfl
    · rfl
  have capStored := (preparedResources.inputs owned).1.2.2.2.2
  have capBorrowed : ∀ a, Emit.NatBorrowed cap a →
      BodyBorrowed s (.progressiveBitList (some cap)) (.bits bits) buffer a := by
    intro a borrowed
    exact Or.inr (Or.inr (Or.inl borrowed))
  have saved := spill_reads t.dmem t.regs.rsp.toBitVec t.regs.rcx.toBitVec t.regs.rsi.toBitVec
  apply progressive_compare_prepare_cps e base hc
  · simpa only [resources.stack, BitVec.add_zero] using resources.mapping _ _
      (body_work_mapped s _ _ buffer address capacity used owned 0 24 (by decide))
  apply progressive_compare_cps e base hc helpers (progressiveCompareReady t) actual.value cap.value
  · exact constructor_return_mapped s _ _ _ buffer address capacity used owned
      preparedResources.mapping preparedResources.stack
  · simpa only [progressiveCompareReady, actualPointer, actualPayload] using
      count_pair_at_call s _ _ bits buffer address capacity used (base + 1548).toBitVec
        actual owned preparedResources counted
  · simpa only [progressiveCompareReady, capPointer, capPayload] using
      bound_pair_at_call s _ _ bits buffer address capacity used (base + 1548).toBitVec
        cap owned preparedResources capStored capBorrowed
  rintro ⟨u, pc⟩ returned
  have pcEq : pc = base + 1548 := by simpa using returned.1
  subst pc
  have afterResources : CountPrefix s bits address capacity used u :=
    compare_count_prefix s (progressiveCompareReady t) (u, base + 1548) _ bits
      buffer address capacity used (base + 1548).toBitVec (compare actual.value cap.value) owned preparedResources returned
  have keep := returned.2.2.2.2.2
  have rBP : u.regs.rbp.toBitVec = t.regs.rbp.toBitVec := keep .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
  have r12 : u.regs.r12.toBitVec = t.regs.r12.toBitVec := keep .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r13 : u.regs.r13.toBitVec = t.regs.r13.toBitVec := keep .r13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r14 : u.regs.r14.toBitVec = t.regs.r14.toBitVec := keep .r14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r15 : u.regs.r15.toBitVec = t.regs.r15.toBitVec := keep .r15 (by decide) (by decide) (by decide) (by decide) (by decide)
  have headerSaved := compare_spill_read (progressiveCompareReady t) (u, base + 1548)
    (base + 1548).toBitVec (compare actual.value cap.value) 8 s.regs.rcx.toBitVec (by decide)
    (by
      have stored := saved.1
      simp only [header] at stored
      simp only [progressiveCompareReady, progressiveCompareMem, header]
      with_unfolding_all exact stored) returned
  have payloadSaved := compare_spill_read (progressiveCompareReady t) (u, base + 1548)
    (base + 1548).toBitVec (compare actual.value cap.value) 16 actual.payload (by decide)
    (by
      have stored := saved.2
      simp only [actualPayload] at stored
      simp only [progressiveCompareReady, progressiveCompareMem, actualPayload]
      with_unfolding_all exact stored) returned
  apply progressive_compare_reload_cps e base hc u s.regs.rcx.toBitVec actual.payload _ headerSaved payloadSaved
  apply progressive_compared_cps e base hc _ (compare actual.value cap.value) _
  · exact returned.2.1
  intro flags
  by_cases over : compare actual.value cap.value = .gt
  · simp only [over, ↓reduceIte]
    have rejected : ¬ actual.value ≤ cap.value := by have h := Nat.compare_eq_gt.mp over; omega
    apply progressive_limit_cps e base hc
    · simpa only [OutputMapped, afterResources.output] using afterResources.mapping _ _ owned.resultMapped
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    apply list_limit_post s _ _ (.progressiveBitList (some cap)) bits buffer address capacity used
      cap actual owned (afterResources.restate rfl rfl rfl rfl) counted
    · exact (afterResources.inputs owned).1.2.2.2.2
    · exact capBorrowed
    · exact list_bound_failure cap actual bits address capacity used counted rejected
    · simp only [afterResources.output, rBP, r12, r13, capPointer, capPayload, actualPointer]
    · exact afterResources.stack
    · exact afterResources.vectors
  · simp only [over, ↓reduceIte]
    have fits : actual.value ≤ cap.value := by
      by_cases fits : actual.value ≤ cap.value
      · exact fits
      · exact False.elim (over (Nat.compare_eq_gt.mpr (by omega)))
    apply progressive_continue_cps e base hc helpers s _ (.progressiveBitList (some cap)) bits
      buffer address capacity used owned
    · exact afterResources.restate rfl rfl rfl rfl
    · exact list_bound_pass (some cap) actual bits address capacity used counted (by
        intro other equal
        cases equal
        exact fits)
    · simp only [UInt64.ofBitVec_toBitVec]
    · exact r15.trans low
    · exact r14.trans high

end SszX86.Measure.Bits

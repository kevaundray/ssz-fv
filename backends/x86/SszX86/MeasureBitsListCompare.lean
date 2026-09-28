import SszX86.MeasureBitsCompareResources

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

theorem list_bound_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s t : MachineData) (cap actual : NatOperand) (bits : Packed)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s (.bitList cap) (.bits bits) buffer address capacity used)
    (resources : CountPrefix s bits address capacity used t)
    (counted : (countCall bits address capacity used).result = .ok actual)
    (actualPointer : t.regs.rbp.toBitVec = actual.pointer)
    (actualPayload : t.regs.r15.toBitVec = actual.payload)
    (capPointer : t.regs.r13.toBitVec = cap.pointer)
    (capPayload : t.regs.r12.toBitVec = cap.payload)
    (high : t.regs.r14.toBitVec = (bits.count >>> 64).setWidth 64)
    (savedLow : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 16) 8 = some ((bits.count.setWidth 64).toNat : Int))
    (savedHeader : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 8) 8 = some (s.regs.rcx.toBitVec.toNat : Int)) :
    Eventually (step e)
      (fun u => u.2 = base + 3335 ∧ BodyPost s (.bitList cap) (.bits bits) buffer address capacity used u.1)
      (t, base + 1341) := by
  let prepared : MachineData := {t with regs := {t.regs with
    rdi := t.regs.rbp, rsi := t.regs.r15, rdx := t.regs.r13, rcx := t.regs.r12}}
  have preparedResources : CountPrefix s bits address capacity used prepared := resources.restate rfl rfl rfl rfl
  have capStored := (resources.inputs owned).1.2.2.2
  have capBorrowed : ∀ a, Emit.NatBorrowed cap a → BodyBorrowed s (.bitList cap) (.bits bits) buffer a := by
    intro a borrowed
    exact Or.inr (Or.inr (Or.inl borrowed))
  apply list_compare_prepare_cps e base hc
  apply list_compare_cps e base hc helpers prepared actual.value cap.value
  · exact constructor_return_mapped s prepared (.bitList cap) (.bits bits) buffer address capacity used owned
      preparedResources.mapping preparedResources.stack
  · simpa only [prepared, actualPointer, actualPayload] using
      count_pair_at_call s prepared (.bitList cap) bits buffer address capacity used (base + 1358).toBitVec
        actual owned preparedResources counted
  · simpa only [prepared, capPointer, capPayload] using
      bound_pair_at_call s prepared (.bitList cap) bits buffer address capacity used (base + 1358).toBitVec
        cap owned preparedResources capStored capBorrowed
  rintro ⟨u, pc⟩ returned
  have pcEq : pc = base + 1358 := by simpa using returned.1
  subst pc
  have afterResources : CountPrefix s bits address capacity used u :=
    compare_count_prefix s prepared (u, base + 1358) (.bitList cap) bits
      buffer address capacity used (base + 1358).toBitVec (compare actual.value cap.value) owned preparedResources returned
  have keep := returned.2.2.2.2.2
  have rBP : u.regs.rbp.toBitVec = t.regs.rbp.toBitVec := keep .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
  have r12 : u.regs.r12.toBitVec = t.regs.r12.toBitVec := keep .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r13 : u.regs.r13.toBitVec = t.regs.r13.toBitVec := keep .r13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r14 : u.regs.r14.toBitVec = t.regs.r14.toBitVec := keep .r14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r15 : u.regs.r15.toBitVec = t.regs.r15.toBitVec := keep .r15 (by decide) (by decide) (by decide) (by decide) (by decide)
  have lowSaved := compare_spill_read prepared (u, base + 1358) (base + 1358).toBitVec
    (compare actual.value cap.value) 16 (bits.count.setWidth 64) (by decide) savedLow returned
  have headerSaved := compare_spill_read prepared (u, base + 1358) (base + 1358).toBitVec
    (compare actual.value cap.value) 8 s.regs.rcx.toBitVec (by decide) savedHeader returned
  apply list_compared_cps e base hc u (compare actual.value cap.value) _ returned.2.1
  intro flags
  by_cases over : compare actual.value cap.value = .gt
  · simp only [over, ↓reduceIte]
    have rejected : ¬ actual.value ≤ cap.value := by have h := Nat.compare_eq_gt.mp over; omega
    apply list_limit_cps e base hc
    · have output : u.regs.rbx = s.regs.rbx := afterResources.output
      simpa only [OutputMapped, output] using afterResources.mapping _ _ owned.resultMapped
    apply Eventually.done
    refine ⟨rfl, ?_⟩
    apply list_limit_post s {u with status := flags} _ (.bitList cap) bits buffer address capacity used
      cap actual owned (afterResources.restate rfl rfl rfl rfl) counted
    · exact (afterResources.inputs owned).1.2.2.2
    · exact capBorrowed
    · exact list_bound_failure cap actual bits address capacity used counted rejected
    · simp only [afterResources.output, rBP, r12, r13, r15, capPointer, capPayload, actualPointer, actualPayload]
    · exact afterResources.stack
    · exact afterResources.vectors
  · simp only [over, ↓reduceIte]
    have fits : actual.value ≤ cap.value := by
      by_cases fits : actual.value ≤ cap.value
      · exact fits
      · exact False.elim (over (Nat.compare_eq_gt.mpr (by omega)))
    apply list_continue_cps e base hc helpers s {u with status := flags} (.bitList cap) bits buffer address capacity used owned
      (afterResources.restate rfl rfl rfl rfl)
    · exact list_bound_pass (some cap) actual bits address capacity used counted (by
        intro other equal
        cases equal
        exact fits)
    · exact r14.trans high
    · exact lowSaved
    · exact headerSaved

end SszX86.Measure.Bits

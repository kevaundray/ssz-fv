import SszX86.SerializePublish

namespace SszX86.Serialize.Publish
open SszNative SszNative.Serialize UintCodec

/-- Numeric observations of the same concrete copied image. -/
structure ObservedImage (m : DataMem) (p : Nat) (v : Image) : Prop where
  w0 : widthLoad m p 8 = some v.w0.toNat
  w1 : widthLoad m (p + 8) 8 = some v.w1.toNat
  w2 : widthLoad m (p + 16) 8 = some v.w2.toNat
  w3 : widthLoad m (p + 24) 8 = some v.w3.toNat
  w4 : widthLoad m (p + 32) 8 = some v.w4.toNat
  w5 : widthLoad m (p + 40) 8 = some v.w5.toNat
  w6 : widthLoad m (p + 48) 8 = some v.w6.toNat
  w7 : widthLoad m (p + 56) 8 = some v.w7.toNat
  tag : widthLoad m (p + 64) 4 = some v.tag.toNat
  padding : widthLoad m (p + 68) 4 = some v.padding.toNat

theorem ImageAt.observed {m : DataMem} {p : BitVec 64} {v : Image}
    (image : ImageAt m p v) : ObservedImage m p.toNat v := by
  have field (n k : Nat) (value : Nat)
      (loaded : Mem.loadInt m (p + BitVec.ofNat 64 n) k = some (value : Int)) :
      widthLoad m (p.toNat+n) k = some value := by
    simp only [widthLoad, width_address, loaded, Option.map_some, Int.toNat_natCast]
  exact ⟨by simpa using field 0 8 v.w0.toNat image.w0,
    field 8 8 v.w1.toNat image.w1, field 16 8 v.w2.toNat image.w2,
    field 24 8 v.w3.toNat image.w3, field 32 8 v.w4.toNat image.w4,
    field 40 8 v.w5.toNat image.w5, field 48 8 v.w6.toNat image.w6,
    field 56 8 v.w7.toNat image.w7, field 64 4 v.tag.toNat image.tag,
    field 68 4 v.padding.toNat image.padding⟩

/-- The five live Plan fields determine the branch and the register-carried Nat. -/
theorem image_plan (m : DataMem) (p : BitVec 64) (v : Image) (operand : NatOperand)
    (image : ImageAt m p v) (plan : Measure.PlanAt (widthLoad m) p.toNat operand) :
    v.tag = 0 ∧ v.w0 = 8 ∧ v.w1 = 0 ∧ v.w2 = operand.pointer ∧
      v.w3 = operand.payload ∧ v.w4 = 0 ∧ operand.At (widthLoad m) := by
  have seen := image.observed
  rcases plan with ⟨h0,h1,⟨h2,h3,borrowed⟩,h4,ht⟩
  simp only [Nat.add_assoc] at h3
  have eq0 := Option.some.inj (seen.w0.symm.trans h0)
  have eq1 := Option.some.inj (seen.w1.symm.trans h1)
  have eq2 := Option.some.inj (seen.w2.symm.trans h2)
  have eq3 := Option.some.inj (seen.w3.symm.trans h3)
  have eq4 := Option.some.inj (seen.w4.symm.trans h4)
  have eqt := Option.some.inj (seen.tag.symm.trans ht)
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq eq2,
    BitVec.eq_of_toNat_eq eq3, BitVec.eq_of_toNat_eq ?_, borrowed⟩
  · simpa using eqt
  · simpa using eq0
  · simpa using eq1
  · simpa using eq4

/-- Every native measurement error has a nonzero tag; neither arithmetic failure
uses the success niche. -/
theorem image_error_tag (m : DataMem) (p : BitVec 64) (v : Image) (reason : Error)
    (image : ImageAt m p v) (error : Measure.ErrorAt (widthLoad m) p.toNat reason) :
    v.tag ≠ 0 := by
  intro zero
  have seen := image.observed.tag
  rw [zero] at seen
  cases reason with
  | wrongType | outputTooSmall =>
    have code := error.2.2.2.2.2.2
    rw [seen] at code
    simp at code
  | scope expected actual | limit expected actual =>
    have code := error.2.2.2.2.2.2
    rw [seen] at code
    simp at code
  | arithmetic failure =>
    have code := error.2.2.2.2.2.2.2.2
    rw [seen] at code
    cases failure <;> simp at code

/-- Error operands are precisely the two retained Nats in Scope/Limit. -/
def ErrorBorrows (reason : Error) (a : BitVec 64) : Prop :=
  match reason with
  | .scope expected actual | .limit expected actual =>
      Emit.NatBorrowed expected a ∨ Emit.NatBorrowed actual a
  | _ => False

private theorem semantic_error_transport (before after : DataMem) (src dst : BitVec 64)
    (v : Image) (code : Nat) (expected actual : NatOperand)
    (source : ImageAt before src v) (destination : ImageAt after dst v)
    (expectedAfter : expected.At (widthLoad before) → expected.At (widthLoad after))
    (actualAfter : actual.At (widthLoad before) → actual.At (widthLoad after))
    (stored : Measure.SemanticErrorAt (widthLoad before) src.toNat code expected actual) :
    Measure.SemanticErrorAt (widthLoad after) dst.toNat code expected actual := by
  have old := source.observed
  have new := destination.observed
  rcases stored with ⟨h0,h1,⟨h2,h3,he⟩,⟨h4,h5,ha⟩,h6,h7,ht⟩
  simp only [Nat.add_assoc] at h3 h5
  refine ⟨new.w0.trans (old.w0.symm.trans h0),
    new.w1.trans (old.w1.symm.trans h1),
    ⟨new.w2.trans (old.w2.symm.trans h2), ?_, expectedAfter he⟩,
    ⟨new.w4.trans (old.w4.symm.trans h4), ?_, actualAfter ha⟩,
    new.w6.trans (old.w6.symm.trans h6), new.w7.trans (old.w7.symm.trans h7),
    new.tag.trans (old.tag.symm.trans ht)⟩
  · simpa only [Nat.add_assoc] using new.w3.trans (old.w3.symm.trans h3)
  · simpa only [Nat.add_assoc] using new.w5.trans (old.w5.symm.trans h5)

/-- Scalar error payloads are copied exactly; borrowed Large limbs are transported
by the actual write frame, not assumed to reappear at a future callsite. -/
theorem error_transport (before after : DataMem) (src dst : BitVec 64)
    (v : Image) (reason : Error) (writable : BitVec 64 → Prop)
    (source : ImageAt before src v) (destination : ImageAt after dst v)
    (frame : MemoryFrame before after writable)
    (safe : ∀ a, ErrorBorrows reason a → ¬ writable a)
    (stored : Measure.ErrorAt (widthLoad before) src.toNat reason) :
    Measure.ErrorAt (widthLoad after) dst.toNat reason := by
  cases reason with
  | wrongType | outputTooSmall =>
    exact semantic_error_transport before after src dst v _ _ _ source destination
      (fun _ => trivial) (fun _ => trivial) stored
  | scope expected actual | limit expected actual =>
    apply semantic_error_transport before after src dst v _ expected actual source destination
      (Measure.operand_frame before after writable frame expected ?_)
      (Measure.operand_frame before after writable frame actual ?_) stored
    · exact fun a h => safe a (Or.inl h)
    · exact fun a h => safe a (Or.inr h)
  | arithmetic failure =>
    have old := source.observed
    have new := destination.observed
    rcases stored with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht⟩
    exact ⟨new.w0.trans (old.w0.symm.trans h0),
      new.w1.trans (old.w1.symm.trans h1), new.w2.trans (old.w2.symm.trans h2),
      new.w3.trans (old.w3.symm.trans h3), new.w4.trans (old.w4.symm.trans h4),
      new.w5.trans (old.w5.symm.trans h5), new.w6.trans (old.w6.symm.trans h6),
      new.w7.trans (old.w7.symm.trans h7), new.tag.trans (old.tag.symm.trans ht)⟩

theorem prepared_image (m : DataMem) (sp : BitVec 64) (v : Image)
    (bound : sp.toNat + 96 ≤ 2^64) (image : ImageAt m (sp + 24#64) v) :
    ImageAt (preparedMem m sp v) (sp + 24#64) v := by
  rcases image with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 ht hp
  constructor <;>
    simp (disch := first | assumption | omega | decide) only
      [preparedMem, BitVec.add_assoc, BitVec.reduceAdd, local_read (extent := 96), load_store_word]
  all_goals assumption

theorem prepared_state_image (s : MachineData) (v : Image) (flags : StatusFlags)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v) :
    ImageAt (prepared s v flags).dmem (s.regs.rsp.toBitVec + 24#64) v :=
  prepared_image _ _ v bound (spill_plan _ _ v bound image)

theorem prepared_operand (s : MachineData) (v : Image) (flags : StatusFlags)
    (operand : NatOperand) (stored : operand.At (widthLoad s.dmem))
    (safe : ∀ a, Emit.NatBorrowed operand a →
      ¬ InSpan a (s.regs.rsp.toBitVec + 8#64) 56) :
    operand.At (widthLoad (prepared s v flags).dmem) :=
  Measure.operand_frame _ _ _ (prepared_state_frame s v flags) operand safe stored

theorem prepared_plan (s : MachineData) (v : Image) (flags : StatusFlags)
    (operand : NatOperand) (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (plan : Measure.PlanAt (widthLoad s.dmem) (s.regs.rsp.toBitVec + 24#64).toNat operand)
    (safe : ∀ a, Emit.NatBorrowed operand a →
      ¬ InSpan a (s.regs.rsp.toBitVec + 8#64) 56) :
    Measure.PlanAt (widthLoad (prepared s v flags).dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat operand ∧
    (prepared s v flags).regs.rax.toBitVec = operand.pointer ∧
    (prepared s v flags).regs.r9.toBitVec = operand.payload := by
  obtain ⟨tag,h0,h1,h2,h3,h4,borrowed⟩ := image_plan _ _ v operand image plan
  have new := (prepared_state_image s v flags bound image).observed
  refine ⟨⟨?_, ?_, ⟨?_, ?_, prepared_operand s v flags operand borrowed safe⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [h0, show (8 : BitVec 64).toNat = 8 from by decide] using new.w0
  · simpa only [h1, show (0 : BitVec 64).toNat = 0 from by decide] using new.w1
  · simpa only [h2] using new.w2
  · simpa only [h3, Nat.add_assoc] using new.w3
  · simpa only [h4, show (0 : BitVec 64).toNat = 0 from by decide] using new.w4
  · simpa only [tag, show (0 : BitVec 32).toNat = 0 from by decide] using new.tag
  · simpa only [prepared, tested, loaded, UInt64.toBitVec_ofBitVec] using h2
  · simpa only [prepared, tested, loaded, UInt64.toBitVec_ofBitVec] using h3

theorem copied_error (s : MachineData) (v : Image) (flags : StatusFlags) (reason : Error)
    (image : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) v)
    (bound : s.regs.rbx.toNat + 80 ≤ 2^64)
    (stored : Measure.ErrorAt (widthLoad s.dmem) (s.regs.rsp.toBitVec + 24#64).toNat reason)
    (safe : ∀ a, ErrorBorrows reason a →
      ¬ (InSpan a s.regs.rbx.toBitVec 72 ∨ InSpan a (s.regs.rsp.toBitVec + 8#64) 16)) :
    Measure.ErrorAt (widthLoad (copied s v flags).dmem) s.regs.rbx.toNat reason := by
  exact error_transport s.dmem (copied s v flags).dmem _ _ v reason _ image
    (copy_image _ _ v bound) (copied_frame s v flags) safe stored

theorem prepared_state_mapping (s : MachineData) (v : Image) (flags : StatusFlags) :
    BitVector.Mapping.Extends s.dmem (prepared s v flags).dmem :=
  (spill_mapping s.dmem s.regs.rsp.toBitVec v).trans (prepared_mapping _ _ v)

theorem copied_state_mapping (s : MachineData) (v : Image) (flags : StatusFlags) :
    BitVector.Mapping.Extends s.dmem (copied s v flags).dmem :=
  (spill_mapping s.dmem s.regs.rsp.toBitVec v).trans (copy_mapping _ _ v)

end SszX86.Serialize.Publish

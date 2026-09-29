import SszX86.CodecBoundedMemory

namespace SszX86.CodecBounded
open SszX86.UintCodec
open SszNative

/-- The bounded helper's physical result image; comparison uses arbitrary
logical operand values, while error payloads retain their original representation. -/
def resultMem (s : MachineData) (base : Int64) (cap : Option NatOperand)
    (actual : NatOperand) : DataMem :=
  match cap with
  | none => Mem.storeInt (savedMem s) (s.regs.rdi.toBitVec + 64#64) 4 0
  | some limit =>
    if actual.value ≤ limit.value then
      Mem.storeInt (calledMem s base) (s.regs.rdi.toBitVec + 64#64) 4 0
    else Mem.storeInt (errorPayload (calledMem s base) s.regs.rdi.toBitVec
      limit.pointer limit.payload actual.pointer actual.payload)
      (s.regs.rdi.toBitVec + 64#64) 4 2

def Returned (s : MachineData) (ra : BitVec 64) (memory : DataMem) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧ t.1.dmem = memory ∧ t.1.zmms = s.zmms ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  t.1.regs.rbx = s.regs.rbx ∧ t.1.regs.rbp = s.regs.rbp ∧
  t.1.regs.r12 = s.regs.r12 ∧ t.1.regs.r13 = s.regs.r13 ∧
  t.1.regs.r14 = s.regs.r14 ∧ t.1.regs.r15 = s.regs.r15

private theorem finish_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s v : MachineData) (ra : BitVec 64) (memory : DataMem)
    (sp : v.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 40)
    (out : v.regs.rbx = s.regs.rdi) (vectors : v.zmms = s.zmms)
    (r13 : v.regs.r13 = s.regs.r13)
    (mapped : Large.Mapped v.dmem v.regs.rbx.toBitVec 68)
    (saved : SavedAt v.dmem v.regs.rsp.toBitVec s ra)
    (apart : ∀ a, InSpan a (s.regs.rsp.toBitVec - 40) 48 → ¬InSpan a s.regs.rdi.toBitVec 68)
    (mem : (published v).dmem = memory) :
    Eventually (step e) (Returned s ra memory) (v, base + 110) := by
  apply publish_cps e base hc v mapped
  apply restore_cps e base hc (published v) s ra
  · apply saved.frame (fun a => InSpan a v.regs.rbx.toBitVec 68)
      (status_frame v.dmem v.regs.rbx.toBitVec _)
    simpa only [out, sp] using apart
  · refine ⟨rfl, mem, vectors, ?_, rfl, rfl, rfl, r13, rfl, rfl⟩
    simp only [restored, published, UInt64.toBitVec_ofBitVec, sp]
    bv_omega

/-- Full None/Some bounded execution. Input metadata and borrowed limbs may
alias each other arbitrarily. Only the actual output and stack write regions
must be disjoint from their read-only footprint. No narrow-Nat restriction,
comparison oracle, allocator, or future-state premise is used. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hcompare : NatCompare.CodeAt e (base + Int64.ofInt natCompareOffset))
    (s : MachineData) (cap : Option NatOperand) (actual : NatOperand) (ra : BitVec 64)
    (input : InputsAt s.dmem s.regs.rsi.toBitVec s.regs.rdx.toBitVec actual cap)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (output : Large.Mapped s.dmem s.regs.rdi.toBitVec 68)
    (separate : ∀ a, Borrowed s.regs.rsi.toBitVec s.regs.rdx.toBitVec actual cap a →
      ¬InSpan a (s.regs.rsp.toBitVec - 48) 48 ∧ ¬InSpan a s.regs.rdi.toBitVec 68)
    (stackOut : ∀ a, InSpan a (s.regs.rsp.toBitVec - 40) 48 → ¬InSpan a s.regs.rdi.toBitVec 68)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Returned s ra (resultMem s base cap actual)) (s, base) := by
  have pushedInputs := inputs_frame s.dmem (savedMem s) s.regs.rsi.toBitVec
    s.regs.rdx.toBitVec actual cap _ (saved_frame s) (fun a ha => (separate a ha).1) input
  have pushedOutput : Large.Mapped (savedMem s) s.regs.rdi.toBitVec 68 := by
    unfold savedMem
    repeat' first | exact output | apply Large.mapped_store
  apply entry_cps e base hc s stack
  intro flags
  cases cap with
  | none =>
    apply option_cps e base hc (entered s flags) 0 pushedInputs
    intro f
    simp only [show (0 : BitVec 32) ≠ 1 by decide, ↓reduceIte]
    apply finish_correct e base hc s _ ra (resultMem s base none actual)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact pushedOutput
    · exact saved_at s ra ret
    · exact stackOut
    · rfl
  | some cap =>
    apply option_cps e base hc (entered s flags) 1 pushedInputs.1
    intro f
    simp only [↓reduceIte]
    let before := prepared {entered s flags with status := f} cap actual
    have capP : Mem.loadInt (savedMem s) (s.regs.rsi.toBitVec + 8#64) 8 =
        some (cap.pointer.toNat : Int) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        widthLoad_eq _ _ _ _ pushedInputs.2.1.1
    have capV : Mem.loadInt (savedMem s) (s.regs.rsi.toBitVec + 16#64) 8 =
        some (cap.payload.toNat : Int) := by
      have h := widthLoad_eq _ _ _ _ pushedInputs.2.1.2.1
      simpa only [width_address, BitVec.add_assoc, BitVec.reduceAdd] using h
    have actualP : Mem.loadInt (savedMem s) s.regs.rdx.toBitVec 8 =
        some (actual.pointer.toNat : Int) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        widthLoad_eq _ _ _ _ pushedInputs.2.2.1
    have actualV : Mem.loadInt (savedMem s) (s.regs.rdx.toBitVec + 8#64) 8 =
        some (actual.payload.toNat : Int) := by
      simpa only [width_address] using widthLoad_eq _ _ _ _ pushedInputs.2.2.2.1
    apply prepare_cps e base hc _ cap actual capP capV actualP actualV
    have callMemory : (callState before base).dmem = calledMem s base := by
      simp only [callState, before, prepared, entered, calledMem, BitVec.sub_sub]
    have callInput := inputs_frame s.dmem (calledMem s base) s.regs.rsi.toBitVec
      s.regs.rdx.toBitVec actual (some cap) _ (called_frame s base)
      (fun a ha => (separate a ha).1) input
    apply compare_cps e base hc hcompare before actual.value cap.value
    · have mappedCall : Large.Mapped (savedMem s) (s.regs.rsp.toBitVec - 48) 48 := by
        unfold savedMem
        repeat' first | exact stack | apply Large.mapped_store
      simpa [before, prepared, entered, BitVec.sub_sub] using
        Large.mapped_load (savedMem s) (s.regs.rsp.toBitVec - 48) 48 0 8 mappedCall (by decide)
    · simpa only [callMemory, before, prepared] using
        NatOperand.At.pair (widthLoad (calledMem s base)) actual callInput.2.2.2.2
    · simpa only [callMemory, before, prepared] using
        NatOperand.At.pair (widthLoad (calledMem s base)) cap callInput.2.1.2.2
    · rintro ⟨t, pc⟩ returned
      have pcEq : pc = base + 47 := by simpa using returned.1
      subst pc
      have memory : t.dmem = calledMem s base := returned.2.2.1.trans callMemory
      have vectors : t.zmms = s.zmms := returned.2.2.2.1
      have stackEq : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 40 := by
        have h := returned.2.2.2.2.1
        simpa [callState, before, prepared, entered, BitVec.sub_sub] using h
      have keep := returned.2.2.2.2.2
      have rbx : t.regs.rbx = s.regs.rdi :=
        keep .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
      have rbp : t.regs.rbp = 0 :=
        keep .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
      have r12 : t.regs.r12.toBitVec = cap.payload :=
        keep .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
      have r13 : t.regs.r13 = s.regs.r13 :=
        keep .r13 (by decide) (by decide) (by decide) (by decide) (by decide)
      have r14 : t.regs.r14 = s.regs.rdx :=
        keep .r14 (by decide) (by decide) (by decide) (by decide) (by decide)
      have r15 : t.regs.r15.toBitVec = cap.pointer :=
        keep .r15 (by decide) (by decide) (by decide) (by decide) (by decide)
      have outputT : Large.Mapped t.dmem t.regs.rbx.toBitVec 68 := by
        rw [memory, rbx]
        apply Large.mapped_store
        exact pushedOutput
      have savedT : SavedAt t.dmem t.regs.rsp.toBitVec s ra := by
        rw [memory, stackEq]
        exact called_saved s base ra ret
      apply compared_cps e base hc t (compare actual.value cap.value) returned.2.1
      intro finalFlags
      by_cases over : compare actual.value cap.value = .gt
      · simp only [over, ↓reduceIte]
        have noFit : ¬actual.value ≤ cap.value := by
          have h := Nat.compare_eq_gt.mp over
          omega
        apply reject_cps e base hc {t with status := finalFlags} actual outputT
        · rw [memory, r14]
          simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
            widthLoad_eq _ _ _ _ callInput.2.2.1
        · rw [memory, r14]
          simpa only [width_address] using widthLoad_eq _ _ _ _ callInput.2.2.2.1
        · intro i hi j hj eq
          apply (separate _ (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩)))).2
          refine ⟨j, hj, ?_⟩
          simpa only [r14, rbx] using eq
        apply finish_correct e base hc s _ ra (resultMem s base (some cap) actual)
        · exact stackEq
        · exact rbx
        · exact vectors
        · exact r13
        · unfold rejected errorPayload
          repeat' first | exact outputT | apply Large.mapped_store
        · apply savedT.frame (fun a => InSpan a t.regs.rbx.toBitVec 68)
            (error_payload_frame _ _ _ _ _ _)
          simpa only [rbx, stackEq] using stackOut
        · exact stackOut
        · simp only [published, rejected, resultMem, noFit, ↓reduceIte, memory, rbx, r12, r15]
      · simp only [over, ↓reduceIte]
        have fit : actual.value ≤ cap.value := by
          by_contra hn
          exact over (Nat.compare_eq_gt.mpr (by omega))
        apply finish_correct e base hc s _ ra (resultMem s base (some cap) actual)
        · exact stackEq
        · exact rbx
        · exact vectors
        · exact r13
        · exact outputT
        · exact savedT
        · exact stackOut
        · simp only [published, resultMem, fit, ↓reduceIte, memory, rbx, rbp]

end SszX86.CodecBounded

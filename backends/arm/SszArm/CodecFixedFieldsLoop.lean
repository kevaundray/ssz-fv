import SszArm.CodecFixedFieldsRound

namespace SszArm.Codec.Fixed.IsFixed

open SszNative.Codec (Desc)
open Dispatch.Block (branch)

private theorem context_pc {source current : ArmState} (context : BodyContext source current)
    (pc : BitVec 64) : BodyContext source (w .PC pc current) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [state_simp_rules] using context.saved.sp
    · simpa only [state_simp_rules] using context.saved.link
    · simpa only [state_simp_rules] using context.saved.first
    · simpa only [state_simp_rules] using context.saved.second
  · intro reg lower upper h19 h20 h30
    simpa only [state_simp_rules] using context.registers reg lower upper h19 h20 h30
  · intro reg lower upper
    simpa only [state_simp_rules] using context.vectors reg lower upper

/-- The length of the remaining physical field slice is the loop measure.
Every recursive descriptor call is supplied by strict child induction; this
lemma introduces no oracle into the public original-entry contract. -/
theorem fields_loop (source : ArmState) (base : BitVec 64) (budget : Nat) :
    ∀ (fields : List (String × Desc)) (pointer : Nat) (current : ArmState),
      FieldsOwned source current fields pointer budget →
      (∀ field ∈ fields, BodyCorrect field.2) → CodeAt current base →
      read_err current = .None → CheckSPAlignment current →
      read_pc current = base + 108#64 →
      ∃ fuel final, run fuel current = final ∧ FieldsPost source current final fields base budget := by
  intro fields
  induction fields with
  | nil =>
    intro pointer current owned children code error aligned pc
    let final := w .PC (base + 188#64) current
    have zero : r (.GPR 19#5) current = 0#64 := by simpa using owned.count
    have executed : run 1 current = final := by
      change stepi current = final
      rw [step .p108 current base code error aligned pc]
      change r .PC current = _ at pc
      simp [Op.effect, branch, final, state_simp_rules, zero, pc, BitVec.add_assoc]
    refine ⟨1, final, executed, context_pc owned.context _, ?_, ?_, ?_, ?_⟩
    · rfl
    · simpa only [final, state_simp_rules] using error
    · simp only [final, SszNative.FixedSize.fieldsFixed, ↓reduceIte, state_simp_rules]
    · intro address outside
      rfl
  | cons field rest ih =>
    rcases field with ⟨name, child⟩
    intro pointer current owned children code error aligned pc
    obtain ⟨roundFuel, next, roundRun, nextOwned, nextProgram, nextError, nextPC, roundFrame⟩ :=
      fields_round source current base name child rest pointer budget owned
        (children (name, child) (by simp)) code error aligned pc
    cases fixed : SszNative.FixedSize.isFixed child with
    | false =>
      refine ⟨roundFuel, next, roundRun, nextOwned.context, nextProgram, nextError, ?_, roundFrame⟩
      simpa only [SszNative.FixedSize.fieldsFixed, fixed, Bool.false_and, ↓reduceIte] using nextPC
    | true =>
      have nextCode : CodeAt next base := by simpa only [CodeAt, nextProgram] using code
      have nextSP : r (.GPR 31#5) next = r (.GPR 31#5) current :=
        nextOwned.context.saved.sp.trans owned.context.saved.sp.symm
      have nextAligned : CheckSPAlignment next := by
        simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, nextSP] using aligned
      have againPC : read_pc next = base + 108#64 := by simpa only [fixed, ↓reduceIte] using nextPC
      obtain ⟨restFuel, final, restRun, post⟩ := ih (pointer + 24) next nextOwned
        (fun field member => children field (List.mem_cons_of_mem _ member)) nextCode nextError nextAligned againPC
      refine ⟨roundFuel + restFuel, final, ?_, post.context,
        post.program.trans nextProgram, post.error, ?_, roundFrame.trans post.frame⟩
      · rw [run_plus, roundRun, restRun]
      · simpa only [SszNative.FixedSize.fieldsFixed, fixed, Bool.true_and] using post.pc

end SszArm.Codec.Fixed.IsFixed

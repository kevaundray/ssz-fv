import SszX86.CodecMeasureImpl
import SszX86.MeasureImpl

namespace SszX86.CodecMeasure

/-- Small structural certificates avoid normalizing the complete 804-row image. -/
private theorem primitive_chunk0 :
    Measure.programChunk0.Sublist (programChunk0 ++ programChunk1 ++ programChunk2) := by
  simp only [Measure.programChunk0, programChunk0, programChunk1, programChunk2,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk1 :
    Measure.programChunk1.Sublist (programChunk2 ++ programChunk3 ++ programChunk4) := by
  simp only [Measure.programChunk1, programChunk2, programChunk3, programChunk4,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk2 :
    Measure.programChunk2.Sublist (programChunk4 ++ programChunk5) := by
  simp only [Measure.programChunk2, programChunk4, programChunk5,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk3 :
    Measure.programChunk3.Sublist (programChunk5 ++ programChunk6) := by
  simp only [Measure.programChunk3, programChunk5, programChunk6,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk4 :
    Measure.programChunk4.Sublist (programChunk6 ++ programChunk7 ++ programChunk8) := by
  simp only [Measure.programChunk4, programChunk6, programChunk7, programChunk8,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk5 :
    Measure.programChunk5.Sublist (programChunk8 ++ programChunk9 ++ programChunk10) := by
  simp only [Measure.programChunk5, programChunk8, programChunk9, programChunk10,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk6 :
    Measure.programChunk6.Sublist (programChunk10 ++ programChunk11) := by
  simp only [Measure.programChunk6, programChunk10, programChunk11,
    List.cons_append, List.nil_append]
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

private theorem primitive_chunk7 :
    Measure.programChunk7.Sublist programChunk11 := by
  unfold Measure.programChunk7 programChunk11
  repeat' first | exact List.Sublist.slnil | apply List.Sublist.cons_cons | apply List.Sublist.cons

/-- Every old fetch is an identical instruction of the complete linked image. -/
theorem primitive_program_subset : Measure.program ⊆ program := by
  intro row member
  simp only [Measure.program, List.mem_append] at member
  rcases member with ((((((h | h) | h) | h) | h) | h) | h) | h
  · have found := primitive_chunk0.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with (found | found) | found <;> simp [found]
  · have found := primitive_chunk1.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with (found | found) | found <;> simp [found]
  · have found := primitive_chunk2.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with found | found <;> simp [found]
  · have found := primitive_chunk3.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with found | found <;> simp [found]
  · have found := primitive_chunk4.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with (found | found) | found <;> simp [found]
  · have found := primitive_chunk5.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with (found | found) | found <;> simp [found]
  · have found := primitive_chunk6.subset h
    simp only [List.mem_append] at found
    simp only [program, List.mem_append]
    rcases found with found | found <;> simp [found]
  · have found := primitive_chunk7.subset h
    simp only [program, List.mem_append]
    simp [found]

/-- The additional compound targets do not introduce directives at a primitive
instruction boundary. Thus the old exact-fetch contract really is a projection,
not a second executable or an assumed instruction simulation. -/
theorem primitive_labels_at : ∀ row ∈ Measure.program,
    labels.filter (fun item => item.2 == row.1) =
      Measure.labels.filter (fun item => item.2 == row.1) := by
  simp only [Measure.program, List.forall_mem_append]
  repeat' apply And.intro
  all_goals
    dsimp only [Measure.programChunk0, Measure.programChunk1, Measure.programChunk2,
      Measure.programChunk3, Measure.programChunk4, Measure.programChunk5,
      Measure.programChunk6, Measure.programChunk7]
    simp only [List.forall_mem_cons]
    repeat' apply And.intro
    all_goals first | exact True.intro | rfl | (intro row empty; cases empty)

/-- All named branch targets of the primitive provider are present unchanged. -/
theorem primitive_labels_sublist : Measure.labels.Sublist labels := by
  unfold Measure.labels labels
  repeat' first
    | exact List.Sublist.slnil
    | apply List.Sublist.cons_cons
    | apply List.Sublist.cons

/-- Reuse the original seven-shape ISA theorem against the full image. The
projection establishes both fetch and branch-target premises structurally. -/
theorem CodeAt.primitive {e : Executable} {base : Int64} (code : CodeAt e base) :
    Measure.CodeAt e base := by
  refine ⟨?_, ?_⟩
  · intro row member
    rw [code.fetch row (primitive_program_subset member)]
    unfold directives Measure.directives
    rw [primitive_labels_at row member]
  · intro item member
    exact code.targets item (primitive_labels_sublist.subset member)

end SszX86.CodecMeasure

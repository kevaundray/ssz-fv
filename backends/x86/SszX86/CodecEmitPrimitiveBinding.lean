import SszX86.CodecEmitImpl
import SszX86.EmitChunks

namespace SszX86.CodecEmit

/-- Primitive-reachable instructions are unchanged rows of the actual complete
image. The proof skips compound rows; it never replaces their semantics. -/
theorem primitive_program_sublist : Emit.program.Sublist program := by
  rw [Emit.program_chunks]
  unfold program
  repeat' first
    | exact List.Sublist.slnil
    | apply List.Sublist.cons_cons
    | apply List.Sublist.cons

/-- New compound branch labels lie at compound-only boundaries. Old primitive
fetches therefore have exactly the original directive sequence. -/
theorem primitive_labels_at : ∀ row ∈ Emit.program,
    labels.filter (fun item => item.2 == row.1) =
      Emit.labels.filter (fun item => item.2 == row.1) := by
  intro row member
  rw [Emit.program_chunks] at member
  simp only [List.mem_append] at member
  rcases member with (member | member) | member
  all_goals
    simp only [Emit.programChunk0, Emit.programChunk1, Emit.programChunk2,
      List.mem_cons, List.not_mem_nil, or_false] at member
    repeat' first
      | (rcases member with rfl | member)
      | subst row
      | rfl

theorem primitive_labels_sublist : Emit.labels.Sublist labels := by
  unfold Emit.labels labels
  repeat' first
    | exact List.Sublist.slnil
    | apply List.Sublist.cons_cons
    | apply List.Sublist.cons

/-- Projection to the immutable provider establishes both actual fetches and
actual branch destinations. No alternate executable is introduced. -/
theorem CodeAt.primitive {e : Executable} {base : Int64} (code : CodeAt e base) :
    Emit.CodeAt e base := by
  refine ⟨?_, ?_⟩
  · intro row member
    rw [code.fetch row (primitive_program_sublist.subset member)]
    unfold directives Emit.directives
    rw [primitive_labels_at row member]
  · intro item member
    exact code.targets item (primitive_labels_sublist.subset member)

end SszX86.CodecEmit

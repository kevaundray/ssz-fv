import SszX86.CodecSerializeImpl
import SszX86.SerializeImpl

namespace SszX86.CodecSerialize

private theorem programChunk0_eq : programChunk0 = Serialize.programChunk0 := by rfl
private theorem programChunk1_eq : programChunk1 = Serialize.programChunk1 := by rfl

/-- The recursive entry is the original native wrapper, not a new allocation or
size-query symbol. Its unchanged machine cuts can be reused independently of
the seven-shape logical domain of the old public wrapper theorem. -/
theorem program_eq : program = Serialize.program := by
  simp only [program, Serialize.program, programChunk0_eq, programChunk1_eq]

theorem labels_eq : labels = Serialize.labels := by rfl

theorem directives_eq (row : Nat × Nat × Program) :
    directives row = Serialize.directives row := by
  simp only [directives, Serialize.directives, labels_eq]

/-- Only instruction ownership is transported; no primitive codec call contract
is substituted for either recursive callee. -/
theorem CodeAt.wrapper {e : Executable} {base : Int64} (code : CodeAt e base) :
    Serialize.CodeAt e base := by
  constructor
  · intro row member
    rw [← program_eq] at member
    exact (code.fetch row member).trans (directives_eq row)
  · intro item member
    rw [← labels_eq] at member
    exact code.targets item member

end SszX86.CodecSerialize

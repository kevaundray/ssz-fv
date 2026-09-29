import SszCodecTypes

namespace SszX86.CodecIsFixed
open SszNative

mutual
  /-- Termination measure for the actual descriptor traversal. Logical Nat
  metadata, field names, active masks and readonly pointer identities are absent. -/
  def traversalRank : Codec.Desc → Nat
    | .vector element _ => traversalRank element + 1
    | .container fields | .progressiveContainer _ fields => fieldsRank fields + 1
    | _ => 1

  def fieldsRank : List (String × Codec.Desc) → Nat
    | [] => 0
    | (_, field) :: rest => traversalRank field + fieldsRank rest + 1
end

theorem vector_rank (element : Codec.Desc) (length : NatOperand) :
    traversalRank element < traversalRank (.vector element length) := by
  simp only [traversalRank]
  omega

theorem field_rank (fields : List (String × Codec.Desc))
    (field : String × Codec.Desc) (member : field ∈ fields) :
    traversalRank field.2 ≤ fieldsRank fields := by
  induction fields with
  | nil => simp at member
  | cons head rest ih =>
    rcases head with ⟨name, desc⟩
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp only [fieldsRank]
      omega
    · have lower := ih member
      simp only [fieldsRank]
      omega

theorem container_field_rank (fields : List (String × Codec.Desc))
    (field : String × Codec.Desc) (member : field ∈ fields) :
    traversalRank field.2 < traversalRank (.container fields) := by
  have lower := field_rank fields field member
  simp only [traversalRank]
  omega

theorem progressive_field_rank (active : List Bool) (fields : List (String × Codec.Desc))
    (field : String × Codec.Desc) (member : field ∈ fields) :
    traversalRank field.2 < traversalRank (.progressiveContainer active fields) := by
  have lower := field_rank fields field member
  simp only [traversalRank]
  omega

end SszX86.CodecIsFixed

import SszX86.CodecIsFixedDispatch
import SszX86.CodecIsFixedOrder

namespace SszX86.CodecIsFixed
open SszNative UintCodec BoolCodec

/-- Simultaneous induction invariant for the two physical tag-test sites. -/
def LoadedRefines (e : Executable) (base : Int64) (desc : SszNative.Codec.Desc) : Prop :=
  ∀ (s : MachineData) (r : Codec.Footprint) (bytes : Nat),
    Working s base r desc bytes → s.regs.rax = UInt64.ofNat (Codec.descTag desc) →
    Eventually (step e) (BodyPost s bytes (FixedSize.isFixed desc) base) (s, base + 7) ∧
      Eventually (step e) (BodyPost s bytes (FixedSize.isFixed desc) base) (s, base + 23)

private theorem loaded_induction_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (desc : SszNative.Codec.Desc)
    (smaller : ∀ child, traversalRank child < traversalRank desc →
      EntryRefines e base child ∧ LoadedRefines e base child) :
    LoadedRefines e base desc := by
  intro s r bytes owned tag
  apply tag_guards e base hc
  intro flags
  let guarded : MachineData := {s with status := flags}
  by_cases vector : ∃ element length, desc = .vector element length
  · obtain ⟨element, length, rfl⟩ := vector
    have tagged : s.regs.rax.toBitVec = 7#64 := by rw [tag]; rfl
    rw [if_pos tagged]
    obtain ⟨child, pointer, stored⟩ := Codec.DescAt.vector owned.descriptor
    apply vector_load e base hc guarded child (Codec.descTag element) _ pointer.load stored.tag
    let prepared := vectorState guarded child (Codec.descTag element)
    have owns : Working prepared base r element bytes :=
      ⟨stored, owned.table, owned.table_readonly, owned.stack,
        owned.enough, owned.above, owned.readonly⟩
    apply eventually_trans (step e) (BodyPost prepared bytes (FixedSize.isFixed element) base) _ _
    · exact ((smaller element (vector_rank element length)).2 prepared r bytes owns rfl).2
    · intro t post
      apply Eventually.done
      exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
  · have notVector : ∀ element length, desc ≠ .vector element length := by
      intro element length same
      exact vector ⟨element, length, same⟩
    have tagged : s.regs.rax.toBitVec ≠ 7#64 := by
      rw [tag]
      cases desc with
      | primitive shape => cases shape <;> decide
      | vector element length => exact False.elim (notVector element length rfl)
      | _ => decide
    rw [if_neg tagged]
    have owns : Working guarded base r desc bytes :=
      ⟨owned.descriptor, owned.table, owned.table_readonly, owned.stack,
        owned.enough, owned.above, owned.readonly⟩
    apply eventually_trans (step e) (BodyPost guarded bytes (FixedSize.isFixed desc) base) _ _
    · apply nonvector_dispatch e base hc desc notVector
      · intro fields shape field member
        rcases shape with same | ⟨active, same⟩
        · subst desc
          exact (smaller field.2 (container_field_rank fields field member)).1
        · subst desc
          exact (smaller field.2 (progressive_field_rank active fields field member)).1
      · exact owns
      · exact tag
    · intro t post
      exact Eventually.done _ (post.preceded
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩)

/-- Both the vector backedge and the self-CALL are closed by strict structural
induction. A public client supplies only code, recursive immutable storage,
finite physical stack ownership and the original return word. -/
theorem is_fixed_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (ra : BitVec 64) (bytes : Nat) (owned : Owned s base r desc ra bytes) :
    Eventually (step e) (Post s desc ra bytes) (s, base) := by
  have complete : ∀ rank (desc : SszNative.Codec.Desc), traversalRank desc = rank →
      EntryRefines e base desc ∧ LoadedRefines e base desc := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro desc rankEq
      have loaded : LoadedRefines e base desc := loaded_induction_step e base hc desc (by
        intro child below
        exact ih (traversalRank child) (by omega) child rfl)
      refine ⟨?_, loaded⟩
      intro initial readable ret budget owns
      apply pushes_runs e base hc initial _ owns.activation_mapped
      have working := working_entry owns
      apply tag_load e base hc (savedState initial) (Codec.descTag desc) _ working.descriptor.tag
      let prepared := loadedState (savedState initial) (Codec.descTag desc)
      have workingLoaded : Working prepared base readable desc (budget - 24) :=
        ⟨working.descriptor, working.table, working.table_readonly, working.stack,
          working.enough, working.above, working.readonly⟩
      apply eventually_trans (step e)
        (BodyPost prepared (budget - 24) (FixedSize.isFixed desc) base) _ _
      · exact (loaded prepared readable (budget - 24) workingLoaded rfl).1
      · intro t post
        apply finish_body e base hc initial readable desc ret budget owns t
        exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
  exact (complete (traversalRank desc) desc rfl).1 s r ra bytes owned

/-- Complete recursive descriptor observations survive the actual execution;
readonly aliases require no disjoint ownership tree. -/
theorem is_fixed_preserves_descriptor (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (ra : BitVec 64) (bytes : Nat) (owned : Owned s base r desc ra bytes) :
    Eventually (step e)
      (fun t => Post s desc ra bytes t ∧ Codec.DescAt t.1.dmem r s.regs.rdi.toBitVec desc)
      (s, base) := by
  apply eventually_trans (step e) (Post s desc ra bytes) _ _
  · exact is_fixed_correct e base hc s r desc ra bytes owned
  · intro t post
    exact Eventually.done _ ⟨post, owned.descriptor.frame post.frame owned.readonly⟩

end SszX86.CodecIsFixed

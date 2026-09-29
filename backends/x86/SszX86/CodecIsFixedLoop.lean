import SszX86.CodecIsFixedBody

namespace SszX86.CodecIsFixed
open SszNative UintCodec BoolCodec

/-- The induction predicate for an original entry. This is discharged for all
finite descriptors by the structural theorem, not assumed by public clients. -/
def EntryRefines (e : Executable) (base : Int64) (desc : SszNative.Codec.Desc) : Prop :=
  ∀ (s : MachineData) (r : Codec.Footprint) (ra : BitVec 64) (bytes : Nat),
    Owned s base r desc ra bytes → Eventually (step e) (Post s desc ra bytes) (s, base)

/-- List induction discharges the native iterator backedge. Recursive descriptor
entries below are precisely the enclosing structural induction hypotheses. -/
theorem fields_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (fields : List (String × SszNative.Codec.Desc))
    (children : ∀ field ∈ fields, EntryRefines e base field.2)
    (s : MachineData) (r : Codec.Footprint) (bytes : Nat)
    (owned : FieldsOwned s base r fields bytes) :
    Eventually (step e) (BodyPost s bytes (FixedSize.fieldsFixed fields) base) (s, base + 96) := by
  induction fields generalizing s with
  | nil =>
    have zero : s.regs.r14.toBitVec = 0 := by simpa using owned.counter
    apply fields_guard e base hc
    intro flags
    rw [if_pos zero]
    apply eventually_trans (step e) (BodyPost {s with status := flags} bytes true base) _ _
    · exact true_body e base hc _ bytes
    · intro t post
      apply Eventually.done
      exact post.preceded ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
  | cons field rest ih =>
    rcases field with ⟨name, desc⟩
    have nonzero : s.regs.r14.toBitVec ≠ 0 := by
      rw [owned.counter]
      have bound := owned.byteBound
      simp only [List.length_cons] at bound
      bv_omega
    obtain ⟨child, childLoad, childStored, restStored⟩ : ∃ child : BitVec 64,
        Codec.LoadAt s.dmem r (s.regs.rbx.toBitVec + 16) 8 (child.toNat : Int) ∧
        Codec.DescAt s.dmem r child desc ∧
        Codec.FieldsAt s.dmem r (s.regs.rbx.toBitVec + 24) rest := by
      cases owned.stored with
      | fieldsCons _ _ _ pointer stored rest => exact ⟨_, pointer, stored, rest⟩
    have childSpace : 8 + stackBytes desc ≤ bytes :=
      (fieldsStackBytes_head name desc rest).trans owned.enough
    have enough : 8 ≤ bytes := by omega
    apply fields_guard e base hc
    intro guardFlags
    rw [if_neg nonzero]
    let guarded : MachineData := {s with status := guardFlags}
    apply child_prepare e base hc guarded child _ childLoad.load
    intro childFlags
    let prepared := childState guarded child childFlags
    have prefixPrepared : Prefix s prepared bytes :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
    have childOwned := child_owned prepared base r desc bytes childStored owned.table
      owned.table_readonly owned.stack childSpace owned.above owned.readonly
    apply call_runs e base hc prepared
    · have slot := owned.stack.substack 0 8 enough
      simpa only [BitVec.ofNat_zero, BitVec.sub_zero, BitVec.add_zero] using
        Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 slot.mapped (by decide)
    · apply eventually_trans (step e)
        (Post (callState prepared (base + 114).toBitVec) desc (base + 114).toBitVec (bytes - 8)) _ _
      · exact children (name, desc) (by simp) _ r _ _ childOwned
      · intro t childPost
        have prefixChild := prefixPrepared.trans (child_prefix prepared base desc bytes enough t childPost)
        have pc : t.2 = base + 114 := by
          simpa only [Int64.ofBitVec_toBitVec] using childPost.returned.pc
        rcases t with ⟨t, at⟩
        dsimp only at pc
        rw [pc]
        apply child_continue e base hc
        intro flags
        let next := decremented t flags
        have prefixNext : Prefix s next bytes := prefixChild.trans
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ h => h⟩
        have childResult := childPost.result
        cases value : FixedSize.isFixed desc with
        | false =>
          have zero : t.regs.rax.toBitVec.setWidth 8 = 0 := by
            simpa only [value, Bool.false_eq_true, ↓reduceIte] using childResult
          rw [if_pos zero]
          apply eventually_trans (step e) (BodyPost next bytes false base) _ _
          · exact false_body e base hc next bytes
          · intro t post
            apply Eventually.done
            simpa only [FixedSize.fieldsFixed, value, Bool.false_and] using post.preceded prefixNext
        | true =>
          have nonzero : t.regs.rax.toBitVec.setWidth 8 ≠ 0 := by
            have one : t.regs.rax.toBitVec.setWidth 8 = 1 := by
              simpa only [value, ↓reduceIte] using childResult
            rw [one]
            decide
          rw [if_neg nonzero]
          have pointer : next.regs.rbx.toBitVec = s.regs.rbx.toBitVec + 24 := by
            change t.regs.rbx.toBitVec = _
            rw [childPost.returned.rbx]
            rfl
          have counter : next.regs.r14.toBitVec = BitVec.ofNat 64 (24 * rest.length) := by
            change t.regs.r14.toBitVec - 24 = _
            rw [childPost.returned.r14]
            change s.regs.r14.toBitVec - 24 = _
            rw [owned.counter]
            simp only [List.length_cons]
            bv_omega
          have nextOwned : FieldsOwned next base r rest bytes := by
            refine ⟨?_, counter, ?_, ?_, owned.table_readonly, ?_,
              (fieldsStackBytes_tail name desc rest).trans owned.enough, ?_, ?_⟩
            · rw [pointer]
              exact restStored.frame prefixNext.frame owned.readonly
            · have bound := owned.byteBound
              simp only [List.length_cons] at bound
              omega
            · exact table_frame owned.table owned.table_readonly prefixNext.frame owned.readonly
            · rw [prefixNext.stack]
              exact ⟨owned.stack.lowEnough, prefixNext.mapped _ _ owned.stack.mapped⟩
            · simpa only [prefixNext.stack] using owned.above
            · simpa only [prefixNext.stack] using owned.readonly
          apply eventually_trans (step e) (BodyPost next bytes (FixedSize.fieldsFixed rest) base) _ _
          · exact ih (fun field member => children field (by simp [member])) next nextOwned
          · intro t post
            apply Eventually.done
            simpa only [FixedSize.fieldsFixed, value, Bool.true_and] using post.preceded prefixNext

end SszX86.CodecIsFixed

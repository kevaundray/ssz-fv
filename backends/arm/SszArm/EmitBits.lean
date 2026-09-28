import SszArm.EmitBitsVectorAligned
import SszArm.EmitBitsVectorTail
import SszArm.EmitBitsListAligned
import SszArm.EmitBitsListTail

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)

/-- The actual private emitter's complete packed-bit body. The descriptor tag
selects the original vector/list machine path; all helper ownership and panic
exclusions follow from the original observations and successful logical size.
No logical capacity narrowing or clean input padding is required. -/
theorem body_correct (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat) (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64) (tag : r (.GPR 8#5) s = descriptorTag desc) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args desc (.bits bits) size base := by
  obtain ⟨prepareRun, preparePC⟩ := prepare_run s base args desc bits size kind owned registers
    code error aligned pc tag
  have copyPost := copy_prepared_correct (pathOf desc) base kind owned registers code error preparePC
  have input := copied_owned (pathOf desc) kind owned registers copyPost
  have work := copied_work (pathOf desc) kind owned registers copyPost
  have prefixBytes := copied_prefix (pathOf desc) owned registers copyPost
  have copyCode : CodeAt (copied (pathOf desc) s bits) base := by
    simpa only [CodeAt, copyPost.program, prepared_program] using code
  have copyAligned := aligned_of_stack aligned (work.stack.trans registers.stack.symm)
  obtain ⟨suffixFuel, t, suffixRun, post⟩ : ∃ fuel t,
      run fuel (copied (pathOf desc) s bits) = t ∧
      Produced (copied (pathOf desc) s bits) t args desc (.bits bits) size base := by
    cases desc with
    | bitVector length =>
      by_cases byteAligned : bits.count.toNat % 8 = 0
      · obtain ⟨t, execution, post⟩ := vector_aligned_suffix _ base args length bits size input work
          byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨4, t, execution, post⟩
      · obtain ⟨t, execution, post⟩ := vector_tail_suffix _ base args length bits size input work
          byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨28, t, execution, post⟩
    | bitList limit =>
      by_cases byteAligned : bits.count.toNat % 8 = 0
      · obtain ⟨t, execution, post⟩ := list_aligned_suffix _ base args (.bitList limit) bits size trivial
          input work byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨14, t, execution, post⟩
      · obtain ⟨t, execution, post⟩ := list_tail_suffix _ base args (.bitList limit) bits size trivial
          input work byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨34, t, execution, post⟩
    | progressiveBitList limit =>
      by_cases byteAligned : bits.count.toNat % 8 = 0
      · obtain ⟨t, execution, post⟩ := list_aligned_suffix _ base args (.progressiveBitList limit) bits size trivial
          input work byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨14, t, execution, post⟩
      · obtain ⟨t, execution, post⟩ := list_tail_suffix _ base args (.progressiveBitList limit) bits size trivial
          input work byteAligned prefixBytes copyCode copyPost.error copyAligned copyPost.pc
        exact ⟨34, t, execution, post⟩
    | _ => cases kind
  refine ⟨(pathOf desc).prepareFuel + ((Memcpy.fuel (bits.count.toNat / 8) + 1) + suffixFuel), t, ?_, ?_⟩
  · rw [run_plus, prepareRun, run_plus]
    exact suffixRun
  · exact prepend_copy (pathOf desc) kind owned registers copyPost post

end SszArm.Emit.Bits

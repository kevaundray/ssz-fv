import SszArm.HashCombineProofs
import SszArm.HashPost

namespace SszArm.Hash

/-- An initially represented stream refines the pinned hash through the actual
finalizer RET; the logical input is not a machine-execution assumption. -/
theorem finalize_hash_correct (s : ArmState) (base : BitVec 64) (value : StreamState)
    (input : ByteArray) (represents : SszNative.HashStream.Represents value input.data.toList)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base + finalizeOffset) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : FinalizeOwned s base value) :
    ∃ fuel, let t := run fuel s
      Returned s t ∧ BytesAt t (r (.GPR 0#5) s) (Ssz.Sha256.hash input) ∧
      Delimited.MemoryFrame (finalizeWrites s) s t ∧ DataAt t base := by
  obtain ⟨fuel, post⟩ := finalize_correct s base value code data compression pc error aligned owned
  exact ⟨fuel, post.returned, post.pinned input represents, post.frame, post.data owned data⟩

/-- Arbitrary raw slices, including empty and mutually aliased inputs, refine
hashing their mathematical concatenation without a native concatenation copy. -/
theorem combine_hash_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    ∃ fuel, let t := run fuel s
      Returned s t ∧ BytesAt t (r (.GPR 0#5) s) (Ssz.Sha256.hash (left ++ right)) ∧
      Delimited.MemoryFrame (combineWrites s) s t ∧
      BytesAt t (r (.GPR 1#5) s) left ∧ BytesAt t (r (.GPR 3#5) s) right ∧ DataAt t base := by
  obtain ⟨fuel, post⟩ := combine_correct s base left right code data compression pc error aligned owned
  exact ⟨fuel, post.returned, post.hash, post.frame, post.left, post.right, post.data owned data⟩

/-- The public SSZ combine corollary preserves the same native execution and
ownership contract; neither input is restricted to a digest-sized chunk. -/
theorem combine_ssz_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (compression : CompressionCorrect base)
    (pc : read_pc s = base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    ∃ fuel, let t := run fuel s
      Returned s t ∧ BytesAt t (r (.GPR 0#5) s) ⟨Ssz.combine left.data right.data⟩ ∧
      Delimited.MemoryFrame (combineWrites s) s t ∧
      BytesAt t (r (.GPR 1#5) s) left ∧ BytesAt t (r (.GPR 3#5) s) right ∧ DataAt t base := by
  obtain ⟨fuel, post⟩ := combine_correct s base left right code data compression pc error aligned owned
  exact ⟨fuel, post.returned, post.pinned, post.frame, post.left, post.right, post.data owned data⟩

end SszArm.Hash

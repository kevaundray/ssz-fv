import SszArm.HashMemory

namespace SszArm.Hash

open Delimited (Span Protected MemoryFrame)

/-- The exact finalizer output relation has precisely 32 observable bytes. -/
theorem FinalizePost.digest (s t : ArmState) (value : StreamState)
    (post : FinalizePost s t value) :
    (SszNative.HashStream.finalize value).size = 32 ∧
      BytesAt t (r (.GPR 0#5) s) (SszNative.HashStream.finalize value) :=
  ⟨SszNative.HashStream.finalize_size value, post.bytes⟩

theorem FinalizePost.data {s t : ArmState} {base : BitVec 64} {value : StreamState}
    (post : FinalizePost s t value) (owned : FinalizeOwned s base value)
    (data : DataAt s base) : DataAt t base :=
  data.frame post.frame owned.initialOwned owned.roundsOwned

theorem FinalizePost.pinned {s t : ArmState} {value : StreamState}
    (post : FinalizePost s t value) (input : ByteArray)
    (represents : SszNative.HashStream.Represents value input.data.toList) :
    BytesAt t (r (.GPR 0#5) s) (Ssz.Sha256.hash input) := by
  rw [← SszNative.HashStream.finalize_eq_hash value input represents]
  exact post.bytes

/-- Read-only borrows need not be disjoint from one another. -/
theorem CombinePost.borrow {s t : ArmState} {left right : ByteArray}
    (post : CombinePost s t left right) (address : BitVec 64) (bytes : ByteArray)
    (physical : address.toNat + bytes.size ≤ 2^64)
    (owned : Protected (combineWrites s) address.toNat bytes.size)
    (source : BytesAt s address bytes) : BytesAt t address bytes :=
  bytesAt_frame post.frame physical owned source

theorem CombinePost.data {s t : ArmState} {base : BitVec 64} {left right : ByteArray}
    (post : CombinePost s t left right) (owned : CombineOwned s base left right)
    (data : DataAt s base) : DataAt t base :=
  data.frame post.frame owned.initialOwned owned.roundsOwned

theorem CombinePost.hash {s t : ArmState} {left right : ByteArray}
    (post : CombinePost s t left right) :
    BytesAt t (r (.GPR 0#5) s) (Ssz.Sha256.hash (left ++ right)) := by
  rw [← SszNative.HashStream.combine_eq_hash left right]
  exact post.bytes

/-- This is the raw SSZ combine, without any fixed-width restriction on either slice. -/
theorem CombinePost.pinned {s t : ArmState} {left right : ByteArray}
    (post : CombinePost s t left right) :
    BytesAt t (r (.GPR 0#5) s) ⟨Ssz.combine left.data right.data⟩ := by
  have same : SszNative.HashStream.combine left right =
      ByteArray.mk (Ssz.combine left.data right.data) := by
    apply ByteArray.ext
    exact SszNative.HashStream.combine_eq left.data right.data
  rw [← same]
  exact post.bytes

theorem CombinePost.digest {s t : ArmState} {left right : ByteArray}
    (post : CombinePost s t left right) :
    (SszNative.HashStream.combine left right).size = 32 ∧
      BytesAt t (r (.GPR 0#5) s) (SszNative.HashStream.combine left right) :=
  ⟨SszNative.HashStream.combine_size left right, post.bytes⟩

end SszArm.Hash

import SszArm.HashTables

namespace SszArm.Hash

/-- The initial chaining copy transfers all eight native little-endian words. -/
theorem ChainingAt.of_copy {s t : ArmState} {dst src : BitVec 64}
    {words : Vector UInt32 8} (source : ChainingAt s src words)
    (memory : ∀ a, t.mem a = Memcpy.image s.mem dst src 32 a)
    (dstBound : dst.toNat + 32 ≤ 2^64) (srcBound : src.toNat + 32 ≤ 2^64) :
    ChainingAt t dst words := by
  intro i
  have bound := i.isLt
  rw [read_copy dst src 32 (4 * i.val) 4 memory dstBound srcBound (by omega)]
  exact source i

/-- IV loading uses the linked bytes, not an assumed future initialized state. -/
theorem initial_copy {s t : ArmState} {dst src : BitVec 64}
    (source : TableAt s src initialTable)
    (memory : ∀ a, t.mem a = Memcpy.image s.mem dst src 32 a)
    (dstBound : dst.toNat + 32 ≤ 2^64) (srcBound : src.toNat + 32 ≤ 2^64) :
    ChainingAt t dst Ssz.Sha256.initialState :=
  (initial_chaining s src source srcBound).of_copy memory dstBound srcBound

end SszArm.Hash

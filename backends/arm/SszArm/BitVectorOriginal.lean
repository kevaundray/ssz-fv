import SszArm.BitVectorStageState

namespace SszArm.BitVector

open UintCodec (widthLoad)

theorem Working.byte_count {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (current : Working s c length) (owned : Owned s length data) :
    r (.GPR 20#5) c = BitVec.ofNat 64 data.size := by
  rw [current.size, ← owned.length]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem original_bytes {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (frame : Delimited.MemoryFrame (writesFor s (outcome s length data)) s c) :
    SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data := by
  intro index within
  have bound := owned.inputBound
  rw [frame.load _ 1 (by omega) (owned.inputOwned.subspan index 1 (by omega))]
  exact owned.input index within

theorem construct_of_scope {s : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true) :
    SszNative.BitVector.construct length data = .ok (BitVec.ofNat 128 length.value) := by
  have bounded := SszNative.BitVector.scope_narrows length expected remainder
    (BitVec.ofNat 64 data.size) arithmetic scope
  have size : data.size = ((BitVec.ofNat 128 length.value).toNat + 7) / 8 := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.physical] using bounded.2.2
  simp only [SszNative.BitVector.construct, bounded.2.1, size, if_pos]

end SszArm.BitVector

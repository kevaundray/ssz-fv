import SszArm.CodecLinked

namespace SszArm.Codec.Linked

/-- The complete linked binding depends only on the immutable program map. -/
theorem CodeAt.congr {s t : ArmState} {bias : BitVec 64}
    (code : CodeAt s bias) (same : t.program = s.program) : CodeAt t bias := by
  constructor
  · exact WordsAt.preserve code.serialize same
  · exact WordsAt.preserve code.measure same
  · exact WordsAt.preserve code.emit same
  · exact WordsAt.preserve code.deserialize same
  · exact WordsAt.preserve code.measure_parts same
  · exact WordsAt.preserve code.measure_child same
  · exact WordsAt.preserve code.emit_parts same
  · exact WordsAt.preserve code.is_fixed same
  · exact WordsAt.preserve code.measure_fixed same
  · exact WordsAt.preserve code.decode_fixed same
  · exact WordsAt.preserve code.decode_offsets same
  · exact WordsAt.preserve code.decode_list same
  · exact WordsAt.preserve code.read_offset same
  · exact WordsAt.preserve code.bounded same
  · exact WordsAt.preserve code.nat_cmp_usize same
  · exact WordsAt.preserve code.plan_singleton same
  · exact WordsAt.preserve code.decode_struct_values same
  · exact code.legacySerialize.congr same
  · simpa only [SszArm.Dispatch.CodeAt, same] using code.dispatch
  · simpa only [SszArm.ByteView.CodeAt, same] using code.byteView
  · simpa only [SszArm.BoolCodec.CodeAt, same] using code.boolBody
  · simpa only [SszArm.UintCodec.CodeAt, same] using code.uintBody
  · exact code.bitVector.of_program same
  · constructor
    · simpa only [SszArm.BitList.CodeAt, same] using code.bitList.body
    · simpa only [SszArm.Delimited.CodeAt, same] using code.bitList.delimited
    · simpa only [SszArm.NatCompare.CodeAt, same] using code.bitList.compare
  · simpa only [SszArm.NatCompare.CodeAt, same] using code.compare
  · simpa only [SszArm.NatFromU128.CodeAt, same] using code.fromU128
  · simpa only [SszArm.NatAdd.CodeAt, same] using code.add
  · simpa only [SszArm.NatDivision.JointCodeAt, SszArm.NatDivision.CodeAt,
      SszArm.Udivti3.CodeAt, SszArm.CodeAt, same] using code.division
  · exact code.mul.transport same
  · simpa only [SszArm.NatMulWord.CodeAt, same] using code.mulWord
  · simpa only [SszArm.NatExact.CodeAt, same] using code.exactLeaf
  · simpa only [SszArm.NatToU128.CodeAt, same] using code.toU128
  · simpa only [SszArm.Delimited.CodeAt, same] using code.delimited
  · simpa only [SszArm.CodeAt, same] using code.memcpy

/-- Binding survives arbitrary actual machine execution, including helper calls. -/
theorem CodeAt.run {s : ArmState} {bias : BitVec 64}
    (code : CodeAt s bias) (fuel : Nat) : CodeAt (run fuel s) bias :=
  code.congr (SszArm.BitVector.run_program fuel s)

end SszArm.Codec.Linked

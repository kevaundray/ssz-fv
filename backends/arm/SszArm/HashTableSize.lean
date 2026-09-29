import SszArm.HashImage

namespace SszArm.Hash

private def roundTail0 : List UInt8 := roundsTable

private theorem roundTail0_head_length : (roundTail0.take 32).length = 32 := by decide

private def roundTail1 : List UInt8 := roundTail0.drop 32

private theorem roundTail1_head_length : (roundTail1.take 32).length = 32 := by decide

private def roundTail2 : List UInt8 := roundTail1.drop 32

private theorem roundTail2_head_length : (roundTail2.take 32).length = 32 := by decide

private def roundTail3 : List UInt8 := roundTail2.drop 32

private theorem roundTail3_head_length : (roundTail3.take 32).length = 32 := by decide

private def roundTail4 : List UInt8 := roundTail3.drop 32

private theorem roundTail4_head_length : (roundTail4.take 32).length = 32 := by decide

private def roundTail5 : List UInt8 := roundTail4.drop 32

private theorem roundTail5_head_length : (roundTail5.take 32).length = 32 := by decide

private def roundTail6 : List UInt8 := roundTail5.drop 32

private theorem roundTail6_head_length : (roundTail6.take 32).length = 32 := by decide

private def roundTail7 : List UInt8 := roundTail6.drop 32

private theorem roundTail7_head_length : (roundTail7.take 32).length = 32 := by decide

private theorem roundTail7_end : roundTail7.drop 32 = [] := by decide

private theorem roundTail7_length : roundTail7.length = 32 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail7)
  rw [List.length_append] at split
  rw [roundTail7_head_length, roundTail7_end, List.length_nil, Nat.add_zero] at split
  exact split.symm

private theorem roundTail6_length : roundTail6.length = 64 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail6)
  rw [List.length_append] at split
  change (roundTail6.take 32).length + roundTail7.length = roundTail6.length at split
  rw [roundTail6_head_length, roundTail7_length] at split
  exact split.symm

private theorem roundTail5_length : roundTail5.length = 96 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail5)
  rw [List.length_append] at split
  change (roundTail5.take 32).length + roundTail6.length = roundTail5.length at split
  rw [roundTail5_head_length, roundTail6_length] at split
  exact split.symm

private theorem roundTail4_length : roundTail4.length = 128 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail4)
  rw [List.length_append] at split
  change (roundTail4.take 32).length + roundTail5.length = roundTail4.length at split
  rw [roundTail4_head_length, roundTail5_length] at split
  exact split.symm

private theorem roundTail3_length : roundTail3.length = 160 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail3)
  rw [List.length_append] at split
  rw [← roundTail4] at split
  rw [roundTail3_head_length, roundTail4_length] at split
  exact split.symm

private theorem roundTail2_length : roundTail2.length = 192 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail2)
  rw [List.length_append] at split
  rw [← roundTail3] at split
  rw [roundTail2_head_length, roundTail3_length] at split
  exact split.symm

private theorem roundTail1_length : roundTail1.length = 224 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail1)
  rw [List.length_append] at split
  rw [← roundTail2] at split
  rw [roundTail1_head_length, roundTail2_length] at split
  exact split.symm

private theorem roundTail0_length : roundTail0.length = 256 := by
  have split := congrArg List.length (List.take_append_drop 32 roundTail0)
  rw [List.length_append] at split
  rw [← roundTail1] at split
  rw [roundTail0_head_length, roundTail1_length] at split
  exact split.symm

theorem roundsTable_length : roundsTable.length = 256 := roundTail0_length

end SszArm.Hash

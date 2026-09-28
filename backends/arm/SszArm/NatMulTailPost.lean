import SszArm.NatMulTailOwned

namespace SszArm.NatMul

theorem TailFrame.post {s u t : ArmState} {left right : SszNative.NatOperand}
    (frame : TailFrame s u) (owned : Owned s left right)
    (operand : SszNative.NatOperand) (factor : BitVec 64)
    (model : outcome s left right = SszNative.NatMul.runWord operand factor
      (arenaOf s).base (arenaOf s).capacity (arenaOf s).used)
    (post : NatMulWord.Post u t operand factor) : Post s t left right := by
  have result : NatMulWord.outcome u operand factor = outcome s left right := by
    unfold NatMulWord.outcome
    rw [frame.arenaOf owned]
    exact model.symm
  have helperMemory : Delimited.MemoryFrame (writesFor s (outcome s left right)) u t := by
    apply (frame.writes_covered (outcome s left right)).frame
    simpa only [result] using post.frame
  have memory := ((entry_covered s (outcome s left right)).frame frame.memory).trans helperMemory
  refine ⟨frame.returned post.returned, ?_, ?_, ?_, memory,
    NatAdd.operand_preserved memory left owned.leftAt owned.leftOwned,
    NatAdd.operand_preserved memory right owned.rightAt owned.rightOwned, ?_, ?_⟩
  · simpa only [result, frame.output] using post.result
  · simpa only [result] using post.written
  · simpa only [result, frame.arena] using post.cursor
  · have initial : read_mem_bytes 8 (r (.GPR 4#5) u) u = read_mem_bytes 8 (r (.GPR 5#5) s) s := by
      simpa only [BitVec.ofNat_zero, BitVec.add_zero] using frame.header owned 0 (by decide)
    simpa only [frame.arena] using post.arenaBase.trans initial
  · have initial : read_mem_bytes 8 (r (.GPR 4#5) u + 8#64) u =
        read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s := by
      with_unfolding_all exact frame.header owned 8 (by decide)
    simpa only [frame.arena] using post.arenaCapacity.trans initial

end SszArm.NatMul

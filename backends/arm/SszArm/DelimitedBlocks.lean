import SszArm.DelimitedExec

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def prologueOps : List Op :=
  [.p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44, .p48, .p52, .p56, .p60]

theorem prologue_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 4#64) :
    run 15 s = block base prologueOps s := by
  apply block_run base prologueOps s hc he ha
  have hpc : r .PC s = base + 4#64 := hp
  simp (config := {decide := true, instances := true})
    [prologueOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def clzStartOps : List Op :=
  [.p64, .p68, .p72, .p76, .p80, .p84, .p88, .p92, .p96, .p100]

theorem clzStart_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 64#64) :
    run 10 s = block base clzStartOps s := by
  apply block_run base clzStartOps s hc he ha
  have hpc : r .PC s = base + 64#64 := hp
  simp (config := {decide := true, instances := true})
    [clzStartOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def clzIterationOps : List Op :=
  [.p104, .p108, .p112]

theorem clzIteration_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 104#64) :
    run 3 s = block base clzIterationOps s := by
  apply block_run base clzIterationOps s hc he ha
  have hpc : r .PC s = base + 104#64 := hp
  simp (config := {decide := true, instances := true})
    [clzIterationOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def countOps : List Op :=
  [.p116, .p120, .p124, .p128, .p132, .p136, .p140, .p144]

theorem count_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 116#64) :
    run 8 s = block base countOps s := by
  apply block_run base countOps s hc he ha
  have hpc : r .PC s = base + 116#64 := hp
  simp (config := {decide := true, instances := true})
    [countOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def smallOps : List Op :=
  [.p148, .p152, .p156, .p160, .p164]

theorem small_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 148#64) :
    run 5 s = block base smallOps s := by
  apply block_run base smallOps s hc he ha
  have hpc : r .PC s = base + 148#64 := hp
  simp (config := {decide := true, instances := true})
    [smallOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def noLimitOps : List Op :=
  [.p168]

theorem noLimit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64) :
    run 1 s = block base noLimitOps s := by
  apply block_run base noLimitOps s hc he ha
  have hpc : r .PC s = base + 168#64 := hp
  simp (config := {decide := true, instances := true})
    [noLimitOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def scanByteOps : List Op :=
  [.p172, .p176, .p180]

theorem scanByte_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 172#64) :
    run 3 s = block base scanByteOps s := by
  apply block_run base scanByteOps s hc he ha
  have hpc : r .PC s = base + 172#64 := hp
  simp (config := {decide := true, instances := true})
    [scanByteOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def scanTestOps : List Op :=
  [.p184]

theorem scanTest_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 184#64) :
    run 1 s = block base scanTestOps s := by
  apply block_run base scanTestOps s hc he ha
  have hpc : r .PC s = base + 184#64 := hp
  simp (config := {decide := true, instances := true})
    [scanTestOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def noDelimiterOps : List Op :=
  [.p188, .p192]

theorem noDelimiter_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 188#64) :
    run 2 s = block base noDelimiterOps s := by
  apply block_run base noDelimiterOps s hc he ha
  have hpc : r .PC s = base + 188#64 := hp
  simp (config := {decide := true, instances := true})
    [noDelimiterOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def emptyOps : List Op :=
  [.p196, .p200, .p204, .p208, .p212, .p216, .p220, .p224, .p228, .p232, .p236, .p240, .p244, .p248, .p252, .p256, .p260, .p264]

theorem empty_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 196#64) :
    run 18 s = block base emptyOps s := by
  apply block_run base emptyOps s hc he ha
  have hpc : r .PC s = base + 196#64 := hp
  simp (config := {decide := true, instances := true})
    [emptyOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaAddressOps : List Op :=
  [.p268, .p272, .p276, .p280]

theorem arenaAddress_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 268#64) :
    run 4 s = block base arenaAddressOps s := by
  apply block_run base arenaAddressOps s hc he ha
  have hpc : r .PC s = base + 268#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaAddressOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaRoundOps : List Op :=
  [.p284, .p288]

theorem arenaRound_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 284#64) :
    run 2 s = block base arenaRoundOps s := by
  apply block_run base arenaRoundOps s hc he ha
  have hpc : r .PC s = base + 284#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaRoundOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaAlignOps : List Op :=
  [.p292, .p296, .p300, .p304, .p308]

theorem arenaAlign_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 292#64) :
    run 5 s = block base arenaAlignOps s := by
  apply block_run base arenaAlignOps s hc he ha
  have hpc : r .PC s = base + 292#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaAlignOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaEndOps : List Op :=
  [.p312, .p316]

theorem arenaEnd_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 312#64) :
    run 2 s = block base arenaEndOps s := by
  apply block_run base arenaEndOps s hc he ha
  have hpc : r .PC s = base + 312#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaEndOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaCapacityOps : List Op :=
  [.p320, .p324, .p328, .p332]

theorem arenaCapacity_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 320#64) :
    run 4 s = block base arenaCapacityOps s := by
  apply block_run base arenaCapacityOps s hc he ha
  have hpc : r .PC s = base + 320#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaCapacityOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def arenaCommitOps : List Op :=
  [.p336, .p340, .p344, .p348, .p352, .p356, .p360]

theorem arenaCommit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 336#64) :
    run 7 s = block base arenaCommitOps s := by
  apply block_run base arenaCommitOps s hc he ha
  have hpc : r .PC s = base + 336#64 := hp
  simp (config := {decide := true, instances := true})
    [arenaCommitOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def callPrepareOps : List Op :=
  [.p364, .p368, .p372, .p376, .p380, .p384, .p388, .p392, .p396]

theorem callPrepare_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 364#64) :
    run 9 s = block base callPrepareOps s := by
  apply block_run base callPrepareOps s hc he ha
  have hpc : r .PC s = base + 364#64 := hp
  simp (config := {decide := true, instances := true})
    [callPrepareOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def callReturnOps : List Op :=
  [.p400, .p404, .p408, .p412, .p416, .p420]

theorem callReturn_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 400#64) :
    run 6 s = block base callReturnOps s := by
  apply block_run base callReturnOps s hc he ha
  have hpc : r .PC s = base + 400#64 := hp
  simp (config := {decide := true, instances := true})
    [callReturnOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def overLimitOps : List Op :=
  [.p424, .p428, .p432, .p436, .p440, .p444, .p448, .p452, .p456, .p460, .p464, .p468, .p472, .p476, .p480, .p484, .p488, .p492, .p496, .p500, .p504, .p508, .p512, .p516, .p520, .p524, .p528, .p532, .p536]

theorem overLimit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 424#64) :
    run 29 s = block base overLimitOps s := by
  apply block_run base overLimitOps s hc he ha
  have hpc : r .PC s = base + 424#64 := hp
  simp (config := {decide := true, instances := true})
    [overLimitOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def representationTestOps : List Op :=
  [.p540, .p544]

theorem representationTest_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 540#64) :
    run 2 s = block base representationTestOps s := by
  apply block_run base representationTestOps s hc he ha
  have hpc : r .PC s = base + 540#64 := hp
  simp (config := {decide := true, instances := true})
    [representationTestOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def alignedByteOps : List Op :=
  [.p548, .p552]

theorem alignedByte_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 548#64) :
    run 2 s = block base alignedByteOps s := by
  apply block_run base alignedByteOps s hc he ha
  have hpc : r .PC s = base + 548#64 := hp
  simp (config := {decide := true, instances := true})
    [alignedByteOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def unalignedByteOps : List Op :=
  [.p556]

theorem unalignedByte_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 556#64) :
    run 1 s = block base unalignedByteOps s := by
  apply block_run base unalignedByteOps s hc he ha
  have hpc : r .PC s = base + 556#64 := hp
  simp (config := {decide := true, instances := true})
    [unalignedByteOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def representationSumOps : List Op :=
  [.p560, .p564, .p568]

theorem representationSum_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 560#64) :
    run 3 s = block base representationSumOps s := by
  apply block_run base representationSumOps s hc he ha
  have hpc : r .PC s = base + 560#64 := hp
  simp (config := {decide := true, instances := true})
    [representationSumOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def noOverflowOps : List Op :=
  [.p572, .p576]

theorem noOverflow_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 572#64) :
    run 2 s = block base noOverflowOps s := by
  apply block_run base noOverflowOps s hc he ha
  have hpc : r .PC s = base + 572#64 := hp
  simp (config := {decide := true, instances := true})
    [noOverflowOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def overflowOps : List Op :=
  [.p580]

theorem overflow_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 580#64) :
    run 1 s = block base overflowOps s := by
  apply block_run base overflowOps s hc he ha
  have hpc : r .PC s = base + 580#64 := hp
  simp (config := {decide := true, instances := true})
    [overflowOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def representationJoinOps : List Op :=
  [.p584, .p588, .p592]

theorem representationJoin_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 584#64) :
    run 3 s = block base representationJoinOps s := by
  apply block_run base representationJoinOps s hc he ha
  have hpc : r .PC s = base + 584#64 := hp
  simp (config := {decide := true, instances := true})
    [representationJoinOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def successOps : List Op :=
  [.p596, .p600, .p604, .p608, .p612]

theorem success_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 596#64) :
    run 5 s = block base successOps s := by
  apply block_run base successOps s hc he ha
  have hpc : r .PC s = base + 596#64 := hp
  simp (config := {decide := true, instances := true})
    [successOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def trailingOps : List Op :=
  [.p616]

theorem trailing_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 616#64) :
    run 1 s = block base trailingOps s := by
  apply block_run base trailingOps s hc he ha
  have hpc : r .PC s = base + 616#64 := hp
  simp (config := {decide := true, instances := true})
    [trailingOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def invalidOps : List Op :=
  [.p620, .p624, .p628, .p632, .p636, .p640, .p644, .p648, .p652, .p656, .p660, .p664, .p668, .p672, .p676, .p680]

theorem invalid_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 620#64) :
    run 16 s = block base invalidOps s := by
  apply block_run base invalidOps s hc he ha
  have hpc : r .PC s = base + 620#64 := hp
  simp (config := {decide := true, instances := true})
    [invalidOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def badRepresentationOps : List Op :=
  [.p684, .p688, .p692, .p696, .p700, .p704, .p708, .p712, .p716, .p720, .p724, .p728, .p732, .p736, .p740, .p744, .p748]

theorem badRepresentation_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 684#64) :
    run 17 s = block base badRepresentationOps s := by
  apply block_run base badRepresentationOps s hc he ha
  have hpc : r .PC s = base + 684#64 := hp
  simp (config := {decide := true, instances := true})
    [badRepresentationOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def scratchOps : List Op :=
  [.p752, .p756, .p760, .p764, .p768, .p772, .p776, .p780, .p784, .p788, .p792, .p796, .p800, .p804, .p808, .p812, .p816, .p820, .p824, .p828, .p832, .p836, .p840, .p844, .p848, .p852, .p856, .p860, .p864, .p868, .p872, .p876, .p880, .p884, .p888, .p892, .p896, .p900, .p904, .p908, .p912]

theorem scratch_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 752#64) :
    run 41 s = block base scratchOps s := by
  apply block_run base scratchOps s hc he ha
  have hpc : r .PC s = base + 752#64 := hp
  simp (config := {decide := true, instances := true})
    [scratchOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def tagsOps : List Op :=
  [.p916, .p920, .p924, .p928, .p932, .p936, .p940, .p944, .p948, .p952, .p956, .p960, .p964, .p968, .p972, .p976]

theorem tags_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 916#64) :
    run 16 s = block base tagsOps s := by
  apply block_run base tagsOps s hc he ha
  have hpc : r .PC s = base + 916#64 := hp
  simp (config := {decide := true, instances := true})
    [tagsOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

def epilogueOps : List Op :=
  [.p980, .p984, .p988, .p992, .p996, .p1000, .p1004, .p1008]

theorem epilogue_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 980#64) :
    run 8 s = block base epilogueOps s := by
  apply block_run base epilogueOps s hc he ha
  have hpc : r .PC s = base + 980#64 := hp
  simp (config := {decide := true, instances := true})
    [epilogueOps, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, hpc, BitVec.add_assoc]

end SszArm.Delimited

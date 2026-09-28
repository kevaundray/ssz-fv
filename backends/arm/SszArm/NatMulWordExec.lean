import SszArm.NatMulWordWords00
import SszArm.NatMulWordWords01
import SszArm.NatMulWordWords02
import SszArm.NatMulWordWords03
import SszArm.NatMulWordWords04
import SszArm.NatMulWordWords05
import SszArm.NatMulWordWords06
import SszArm.NatMulWordWords07
import SszArm.NatMulWordWords08
import SszArm.NatMulWordWords09
import SszArm.NatMulWordWords10
import SszArm.NatMulWordMembership

namespace SszArm.NatMulWord

theorem Op.mem_program (op : Op) : op.row ∈ program := by
  cases op <;> simp

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hf : s.program.find? (read_pc s) = some op.row.2 := by
    rw [hp]
    exact hc op.row op.mem_program
  cases op
  case p0 => simpa only [Op.effect] using word_p0 s base he ha hf
  case p4 => simpa only [Op.effect] using word_p4 s base he ha hf hp
  case p8 => simpa only [Op.effect] using word_p8 s base he ha hf hp
  case p12 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p16 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p20 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p24 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p28 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p32 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p36 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p40 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p44 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p48 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p52 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p56 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p60 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p64 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p68 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p72 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p76 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p80 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p84 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p88 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p92 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p96 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p100 => simpa only [Op.effect] using word_p100 s base he ha hf hp
  case p104 => simpa only [Op.effect] using word_p104 s base he ha hf
  case p108 => simpa only [Op.effect] using word_p108 s base he ha hf
  case p112 => simpa only [Op.effect] using word_p112 s base he ha hf hp
  case p116 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p120 => simpa only [Op.effect] using word_p120 s base he ha hf
  case p124 => simpa only [Op.effect] using word_p124 s base he ha hf
  case p128 => simpa only [Op.effect] using word_p128 s base he ha hf
  case p132 => simpa only [Op.effect] using word_p132 s base he ha hf
  case p136 => simpa only [Op.effect] using word_p136 s base he ha hf
  case p140 => simpa only [Op.effect] using word_p140 s base he ha hf
  case p144 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p148 => simpa only [Op.effect] using word_p148 s base he ha hf
  case p152 => simpa only [Op.effect] using word_p152 s base he ha hf
  case p156 => simpa only [Op.effect] using word_p156 s base he ha hf hp
  case p160 => simpa only [Op.effect] using word_p160 s base he ha hf
  case p164 => simpa only [Op.effect] using word_p164 s base he ha hf
  case p168 => simpa only [Op.effect] using word_p168 s base he ha hf hp
  case p172 => simpa only [Op.effect] using word_p172 s base he ha hf
  case p176 => simpa only [Op.effect] using word_p176 s base he ha hf
  case p180 => simpa only [Op.effect] using word_p180 s base he ha hf
  case p184 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p188 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p192 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p196 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p200 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p204 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p208 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p212 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p216 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p220 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p224 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p228 => simpa only [Op.effect] using word_p228 s base he ha hf hp
  case p232 => simpa only [Op.effect] using word_p232 s base he ha hf
  case p236 => simpa only [Op.effect] using word_p236 s base he ha hf
  case p240 => simpa only [Op.effect] using word_p240 s base he ha hf
  case p244 => simpa only [Op.effect] using word_p244 s base he ha hf
  case p248 => simpa only [Op.effect] using word_p248 s base he ha hf
  case p252 => simpa only [Op.effect] using word_p252 s base he ha hf
  case p256 => simpa only [Op.effect] using word_p256 s base he ha hf hp
  case p260 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p264 => simpa only [Op.effect] using word_p264 s base he ha hf
  case p268 => simpa only [Op.effect] using word_p268 s base he ha hf
  case p272 => simpa only [Op.effect] using word_p272 s base he ha hf
  case p276 => simpa only [Op.effect] using word_p276 s base he ha hf
  case p280 => simpa only [Op.effect] using word_p280 s base he ha hf
  case p284 => simpa only [Op.effect] using word_p284 s base he ha hf
  case p288 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p292 => simpa only [Op.effect] using word_p292 s base he ha hf
  case p296 => simpa only [Op.effect] using word_p152 s base he ha hf
  case p300 => simpa only [Op.effect] using word_p300 s base he ha hf hp
  case p304 => simpa only [Op.effect] using word_p304 s base he ha hf
  case p308 => simpa only [Op.effect] using word_p308 s base he ha hf
  case p312 => simpa only [Op.effect] using word_p312 s base he ha hf
  case p316 => simpa only [Op.effect] using word_p316 s base he ha hf hp
  case p320 => simpa only [Op.effect] using word_p108 s base he ha hf
  case p324 => simpa only [Op.effect] using word_p324 s base he ha hf hp
  case p328 => simpa only [Op.effect] using word_p328 s base he ha hf
  case p332 => simpa only [Op.effect] using word_p332 s base he ha hf
  case p336 => simpa only [Op.effect] using word_p336 s base he ha hf hp
  case p340 => simpa only [Op.effect] using word_p340 s base he ha hf
  case p344 => simpa only [Op.effect] using word_p344 s base he ha hf
  case p348 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p352 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p356 => simpa only [Op.effect] using word_p356 s base he ha hf
  case p360 => simpa only [Op.effect] using word_p360 s base he ha hf hp
  case p364 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p368 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p372 => simpa only [Op.effect] using word_p372 s base he ha hf hp
  case p376 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p380 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p384 => simpa only [Op.effect] using word_p384 s base he ha hf hp
  case p388 => simpa only [Op.effect] using word_p388 s base he ha hf
  case p392 => simpa only [Op.effect] using word_p392 s base he ha hf
  case p396 => simpa only [Op.effect] using word_p396 s base he ha hf
  case p400 => simpa only [Op.effect] using word_p400 s base he ha hf hp
  case p404 => simpa only [Op.effect] using word_p404 s base he ha hf
  case p408 => simpa only [Op.effect] using word_p408 s base he ha hf hp
  case p412 => simpa only [Op.effect] using word_p412 s base he ha hf
  case p416 => simpa only [Op.effect] using word_p416 s base he ha hf
  case p420 => simpa only [Op.effect] using word_p420 s base he ha hf
  case p424 => simpa only [Op.effect] using word_p424 s base he ha hf
  case p428 => simpa only [Op.effect] using word_p428 s base he ha hf hp
  case p432 => simpa only [Op.effect] using word_p432 s base he ha hf
  case p436 => simpa only [Op.effect] using word_p436 s base he ha hf hp
  case p440 => simpa only [Op.effect] using word_p440 s base he ha hf
  case p444 => simpa only [Op.effect] using word_p444 s base he ha hf
  case p448 => simpa only [Op.effect] using word_p448 s base he ha hf hp
  case p452 => simpa only [Op.effect] using word_p452 s base he ha hf
  case p456 => simpa only [Op.effect] using word_p456 s base he ha hf
  case p460 => simpa only [Op.effect] using word_p460 s base he ha hf
  case p464 => simpa only [Op.effect] using word_p464 s base he ha hf
  case p468 => simpa only [Op.effect] using word_p468 s base he ha hf
  case p472 => simpa only [Op.effect] using word_p472 s base he ha hf
  case p476 => simpa only [Op.effect] using word_p476 s base he ha hf
  case p480 => simpa only [Op.effect] using word_p480 s base he ha hf
  case p484 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p488 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p492 => simpa only [Op.effect] using word_p492 s base he ha hf
  case p496 => simpa only [Op.effect] using word_p496 s base he ha hf
  case p500 => simpa only [Op.effect] using word_p500 s base he ha hf
  case p504 => simpa only [Op.effect] using word_p504 s base he ha hf
  case p508 => simpa only [Op.effect] using word_p508 s base he ha hf
  case p512 => simpa only [Op.effect] using word_p512 s base he ha hf
  case p516 => simpa only [Op.effect] using word_p516 s base he ha hf
  case p520 => simpa only [Op.effect] using word_p520 s base he ha hf
  case p524 => simpa only [Op.effect] using word_p524 s base he ha hf
  case p528 => simpa only [Op.effect] using word_p528 s base he ha hf
  case p532 => simpa only [Op.effect] using word_p532 s base he ha hf
  case p536 => simpa only [Op.effect] using word_p536 s base he ha hf
  case p540 => simpa only [Op.effect] using word_p540 s base he ha hf
  case p544 => simpa only [Op.effect] using word_p544 s base he ha hf
  case p548 => simpa only [Op.effect] using word_p548 s base he ha hf
  case p552 => simpa only [Op.effect] using word_p552 s base he ha hf
  case p556 => simpa only [Op.effect] using word_p556 s base he ha hf
  case p560 => simpa only [Op.effect] using word_p560 s base he ha hf
  case p564 => simpa only [Op.effect] using word_p564 s base he ha hf
  case p568 => simpa only [Op.effect] using word_p568 s base he ha hf
  case p572 => simpa only [Op.effect] using word_p572 s base he ha hf
  case p576 => simpa only [Op.effect] using word_p576 s base he ha hf
  case p580 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p584 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p588 => simpa only [Op.effect] using word_p588 s base he ha hf
  case p592 => simpa only [Op.effect] using word_p592 s base he ha hf
  case p596 => simpa only [Op.effect] using word_p596 s base he ha hf hp
  case p600 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p604 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p608 => simpa only [Op.effect] using word_p608 s base he ha hf
  case p612 => simpa only [Op.effect] using word_p612 s base he ha hf
  case p616 => simpa only [Op.effect] using word_p616 s base he ha hf
  case p620 => simpa only [Op.effect] using word_p620 s base he ha hf
  case p624 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p628 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p632 => simpa only [Op.effect] using word_p632 s base he ha hf
  case p636 => simpa only [Op.effect] using word_p480 s base he ha hf
  case p640 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p644 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p648 => simpa only [Op.effect] using word_p492 s base he ha hf
  case p652 => simpa only [Op.effect] using word_p496 s base he ha hf
  case p656 => simpa only [Op.effect] using word_p500 s base he ha hf
  case p660 => simpa only [Op.effect] using word_p660 s base he ha hf
  case p664 => simpa only [Op.effect] using word_p664 s base he ha hf
  case p668 => simpa only [Op.effect] using word_p668 s base he ha hf
  case p672 => simpa only [Op.effect] using word_p516 s base he ha hf
  case p676 => simpa only [Op.effect] using word_p520 s base he ha hf
  case p680 => simpa only [Op.effect] using word_p524 s base he ha hf
  case p684 => simpa only [Op.effect] using word_p528 s base he ha hf
  case p688 => simpa only [Op.effect] using word_p532 s base he ha hf
  case p692 => simpa only [Op.effect] using word_p536 s base he ha hf
  case p696 => simpa only [Op.effect] using word_p696 s base he ha hf
  case p700 => simpa only [Op.effect] using word_p700 s base he ha hf
  case p704 => simpa only [Op.effect] using word_p704 s base he ha hf
  case p708 => simpa only [Op.effect] using word_p552 s base he ha hf
  case p712 => simpa only [Op.effect] using word_p712 s base he ha hf
  case p716 => simpa only [Op.effect] using word_p716 s base he ha hf
  case p720 => simpa only [Op.effect] using word_p720 s base he ha hf
  case p724 => simpa only [Op.effect] using word_p568 s base he ha hf
  case p728 => simpa only [Op.effect] using word_p572 s base he ha hf
  case p732 => simpa only [Op.effect] using word_p576 s base he ha hf
  case p736 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p740 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p744 => simpa only [Op.effect] using word_p588 s base he ha hf
  case p748 => simpa only [Op.effect] using word_p748 s base he ha hf
  case p752 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p756 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p760 => simpa only [Op.effect] using word_p608 s base he ha hf
  case p764 => simpa only [Op.effect] using word_p612 s base he ha hf
  case p768 => simpa only [Op.effect] using word_p768 s base he ha hf
  case p772 => simpa only [Op.effect] using word_p772 s base he ha hf
  case p776 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p780 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p784 => simpa only [Op.effect] using word_p784 s base he ha hf
  case p788 => simpa only [Op.effect] using word_p788 s base he ha hf hp
  case p792 => simpa only [Op.effect] using word_p792 s base he ha hf
  case p796 => simpa only [Op.effect] using word_p796 s base he ha hf hp
  case p800 => simpa only [Op.effect] using word_p800 s base he ha hf
  case p804 => simpa only [Op.effect] using word_p804 s base he ha hf
  case p808 => simpa only [Op.effect] using word_p808 s base he ha hf hp
  case p812 => simpa only [Op.effect] using word_p812 s base he ha hf
  case p816 => simpa only [Op.effect] using word_p816 s base he ha hf
  case p820 => simpa only [Op.effect] using word_p820 s base he ha hf hp
  case p824 => simpa only [Op.effect] using word_p824 s base he ha hf
  case p828 => simpa only [Op.effect] using word_p828 s base he ha hf hp
  case p832 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p836 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p840 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p844 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p848 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p852 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p856 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p860 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p864 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p868 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p872 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p876 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p880 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p884 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p888 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p892 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p896 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p900 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p904 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p908 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p912 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p916 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p920 => simpa only [Op.effect] using word_p920 s base he ha hf hp
  case p924 => simpa only [Op.effect] using word_p172 s base he ha hf
  case p928 => simpa only [Op.effect] using word_p480 s base he ha hf
  case p932 => simpa only [Op.effect] using word_p932 s base he ha hf
  case p936 => simpa only [Op.effect] using word_p936 s base he ha hf
  case p940 => simpa only [Op.effect] using word_p940 s base he ha hf
  case p944 => simpa only [Op.effect] using word_p944 s base he ha hf
  case p948 => simpa only [Op.effect] using word_p948 s base he ha hf
  case p952 => simpa only [Op.effect] using word_p504 s base he ha hf
  case p956 => simpa only [Op.effect] using word_p956 s base he ha hf
  case p960 => simpa only [Op.effect] using word_p960 s base he ha hf
  case p964 => simpa only [Op.effect] using word_p964 s base he ha hf
  case p968 => simpa only [Op.effect] using word_p968 s base he ha hf
  case p972 => simpa only [Op.effect] using word_p972 s base he ha hf
  case p976 => simpa only [Op.effect] using word_p704 s base he ha hf
  case p980 => simpa only [Op.effect] using word_p980 s base he ha hf
  case p984 => simpa only [Op.effect] using word_p984 s base he ha hf
  case p988 => simpa only [Op.effect] using word_p988 s base he ha hf
  case p992 => simpa only [Op.effect] using word_p992 s base he ha hf
  case p996 => simpa only [Op.effect] using word_p548 s base he ha hf
  case p1000 => simpa only [Op.effect] using word_p1000 s base he ha hf
  case p1004 => simpa only [Op.effect] using word_p1004 s base he ha hf
  case p1008 => simpa only [Op.effect] using word_p1008 s base he ha hf
  case p1012 => simpa only [Op.effect] using word_p564 s base he ha hf
  case p1016 => simpa only [Op.effect] using word_p1016 s base he ha hf
  case p1020 => simpa only [Op.effect] using word_p1020 s base he ha hf
  case p1024 => simpa only [Op.effect] using word_p1024 s base he ha hf
  case p1028 => simpa only [Op.effect] using word_p1028 s base he ha hf
  case p1032 => simpa only [Op.effect] using word_p1032 s base he ha hf
  case p1036 => simpa only [Op.effect] using word_p588 s base he ha hf
  case p1040 => simpa only [Op.effect] using word_p1040 s base he ha hf
  case p1044 => simpa only [Op.effect] using word_p1044 s base he ha hf hp
  case p1048 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1052 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1056 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1060 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1064 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1068 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1072 => simpa only [Op.effect] using word_p1072 s base he ha hf
  case p1076 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1080 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1084 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1088 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1092 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1096 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1100 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1104 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p1108 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p1112 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p1116 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1120 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1124 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1128 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p1132 => simpa only [Op.effect] using word_p388 s base he ha hf
  case p1136 => simpa only [Op.effect] using word_p1136 s base he ha hf
  case p1140 => simpa only [Op.effect] using word_p1140 s base he ha hf
  case p1144 => simpa only [Op.effect] using word_p1144 s base he ha hf hp
  case p1148 => simpa only [Op.effect] using word_p1148 s base he ha hf
  case p1152 => simpa only [Op.effect] using word_p1152 s base he ha hf hp
  case p1156 => simpa only [Op.effect] using word_p1156 s base he ha hf
  case p1160 => simpa only [Op.effect] using word_p1160 s base he ha hf
  case p1164 => simpa only [Op.effect] using word_p1164 s base he ha hf
  case p1168 => simpa only [Op.effect] using word_p1168 s base he ha hf
  case p1172 => simpa only [Op.effect] using word_p1172 s base he ha hf hp
  case p1176 => simpa only [Op.effect] using word_p1176 s base he ha hf
  case p1180 => simpa only [Op.effect] using word_p1180 s base he ha hf hp
  case p1184 => simpa only [Op.effect] using word_p1184 s base he ha hf
  case p1188 => simpa only [Op.effect] using word_p1188 s base he ha hf
  case p1192 => simpa only [Op.effect] using word_p1192 s base he ha hf
  case p1196 => simpa only [Op.effect] using word_p1196 s base he ha hf hp
  case p1200 => simpa only [Op.effect] using word_p1200 s base he ha hf
  case p1204 => simpa only [Op.effect] using word_p1204 s base he ha hf
  case p1208 => simpa only [Op.effect] using word_p1208 s base he ha hf
  case p1212 => simpa only [Op.effect] using word_p1212 s base he ha hf
  case p1216 => simpa only [Op.effect] using word_p1216 s base he ha hf
  case p1220 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1224 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1228 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1232 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1236 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p1240 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p1244 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p1248 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1252 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1256 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1260 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p1264 => simpa only [Op.effect] using word_p1264 s base he ha hf
  case p1268 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1272 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1276 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1280 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1284 => simpa only [Op.effect] using word_p1284 s base he ha hf
  case p1288 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1292 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1296 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1300 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1304 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1308 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1312 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1316 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1320 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1324 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1328 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1332 => simpa only [Op.effect] using word_p1332 s base he ha hf
  case p1336 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1340 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1344 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1348 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1352 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1356 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1360 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1364 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1368 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1372 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1376 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1380 => simpa only [Op.effect] using word_p1380 s base he ha hf
  case p1384 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1388 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1392 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1396 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1400 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1404 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1408 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1412 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1416 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1420 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1424 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1428 => simpa only [Op.effect] using word_p1428 s base he ha hf
  case p1432 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1436 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1440 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1444 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1448 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1452 => simpa only [Op.effect] using word_p1452 s base he ha hf
  case p1456 => simpa only [Op.effect] using word_p1456 s base he ha hf
  case p1460 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p1464 => simpa only [Op.effect] using word_p1464 s base he ha hf
  case p1468 => simpa only [Op.effect] using word_p1468 s base he ha hf
  case p1472 => simpa only [Op.effect] using word_p1472 s base he ha hf hp
  case p1476 => simpa only [Op.effect] using word_p1476 s base he ha hf
  case p1480 => simpa only [Op.effect] using word_p1480 s base he ha hf hp
  case p1484 => simpa only [Op.effect] using word_p1484 s base he ha hf
  case p1488 => simpa only [Op.effect] using word_p1488 s base he ha hf
  case p1492 => simpa only [Op.effect] using word_p1492 s base he ha hf
  case p1496 => simpa only [Op.effect] using word_p1496 s base he ha hf
  case p1500 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1504 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1508 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1512 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1516 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p1520 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p1524 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p1528 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1532 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1536 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1540 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p1544 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1548 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1552 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1556 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1560 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1564 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1568 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1572 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1576 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1580 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1584 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1588 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1592 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1596 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1600 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1604 => simpa only [Op.effect] using word_p72 s base he ha hf
  case p1608 => simpa only [Op.effect] using word_p76 s base he ha hf
  case p1612 => simpa only [Op.effect] using word_p80 s base he ha hf
  case p1616 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1620 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1624 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1628 => simpa only [Op.effect] using word_p96 s base he ha hf
  case p1632 => simpa only [Op.effect] using word_p1264 s base he ha hf
  case p1636 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1640 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1644 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1648 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1652 => simpa only [Op.effect] using word_p1380 s base he ha hf
  case p1656 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1660 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1664 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1668 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1672 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1676 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1680 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1684 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1688 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1692 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1696 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1700 => simpa only [Op.effect] using word_p1428 s base he ha hf
  case p1704 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1708 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1712 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1716 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1720 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1724 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1728 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1732 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1736 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1740 => simpa only [Op.effect] using word_p1332 s base he ha hf
  case p1744 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1748 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1752 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1756 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1760 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1764 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1768 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1772 => simpa only [Op.effect] using word_p12 s base he ha hf
  case p1776 => simpa only [Op.effect] using word_p16 s base he ha hf
  case p1780 => simpa only [Op.effect] using word_p20 s base he ha hf
  case p1784 => simpa only [Op.effect] using word_p24 s base he ha hf
  case p1788 => simpa only [Op.effect] using word_p1284 s base he ha hf
  case p1792 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1796 => simpa only [Op.effect] using word_p32 s base he ha hf
  case p1800 => simpa only [Op.effect] using word_p28 s base he ha hf
  case p1804 => simpa only [Op.effect] using word_p40 s base he ha hf
  case p1808 => simpa only [Op.effect] using word_p44 s base he ha hf
  case p1812 => simpa only [Op.effect] using word_p48 s base he ha hf
  case p1816 => simpa only [Op.effect] using word_p52 s base he ha hf
  case p1820 => simpa only [Op.effect] using word_p1452 s base he ha hf
  case p1824 => simpa only [Op.effect] using word_p1456 s base he ha hf
  case p1828 => simpa only [Op.effect] using word_p96 s base he ha hf

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  have hs := BoolCodec.stack_aligned s ha
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, ha]
  all_goals
    simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at hs ⊢
    bv_omega

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, Op.program] using hc)
      (by simpa only [Op.error] using he) (op.aligned base s ha) hf.2

@[simp] theorem block_program (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

@[simp] theorem block_error (base : BitVec 64) (ops : List Op) (s : ArmState) :
    read_err (block base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

theorem block_aligned (base : BitVec 64) (ops : List Op) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (block base ops s) := by
  induction ops generalizing s with
  | nil => exact ha
  | cons op ops ih => exact ih _ (op.aligned base s ha)

end SszArm.NatMulWord

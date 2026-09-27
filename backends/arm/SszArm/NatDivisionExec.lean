import SszArm.NatDivisionIntegerExec
import SszArm.NatDivisionMemoryExec
import SszArm.NatDivisionBranchExec

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Dispatch to bounded, single-instruction ISA proofs. No arithmetic,
ownership, loop invariant, or callee-result assumptions enter this layer. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hf : s.program.find? (read_pc s) = some op.row.2 := by
    rw [hp]
    exact hc op.row op.row_mem
  cases op
  case p0 =>
    simpa only [Op.effect] using word_p0 s base he ha hf
  case p4 =>
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p8 =>
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p12 =>
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p16 =>
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p20 =>
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p24 =>
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p28 =>
    simpa only [Op.effect] using word_p28 s base he ha hf
  case p32 =>
    simpa only [Op.effect] using word_p32 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p36 =>
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p40 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p44 =>
    simpa only [Op.effect] using word_p44 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p48 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p52 =>
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p56 =>
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p60 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p64 =>
    simpa only [Op.effect] using word_p64 s base he ha hf
  case p68 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p72 =>
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p76 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p80 =>
    simpa only [Op.effect] using word_p80 s base he ha hf
  case p84 =>
    simpa only [Op.effect] using word_p84 s base he ha hf
  case p88 =>
    simpa only [Op.effect] using word_p88 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p92 =>
    simpa only [Op.effect] using word_p92 s base he ha hf
  case p96 =>
    simpa only [Op.effect] using word_p96 s base he ha hf
  case p100 =>
    simpa only [Op.effect] using word_p100 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p104 =>
    simpa only [Op.effect] using word_p104 s base he ha hf
  case p108 =>
    simpa only [Op.effect] using word_p108 s base he ha hf
  case p112 =>
    simpa only [Op.effect] using word_p112 s base he ha hf
  case p116 =>
    simpa only [Op.effect] using word_p116 s base he ha hf
  case p120 =>
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p124 =>
    simpa only [Op.effect] using word_p124 s base he ha hf
  case p128 =>
    simpa only [Op.effect] using word_p128 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p132 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p136 =>
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p140 =>
    simpa only [Op.effect] using word_p140 s base he ha hf
  case p144 =>
    simpa only [Op.effect] using word_p144 s base he ha hf
  case p148 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p152 =>
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p156 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p160 =>
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p164 =>
    simpa only [Op.effect] using word_p164 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p168 =>
    simpa only [Op.effect] using word_p168 s base he ha hf
  case p172 =>
    simpa only [Op.effect] using word_p172 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p176 =>
    simpa only [Op.effect] using word_p176 s base he ha hf
  case p180 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p184 =>
    simpa only [Op.effect] using word_p184 s base he ha hf
  case p188 =>
    simpa only [Op.effect] using word_p188 s base he ha hf
  case p192 =>
    simpa only [Op.effect] using word_p192 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p196 =>
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p200 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p204 =>
    simpa only [Op.effect] using word_p204 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p208 =>
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p212 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p216 =>
    simpa only [Op.effect] using word_p216 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p220 =>
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p224 =>
    simpa only [Op.effect] using word_p224 s base he ha hf
  case p228 =>
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p232 =>
    simpa only [Op.effect] using word_p232 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p236 =>
    simpa only [Op.effect] using word_p236 s base he ha hf
  case p240 =>
    simpa only [Op.effect] using word_p240 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p244 =>
    simpa only [Op.effect] using word_p244 s base he ha hf
  case p248 =>
    simpa only [Op.effect] using word_p248 s base he ha hf
  case p252 =>
    simpa only [Op.effect] using word_p252 s base he ha hf
  case p256 =>
    simpa only [Op.effect] using word_p256 s base he ha hf
  case p260 =>
    simpa only [Op.effect] using word_p260 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p264 =>
    simpa only [Op.effect] using word_p264 s base he ha hf
  case p268 =>
    simpa only [Op.effect] using word_p268 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p272 =>
    simpa only [Op.effect] using word_p272 s base he ha hf
  case p276 =>
    simpa only [Op.effect] using word_p276 s base he ha hf
  case p280 =>
    simpa only [Op.effect] using word_p280 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p284 =>
    simpa only [Op.effect] using word_p284 s base he ha hf
  case p288 =>
    simpa only [Op.effect] using word_p288 s base he ha hf
  case p292 =>
    simpa only [Op.effect] using word_p292 s base he ha hf
  case p296 =>
    simpa only [Op.effect] using word_p296 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p300 =>
    simpa only [Op.effect] using word_p300 s base he ha hf
  case p304 =>
    simpa only [Op.effect] using word_p304 s base he ha hf
  case p308 =>
    simpa only [Op.effect] using word_p308 s base he ha hf
  case p312 =>
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p316 =>
    simpa only [Op.effect] using word_p316 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p320 =>
    simpa only [Op.effect] using word_p320 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p324 =>
    simpa only [Op.effect] using word_p324 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p328 =>
    simpa only [Op.effect] using word_p328 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p332 =>
    simpa only [Op.effect] using word_p332 s base he ha hf
  case p336 =>
    simpa only [Op.effect] using word_p336 s base he ha hf
  case p340 =>
    simpa only [Op.effect] using word_p340 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p344 =>
    simpa only [Op.effect] using word_p344 s base he ha hf
  case p348 =>
    simpa only [Op.effect] using word_p304 s base he ha hf
  case p352 =>
    simpa only [Op.effect] using word_p308 s base he ha hf
  case p356 =>
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p360 =>
    simpa only [Op.effect] using word_p360 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p364 =>
    simpa only [Op.effect] using word_p364 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p368 =>
    simpa only [Op.effect] using word_p368 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p372 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p376 =>
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p380 =>
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p384 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p388 =>
    simpa only [Op.effect] using word_p64 s base he ha hf
  case p392 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p396 =>
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p400 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p404 =>
    simpa only [Op.effect] using word_p404 s base he ha hf
  case p408 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p412 =>
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p416 =>
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p420 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p424 =>
    simpa only [Op.effect] using word_p424 s base he ha hf
  case p428 =>
    simpa only [Op.effect] using word_p428 s base he ha hf
  case p432 =>
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p436 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p440 =>
    simpa only [Op.effect] using word_p440 s base he ha hf
  case p444 =>
    simpa only [Op.effect] using word_p444 s base he ha hf
  case p448 =>
    simpa only [Op.effect] using word_p448 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p452 =>
    simpa only [Op.effect] using word_p452 s base he ha hf
  case p456 =>
    simpa only [Op.effect] using word_p456 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p460 =>
    simpa only [Op.effect] using word_p404 s base he ha hf
  case p464 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p468 =>
    simpa only [Op.effect] using word_p184 s base he ha hf
  case p472 =>
    simpa only [Op.effect] using word_p472 s base he ha hf
  case p476 =>
    simpa only [Op.effect] using word_p476 s base he ha hf
  case p480 =>
    simpa only [Op.effect] using word_p480 s base he ha hf
  case p484 =>
    simpa only [Op.effect] using word_p484 s base he ha hf
  case p488 =>
    simpa only [Op.effect] using word_p488 s base he ha hf
  case p492 =>
    simpa only [Op.effect] using word_p492 s base he ha hf
  case p496 =>
    simpa only [Op.effect] using word_p496 s base he ha hf
  case p500 =>
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p504 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p508 =>
    simpa only [Op.effect] using word_p440 s base he ha hf
  case p512 =>
    simpa only [Op.effect] using word_p444 s base he ha hf
  case p516 =>
    simpa only [Op.effect] using word_p516 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p520 =>
    simpa only [Op.effect] using word_p520 s base he ha hf
  case p524 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p528 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p532 =>
    simpa only [Op.effect] using word_p532 s base he ha hf
  case p536 =>
    simpa only [Op.effect] using word_p536 s base he ha hf
  case p540 =>
    simpa only [Op.effect] using word_p540 s base he ha hf
  case p544 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p548 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p552 =>
    simpa only [Op.effect] using word_p308 s base he ha hf
  case p556 =>
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p560 =>
    simpa only [Op.effect] using word_p560 s base he ha hf
  case p564 =>
    simpa only [Op.effect] using word_p564 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p568 =>
    simpa only [Op.effect] using word_p568 s base he ha hf
  case p572 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p576 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p580 =>
    simpa only [Op.effect] using word_p532 s base he ha hf
  case p584 =>
    simpa only [Op.effect] using word_p536 s base he ha hf
  case p588 =>
    simpa only [Op.effect] using word_p588 s base he ha hf
  case p592 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p596 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p600 =>
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p604 =>
    simpa only [Op.effect] using word_p604 s base he ha hf
  case p608 =>
    simpa only [Op.effect] using word_p608 s base he ha hf
  case p612 =>
    simpa only [Op.effect] using word_p612 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p616 =>
    simpa only [Op.effect] using word_p616 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p620 =>
    simpa only [Op.effect] using word_p520 s base he ha hf
  case p624 =>
    simpa only [Op.effect] using word_p304 s base he ha hf
  case p628 =>
    simpa only [Op.effect] using word_p308 s base he ha hf
  case p632 =>
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p636 =>
    simpa only [Op.effect] using word_p636 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p640 =>
    simpa only [Op.effect] using word_p640 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p644 =>
    simpa only [Op.effect] using word_p284 s base he ha hf
  case p648 =>
    simpa only [Op.effect] using word_p648 s base he ha hf
  case p652 =>
    simpa only [Op.effect] using word_p652 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p656 =>
    simpa only [Op.effect] using word_p520 s base he ha hf
  case p660 =>
    simpa only [Op.effect] using word_p660 s base he ha hf
  case p664 =>
    simpa only [Op.effect] using word_p304 s base he ha hf
  case p668 =>
    simpa only [Op.effect] using word_p308 s base he ha hf
  case p672 =>
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p676 =>
    simpa only [Op.effect] using word_p676 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p680 =>
    simpa only [Op.effect] using word_p680 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p684 =>
    simpa only [Op.effect] using word_p684 s base he ha hf
  case p688 =>
    simpa only [Op.effect] using word_p688 s base he ha hf
  case p692 =>
    simpa only [Op.effect] using word_p692 s base he ha hf
  case p696 =>
    simpa only [Op.effect] using word_p696 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p700 =>
    simpa only [Op.effect] using word_p700 s base he ha hf
  case p704 =>
    simpa only [Op.effect] using word_p704 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p708 =>
    simpa only [Op.effect] using word_p708 s base he ha hf
  case p712 =>
    simpa only [Op.effect] using word_p712 s base he ha hf
  case p716 =>
    simpa only [Op.effect] using word_p716 s base he ha hf
  case p720 =>
    simpa only [Op.effect] using word_p720 s base he ha hf
  case p724 =>
    simpa only [Op.effect] using word_p724 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p728 =>
    simpa only [Op.effect] using word_p728 s base he ha hf
  case p732 =>
    simpa only [Op.effect] using word_p732 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p736 =>
    simpa only [Op.effect] using word_p736 s base he ha hf
  case p740 =>
    simpa only [Op.effect] using word_p740 s base he ha hf
  case p744 =>
    simpa only [Op.effect] using word_p744 s base he ha hf
  case p748 =>
    simpa only [Op.effect] using word_p748 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p752 =>
    simpa only [Op.effect] using word_p752 s base he ha hf
  case p756 =>
    simpa only [Op.effect] using word_p756 s base he ha hf
  case p760 =>
    simpa only [Op.effect] using word_p760 s base he ha hf
  case p764 =>
    simpa only [Op.effect] using word_p764 s base he ha hf
  case p768 =>
    simpa only [Op.effect] using word_p768 s base he ha hf
  case p772 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p776 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p780 =>
    simpa only [Op.effect] using word_p780 s base he ha hf
  case p784 =>
    simpa only [Op.effect] using word_p784 s base he ha hf
  case p788 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p792 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p796 =>
    simpa only [Op.effect] using word_p796 s base he ha hf
  case p800 =>
    simpa only [Op.effect] using word_p800 s base he ha hf
  case p804 =>
    simpa only [Op.effect] using word_p804 s base he ha hf
  case p808 =>
    simpa only [Op.effect] using word_p808 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p812 =>
    simpa only [Op.effect] using word_p520 s base he ha hf
  case p816 =>
    simpa only [Op.effect] using word_p816 s base he ha hf
  case p820 =>
    simpa only [Op.effect] using word_p820 s base he ha hf
  case p824 =>
    simpa only [Op.effect] using word_p824 s base he ha hf
  case p828 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p832 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p836 =>
    simpa only [Op.effect] using word_p836 s base he ha hf
  case p840 =>
    simpa only [Op.effect] using word_p840 s base he ha hf
  case p844 =>
    simpa only [Op.effect] using word_p844 s base he ha hf
  case p848 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p852 =>
    simpa only [Op.effect] using word_p852 s base he ha hf
  case p856 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p860 =>
    simpa only [Op.effect] using word_p860 s base he ha hf
  case p864 =>
    simpa only [Op.effect] using word_p864 s base he ha hf
  case p868 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p872 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p876 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p880 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p884 =>
    simpa only [Op.effect] using word_p836 s base he ha hf
  case p888 =>
    simpa only [Op.effect] using word_p840 s base he ha hf
  case p892 =>
    simpa only [Op.effect] using word_p892 s base he ha hf
  case p896 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p900 =>
    simpa only [Op.effect] using word_p852 s base he ha hf
  case p904 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p908 =>
    simpa only [Op.effect] using word_p860 s base he ha hf
  case p912 =>
    simpa only [Op.effect] using word_p864 s base he ha hf
  case p916 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p920 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p924 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p928 =>
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p932 =>
    simpa only [Op.effect] using word_p836 s base he ha hf
  case p936 =>
    simpa only [Op.effect] using word_p840 s base he ha hf
  case p940 =>
    simpa only [Op.effect] using word_p940 s base he ha hf
  case p944 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p948 =>
    simpa only [Op.effect] using word_p852 s base he ha hf
  case p952 =>
    simpa only [Op.effect] using word_p848 s base he ha hf
  case p956 =>
    simpa only [Op.effect] using word_p860 s base he ha hf
  case p960 =>
    simpa only [Op.effect] using word_p864 s base he ha hf
  case p964 =>
    simpa only [Op.effect] using word_p544 s base he ha hf
  case p968 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p972 =>
    simpa only [Op.effect] using word_p972 s base he ha hf
  case p976 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p980 =>
    simpa only [Op.effect] using word_p184 s base he ha hf
  case p984 =>
    simpa only [Op.effect] using word_p476 s base he ha hf
  case p988 =>
    simpa only [Op.effect] using word_p988 s base he ha hf
  case p992 =>
    simpa only [Op.effect] using word_p992 s base he ha hf
  case p996 =>
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p1000 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p1004 =>
    simpa only [Op.effect] using word_p1004 s base he ha hf
  case p1008 =>
    simpa only [Op.effect] using word_p1008 s base he ha hf
  case p1012 =>
    simpa only [Op.effect] using word_p1012 s base he ha hf
  case p1016 =>
    simpa only [Op.effect] using word_p1016 s base he ha hf
  case p1020 =>
    simpa only [Op.effect] using word_p1020 s base he ha hf
  case p1024 =>
    simpa only [Op.effect] using word_p1024 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p1028 =>
    simpa only [Op.effect] using word_p520 s base he ha hf
  case p1032 =>
    simpa only [Op.effect] using word_p1032 s base he ha hf
  case p1036 =>
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p1040 =>
    simpa only [Op.effect] using word_p1040 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p1044 =>
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p1048 =>
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p1052 =>
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p1056 =>
    simpa only [Op.effect] using word_p60 s base he ha hf
  case p1060 =>
    simpa only [Op.effect] using word_p424 s base he ha hf
  case p1064 =>
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p1068 =>
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p1072 =>
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p1076 =>
    simpa only [Op.effect] using word_p80 s base he ha hf
  case p1080 =>
    simpa only [Op.effect] using word_p84 s base he ha hf
  case p1084 =>
    simpa only [Op.effect] using word_p1084 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p1088 =>
    simpa only [Op.effect] using word_p1088 s base he ha hf
  case p1092 =>
    simpa only [Op.effect] using word_p1092 s base he ha hf
  case p1096 =>
    simpa only [Op.effect] using word_p1096 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p1100 =>
    simpa only [Op.effect] using word_p1100 s base he ha hf
  case p1104 =>
    simpa only [Op.effect] using word_p1104 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p1108 =>
    simpa only [Op.effect] using word_p1108 s base he ha hf
  case p1112 =>
    simpa only [Op.effect] using word_p1112 s base he ha hf
  case p1116 =>
    simpa only [Op.effect] using word_p768 s base he ha hf
  case p1120 =>
    simpa only [Op.effect] using word_p1120 s base he ha hf
  case p1124 =>
    simpa only [Op.effect] using word_p1124 s base he ha hf
      (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)

/-- Replay a concrete opcode path. A BL path ends at the callee entry unless
the caller separately composes the callee's actual run. -/
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

/-- The routine has no writes to the five high nonvolatile GPRs. -/
theorem Op.high_gpr_frame (op : Op) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5)
    (hr : reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨ reg = 28#5 ∨ reg = 29#5) :
    r (.GPR reg) (op.effect base s) = r (.GPR reg) s := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    cases op <;> simp [Op.effect, put, next, state_simp_rules]

macro "natdivision_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [block, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, BitVec.add_assoc])

end SszArm.NatDivision

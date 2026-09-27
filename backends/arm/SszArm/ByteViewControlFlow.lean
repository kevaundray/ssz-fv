import SszArm.ByteViewImpl
import SszArm.UintWidth

namespace SszArm.ByteView.ControlFlow

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The byte-only closure has a direct branch at every control transfer other
than the original RET. A node carries at most two successors. -/
inductive Node where
  | p688 | p692 | p696 | p700 | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736 | p740 | p744 | p748 | p752 | p756 | p760 | p764 | p768 | p772 | p776 | p780 | p784 | p788 | p792 | p796 | p1972 | p1976 | p1980 | p1984 | p1988 | p1992 | p1996 | p2000 | p2004 | p2008 | p2012 | p2016 | p2020 | p2024 | p2028 | p2032 | p2036 | p2040 | p2044 | p2048 | p2596 | p2600 | p2604 | p2608 | p2612 | p2616 | p2620 | p2624 | p2628 | p2632 | p2636 | p2640 | p2644 | p2648 | p2652 | p2656 | p2660 | p2664 | p2668 | p2672 | p2676 | p2680 | p2684 | p2688 | p2692 | p2696 | p2700 | p3468 | p3472 | p3476 | p3480 | p3484 | p3488 | p3492 | p3496 | p3500 | p3504 | p3508 | p3512 | p3516 | p3520 | p3524 | p3528 | p3532 | p3536 | p3540 | p3544 | p3548 | p3552 | p3556 | p3560 | p3564 | p3568 | p3572 | p3576 | p3580 | p3584 | p3588 | p3592 | p3596 | p3600 | p3604 | p3608 | p3612 | p3616 | p3620 | p3624 | p3628 | p3632 | p3636 | p3640 | p3644 | p3648 | p3652 | p3656 | p3660 | p3664 | p3668 | p3672 | p3676 | p3680 | p3684 | p3688 | p3692 | p3696 | p3700 | p3704 | p3708 | p3712 | p3716 | p3720 | p3748 | p3752 | p3756 | p3760 | p3764 | p3768 | p4076 | p4080 | p4472 | p4476 | p4480 | p4484 | p4488 | p4492 | p4496 | p4500 | p4504 | p4508 | p4512 | p4516 | p4520 | p4524 | p4528 | p4532 | p4536 | p4540 | p4544 | p4548 | p4552 | p4556 | p4560 | p4564 | p4568 | p4572 | p4576 | p4580 | p4584 | p4588 | p4592 | p4596 | p4600 | p4604 | p4608 | p4612 | p4616 | p4620 | p4624 | p4628 | p4632 | p4636 | p4640 | p4644 | p4648 | p4652 | p4656 | p4660 | p4664 | p4668 | p4672 | p4676 | p4680 | p4684 | p4688 | p4692 | p4696 | p4700 | p4704 | p4708 | p4712 | p4716 | p4720 | p4724 | p4728 | p4732 | p4736 | p4740 | p4744 | p4748 | p4752 | p4756 | p4760
  deriving DecidableEq

def Node.pc : Node → Nat
  | .p688 => 688
  | .p692 => 692
  | .p696 => 696
  | .p700 => 700
  | .p704 => 704
  | .p708 => 708
  | .p712 => 712
  | .p716 => 716
  | .p720 => 720
  | .p724 => 724
  | .p728 => 728
  | .p732 => 732
  | .p736 => 736
  | .p740 => 740
  | .p744 => 744
  | .p748 => 748
  | .p752 => 752
  | .p756 => 756
  | .p760 => 760
  | .p764 => 764
  | .p768 => 768
  | .p772 => 772
  | .p776 => 776
  | .p780 => 780
  | .p784 => 784
  | .p788 => 788
  | .p792 => 792
  | .p796 => 796
  | .p1972 => 1972
  | .p1976 => 1976
  | .p1980 => 1980
  | .p1984 => 1984
  | .p1988 => 1988
  | .p1992 => 1992
  | .p1996 => 1996
  | .p2000 => 2000
  | .p2004 => 2004
  | .p2008 => 2008
  | .p2012 => 2012
  | .p2016 => 2016
  | .p2020 => 2020
  | .p2024 => 2024
  | .p2028 => 2028
  | .p2032 => 2032
  | .p2036 => 2036
  | .p2040 => 2040
  | .p2044 => 2044
  | .p2048 => 2048
  | .p2596 => 2596
  | .p2600 => 2600
  | .p2604 => 2604
  | .p2608 => 2608
  | .p2612 => 2612
  | .p2616 => 2616
  | .p2620 => 2620
  | .p2624 => 2624
  | .p2628 => 2628
  | .p2632 => 2632
  | .p2636 => 2636
  | .p2640 => 2640
  | .p2644 => 2644
  | .p2648 => 2648
  | .p2652 => 2652
  | .p2656 => 2656
  | .p2660 => 2660
  | .p2664 => 2664
  | .p2668 => 2668
  | .p2672 => 2672
  | .p2676 => 2676
  | .p2680 => 2680
  | .p2684 => 2684
  | .p2688 => 2688
  | .p2692 => 2692
  | .p2696 => 2696
  | .p2700 => 2700
  | .p3468 => 3468
  | .p3472 => 3472
  | .p3476 => 3476
  | .p3480 => 3480
  | .p3484 => 3484
  | .p3488 => 3488
  | .p3492 => 3492
  | .p3496 => 3496
  | .p3500 => 3500
  | .p3504 => 3504
  | .p3508 => 3508
  | .p3512 => 3512
  | .p3516 => 3516
  | .p3520 => 3520
  | .p3524 => 3524
  | .p3528 => 3528
  | .p3532 => 3532
  | .p3536 => 3536
  | .p3540 => 3540
  | .p3544 => 3544
  | .p3548 => 3548
  | .p3552 => 3552
  | .p3556 => 3556
  | .p3560 => 3560
  | .p3564 => 3564
  | .p3568 => 3568
  | .p3572 => 3572
  | .p3576 => 3576
  | .p3580 => 3580
  | .p3584 => 3584
  | .p3588 => 3588
  | .p3592 => 3592
  | .p3596 => 3596
  | .p3600 => 3600
  | .p3604 => 3604
  | .p3608 => 3608
  | .p3612 => 3612
  | .p3616 => 3616
  | .p3620 => 3620
  | .p3624 => 3624
  | .p3628 => 3628
  | .p3632 => 3632
  | .p3636 => 3636
  | .p3640 => 3640
  | .p3644 => 3644
  | .p3648 => 3648
  | .p3652 => 3652
  | .p3656 => 3656
  | .p3660 => 3660
  | .p3664 => 3664
  | .p3668 => 3668
  | .p3672 => 3672
  | .p3676 => 3676
  | .p3680 => 3680
  | .p3684 => 3684
  | .p3688 => 3688
  | .p3692 => 3692
  | .p3696 => 3696
  | .p3700 => 3700
  | .p3704 => 3704
  | .p3708 => 3708
  | .p3712 => 3712
  | .p3716 => 3716
  | .p3720 => 3720
  | .p3748 => 3748
  | .p3752 => 3752
  | .p3756 => 3756
  | .p3760 => 3760
  | .p3764 => 3764
  | .p3768 => 3768
  | .p4076 => 4076
  | .p4080 => 4080
  | .p4472 => 4472
  | .p4476 => 4476
  | .p4480 => 4480
  | .p4484 => 4484
  | .p4488 => 4488
  | .p4492 => 4492
  | .p4496 => 4496
  | .p4500 => 4500
  | .p4504 => 4504
  | .p4508 => 4508
  | .p4512 => 4512
  | .p4516 => 4516
  | .p4520 => 4520
  | .p4524 => 4524
  | .p4528 => 4528
  | .p4532 => 4532
  | .p4536 => 4536
  | .p4540 => 4540
  | .p4544 => 4544
  | .p4548 => 4548
  | .p4552 => 4552
  | .p4556 => 4556
  | .p4560 => 4560
  | .p4564 => 4564
  | .p4568 => 4568
  | .p4572 => 4572
  | .p4576 => 4576
  | .p4580 => 4580
  | .p4584 => 4584
  | .p4588 => 4588
  | .p4592 => 4592
  | .p4596 => 4596
  | .p4600 => 4600
  | .p4604 => 4604
  | .p4608 => 4608
  | .p4612 => 4612
  | .p4616 => 4616
  | .p4620 => 4620
  | .p4624 => 4624
  | .p4628 => 4628
  | .p4632 => 4632
  | .p4636 => 4636
  | .p4640 => 4640
  | .p4644 => 4644
  | .p4648 => 4648
  | .p4652 => 4652
  | .p4656 => 4656
  | .p4660 => 4660
  | .p4664 => 4664
  | .p4668 => 4668
  | .p4672 => 4672
  | .p4676 => 4676
  | .p4680 => 4680
  | .p4684 => 4684
  | .p4688 => 4688
  | .p4692 => 4692
  | .p4696 => 4696
  | .p4700 => 4700
  | .p4704 => 4704
  | .p4708 => 4708
  | .p4712 => 4712
  | .p4716 => 4716
  | .p4720 => 4720
  | .p4724 => 4724
  | .p4728 => 4728
  | .p4732 => 4732
  | .p4736 => 4736
  | .p4740 => 4740
  | .p4744 => 4744
  | .p4748 => 4748
  | .p4752 => 4752
  | .p4756 => 4756
  | .p4760 => 4760

def Node.word : Node → BitVec 32
  | .p688 => 0xa940a428#32
  | .p692 => 0xf100007f#32
  | .p696 => 0x54000061#32
  | .p700 => 0x5280000a#32
  | .p704 => 0x14000002#32
  | .p708 => 0x5280002a#32
  | .p712 => 0xb4003ae8#32
  | .p716 => 0xd100052b#32
  | .p720 => 0xb100057f#32
  | .p724 => 0x54005620#32
  | .p728 => 0xd10043ff#32
  | .p732 => 0xf90003e9#32
  | .p736 => 0xaa0b03e9#32
  | .p740 => 0xd37df129#32
  | .p744 => 0x8b090109#32
  | .p748 => 0xf940012c#32
  | .p752 => 0xf94003e9#32
  | .p756 => 0x910043ff#32
  | .p760 => 0xd100056b#32
  | .p764 => 0xb4fffeac#32
  | .p768 => 0x9100096b#32
  | .p772 => 0xeb0a017f#32
  | .p776 => 0x54000063#32
  | .p780 => 0x5280000a#32
  | .p784 => 0x14000002#32
  | .p788 => 0x5280002a#32
  | .p792 => 0x540054c0#32
  | .p796 => 0x140002ad#32
  | .p1972 => 0xa940a428#32
  | .p1976 => 0xb4002ea8#32
  | .p1980 => 0xd100052b#32
  | .p1984 => 0xb100057f#32
  | .p1988 => 0x54003700#32
  | .p1992 => 0xd10043ff#32
  | .p1996 => 0xf90003e9#32
  | .p2000 => 0xaa0b03e9#32
  | .p2004 => 0xd37df129#32
  | .p2008 => 0x8b090109#32
  | .p2012 => 0xf940012c#32
  | .p2016 => 0xf94003e9#32
  | .p2020 => 0x910043ff#32
  | .p2024 => 0xaa0b03ea#32
  | .p2028 => 0xd100056b#32
  | .p2032 => 0xb4fffe8c#32
  | .p2036 => 0x9100054a#32
  | .p2040 => 0xf1000d5f#32
  | .p2044 => 0x54004e22#32
  | .p2048 => 0x140001aa#32
  | .p2596 => 0xf100007f#32
  | .p2600 => 0x54000061#32
  | .p2604 => 0x5280000a#32
  | .p2608 => 0x14000002#32
  | .p2612 => 0x5280002a#32
  | .p2616 => 0xf100013f#32
  | .p2620 => 0x54000061#32
  | .p2624 => 0x5280000b#32
  | .p2628 => 0x14000002#32
  | .p2632 => 0x5280002b#32
  | .p2636 => 0x4a0b014b#32
  | .p2640 => 0x1a8a13ea#32
  | .p2644 => 0xd10043ff#32
  | .p2648 => 0xf90003e9#32
  | .p2652 => 0x12000169#32
  | .p2656 => 0x35000089#32
  | .p2660 => 0xf94003e9#32
  | .p2664 => 0x910043ff#32
  | .p2668 => 0x14000004#32
  | .p2672 => 0xf94003e9#32
  | .p2676 => 0x910043ff#32
  | .p2680 => 0x140000d6#32
  | .p2684 => 0xb4003883#32
  | .p2688 => 0xeb09007f#32
  | .p2692 => 0xaa0903ea#32
  | .p2696 => 0x540019e1#32
  | .p2700 => 0x140001c0#32
  | .p3468 => 0xaa1f03eb#32
  | .p3472 => 0xaa0903ea#32
  | .p3476 => 0x140000fb#32
  | .p3480 => 0xeb0a03ff#32
  | .p3484 => 0x54000063#32
  | .p3488 => 0x5280000a#32
  | .p3492 => 0x14000002#32
  | .p3496 => 0x5280002a#32
  | .p3500 => 0x54000121#32
  | .p3504 => 0xb4001ee3#32
  | .p3508 => 0xb4000229#32
  | .p3512 => 0xf940010a#32
  | .p3516 => 0xeb0a007f#32
  | .p3520 => 0x54001e60#32
  | .p3524 => 0xeb0a007f#32
  | .p3528 => 0x54001e29#32
  | .p3532 => 0x1400000b#32
  | .p3536 => 0xd10043ff#32
  | .p3540 => 0xf90003e9#32
  | .p3544 => 0x12000149#32
  | .p3548 => 0x34000089#32
  | .p3552 => 0xf94003e9#32
  | .p3556 => 0x910043ff#32
  | .p3560 => 0x14000004#32
  | .p3564 => 0xf94003e9#32
  | .p3568 => 0x910043ff#32
  | .p3572 => 0x140000e6#32
  | .p3576 => 0xd10043ff#32
  | .p3580 => 0xf90003e9#32
  | .p3584 => 0xf90007ea#32
  | .p3588 => 0x91000009#32
  | .p3592 => 0x9100e129#32
  | .p3596 => 0xd280000a#32
  | .p3600 => 0xf900012a#32
  | .p3604 => 0xd280000a#32
  | .p3608 => 0xf900052a#32
  | .p3612 => 0xf94007ea#32
  | .p3616 => 0xf94003e9#32
  | .p3620 => 0x910043ff#32
  | .p3624 => 0xd10043ff#32
  | .p3628 => 0xf90003e9#32
  | .p3632 => 0xf90007ea#32
  | .p3636 => 0x91000009#32
  | .p3640 => 0x91004129#32
  | .p3644 => 0xd280000a#32
  | .p3648 => 0xf900012a#32
  | .p3652 => 0xf9000528#32
  | .p3656 => 0xf94007ea#32
  | .p3660 => 0xf94003e9#32
  | .p3664 => 0x910043ff#32
  | .p3668 => 0x52800048#32
  | .p3672 => 0xd10043ff#32
  | .p3676 => 0xf90003ea#32
  | .p3680 => 0xf90007eb#32
  | .p3684 => 0x9100000a#32
  | .p3688 => 0x9100814a#32
  | .p3692 => 0xf9000149#32
  | .p3696 => 0xd280000b#32
  | .p3700 => 0xf900054b#32
  | .p3704 => 0xf94007eb#32
  | .p3708 => 0xf94003ea#32
  | .p3712 => 0x910043ff#32
  | .p3716 => 0xf9001803#32
  | .p3720 => 0x140000fa#32
  | .p3748 => 0xb40016a9#32
  | .p3752 => 0xf940010a#32
  | .p3756 => 0xf100093f#32
  | .p3760 => 0x540009e3#32
  | .p3764 => 0xf940050b#32
  | .p3768 => 0x140000b2#32
  | .p4076 => 0xaa1f03eb#32
  | .p4080 => 0x14000064#32
  | .p4472 => 0xaa1f03eb#32
  | .p4476 => 0xaa1f03ea#32
  | .p4480 => 0xca03014a#32
  | .p4484 => 0xaa0b014a#32
  | .p4488 => 0xb50001ca#32
  | .p4492 => 0x52800048#32
  | .p4496 => 0xa9018c02#32
  | .p4500 => 0x39004008#32
  | .p4504 => 0xd10043ff#32
  | .p4508 => 0xf90003e9#32
  | .p4512 => 0xf90007ea#32
  | .p4516 => 0x91000009#32
  | .p4520 => 0xd280000a#32
  | .p4524 => 0xf900012a#32
  | .p4528 => 0xf94007ea#32
  | .p4532 => 0xf94003e9#32
  | .p4536 => 0x910043ff#32
  | .p4540 => 0x14000030#32
  | .p4544 => 0xd10043ff#32
  | .p4548 => 0xf90003e9#32
  | .p4552 => 0xf90007ea#32
  | .p4556 => 0x91000009#32
  | .p4560 => 0x91010129#32
  | .p4564 => 0xd280000a#32
  | .p4568 => 0xf900012a#32
  | .p4572 => 0xf94007ea#32
  | .p4576 => 0xf94003e9#32
  | .p4580 => 0x910043ff#32
  | .p4584 => 0xd10043ff#32
  | .p4588 => 0xf90003e9#32
  | .p4592 => 0xf90007ea#32
  | .p4596 => 0x91000009#32
  | .p4600 => 0x91004129#32
  | .p4604 => 0xd280000a#32
  | .p4608 => 0xf900012a#32
  | .p4612 => 0xf9000528#32
  | .p4616 => 0xf94007ea#32
  | .p4620 => 0xf94003e9#32
  | .p4624 => 0x910043ff#32
  | .p4628 => 0xf9001009#32
  | .p4632 => 0x52800068#32
  | .p4636 => 0xd10043ff#32
  | .p4640 => 0xf90003e9#32
  | .p4644 => 0xf90007ea#32
  | .p4648 => 0x91000009#32
  | .p4652 => 0x9100a129#32
  | .p4656 => 0xd280000a#32
  | .p4660 => 0xf900012a#32
  | .p4664 => 0xf9000523#32
  | .p4668 => 0xf94007ea#32
  | .p4672 => 0xf94003e9#32
  | .p4676 => 0x910043ff#32
  | .p4680 => 0xd10043ff#32
  | .p4684 => 0xf90003e9#32
  | .p4688 => 0xf90007ea#32
  | .p4692 => 0x91000009#32
  | .p4696 => 0x9100e129#32
  | .p4700 => 0xd280000a#32
  | .p4704 => 0xf900012a#32
  | .p4708 => 0xf94007ea#32
  | .p4712 => 0xf94003e9#32
  | .p4716 => 0x910043ff#32
  | .p4720 => 0x52800029#32
  | .p4724 => 0xb9004808#32
  | .p4728 => 0xa9002409#32
  | .p4732 => 0xa9564ff4#32
  | .p4736 => 0xa95557f6#32
  | .p4740 => 0xa9545ff8#32
  | .p4744 => 0xa95367fa#32
  | .p4748 => 0xa9526ffc#32
  | .p4752 => 0xa9517bfd#32
  | .p4756 => 0x9105c3ff#32
  | .p4760 => 0xd65f03c0#32

def Node.targets : Node → List Node
  | .p688 => [.p692]
  | .p692 => [.p696]
  | .p696 => [.p700, .p708]
  | .p700 => [.p704]
  | .p704 => [.p712]
  | .p708 => [.p712]
  | .p712 => [.p716, .p2596]
  | .p716 => [.p720]
  | .p720 => [.p724]
  | .p724 => [.p728, .p3480]
  | .p728 => [.p732]
  | .p732 => [.p736]
  | .p736 => [.p740]
  | .p740 => [.p744]
  | .p744 => [.p748]
  | .p748 => [.p752]
  | .p752 => [.p756]
  | .p756 => [.p760]
  | .p760 => [.p764]
  | .p764 => [.p768, .p720]
  | .p768 => [.p772]
  | .p772 => [.p776]
  | .p776 => [.p780, .p788]
  | .p780 => [.p784]
  | .p784 => [.p792]
  | .p788 => [.p792]
  | .p792 => [.p796, .p3504]
  | .p796 => [.p3536]
  | .p1972 => [.p1976]
  | .p1976 => [.p1980, .p3468]
  | .p1980 => [.p1984]
  | .p1984 => [.p1988]
  | .p1988 => [.p1992, .p3748]
  | .p1992 => [.p1996]
  | .p1996 => [.p2000]
  | .p2000 => [.p2004]
  | .p2004 => [.p2008]
  | .p2008 => [.p2012]
  | .p2012 => [.p2016]
  | .p2016 => [.p2020]
  | .p2020 => [.p2024]
  | .p2024 => [.p2028]
  | .p2028 => [.p2032]
  | .p2032 => [.p2036, .p1984]
  | .p2036 => [.p2040]
  | .p2040 => [.p2044]
  | .p2044 => [.p2048, .p4544]
  | .p2048 => [.p3752]
  | .p2596 => [.p2600]
  | .p2600 => [.p2604, .p2612]
  | .p2604 => [.p2608]
  | .p2608 => [.p2616]
  | .p2612 => [.p2616]
  | .p2616 => [.p2620]
  | .p2620 => [.p2624, .p2632]
  | .p2624 => [.p2628]
  | .p2628 => [.p2636]
  | .p2632 => [.p2636]
  | .p2636 => [.p2640]
  | .p2640 => [.p2644]
  | .p2644 => [.p2648]
  | .p2648 => [.p2652]
  | .p2652 => [.p2656]
  | .p2656 => [.p2660, .p2672]
  | .p2660 => [.p2664]
  | .p2664 => [.p2668]
  | .p2668 => [.p2684]
  | .p2672 => [.p2676]
  | .p2676 => [.p2680]
  | .p2680 => [.p3536]
  | .p2684 => [.p2688, .p4492]
  | .p2688 => [.p2692]
  | .p2692 => [.p2696]
  | .p2696 => [.p2700, .p3524]
  | .p2700 => [.p4492]
  | .p3468 => [.p3472]
  | .p3472 => [.p3476]
  | .p3476 => [.p4480]
  | .p3480 => [.p3484]
  | .p3484 => [.p3488, .p3496]
  | .p3488 => [.p3492]
  | .p3492 => [.p3500]
  | .p3496 => [.p3500]
  | .p3500 => [.p3504, .p3536]
  | .p3504 => [.p3508, .p4492]
  | .p3508 => [.p3512, .p3576]
  | .p3512 => [.p3516]
  | .p3516 => [.p3520]
  | .p3520 => [.p3524, .p4492]
  | .p3524 => [.p3528]
  | .p3528 => [.p3532, .p4492]
  | .p3532 => [.p3576]
  | .p3536 => [.p3540]
  | .p3540 => [.p3544]
  | .p3544 => [.p3548]
  | .p3548 => [.p3552, .p3564]
  | .p3552 => [.p3556]
  | .p3556 => [.p3560]
  | .p3560 => [.p3576]
  | .p3564 => [.p3568]
  | .p3568 => [.p3572]
  | .p3572 => [.p4492]
  | .p3576 => [.p3580]
  | .p3580 => [.p3584]
  | .p3584 => [.p3588]
  | .p3588 => [.p3592]
  | .p3592 => [.p3596]
  | .p3596 => [.p3600]
  | .p3600 => [.p3604]
  | .p3604 => [.p3608]
  | .p3608 => [.p3612]
  | .p3612 => [.p3616]
  | .p3616 => [.p3620]
  | .p3620 => [.p3624]
  | .p3624 => [.p3628]
  | .p3628 => [.p3632]
  | .p3632 => [.p3636]
  | .p3636 => [.p3640]
  | .p3640 => [.p3644]
  | .p3644 => [.p3648]
  | .p3648 => [.p3652]
  | .p3652 => [.p3656]
  | .p3656 => [.p3660]
  | .p3660 => [.p3664]
  | .p3664 => [.p3668]
  | .p3668 => [.p3672]
  | .p3672 => [.p3676]
  | .p3676 => [.p3680]
  | .p3680 => [.p3684]
  | .p3684 => [.p3688]
  | .p3688 => [.p3692]
  | .p3692 => [.p3696]
  | .p3696 => [.p3700]
  | .p3700 => [.p3704]
  | .p3704 => [.p3708]
  | .p3708 => [.p3712]
  | .p3712 => [.p3716]
  | .p3716 => [.p3720]
  | .p3720 => [.p4720]
  | .p3748 => [.p3752, .p4472]
  | .p3752 => [.p3756]
  | .p3756 => [.p3760]
  | .p3760 => [.p3764, .p4076]
  | .p3764 => [.p3768]
  | .p3768 => [.p4480]
  | .p4076 => [.p4080]
  | .p4080 => [.p4480]
  | .p4472 => [.p4476]
  | .p4476 => [.p4480]
  | .p4480 => [.p4484]
  | .p4484 => [.p4488]
  | .p4488 => [.p4492, .p4544]
  | .p4492 => [.p4496]
  | .p4496 => [.p4500]
  | .p4500 => [.p4504]
  | .p4504 => [.p4508]
  | .p4508 => [.p4512]
  | .p4512 => [.p4516]
  | .p4516 => [.p4520]
  | .p4520 => [.p4524]
  | .p4524 => [.p4528]
  | .p4528 => [.p4532]
  | .p4532 => [.p4536]
  | .p4536 => [.p4540]
  | .p4540 => [.p4732]
  | .p4544 => [.p4548]
  | .p4548 => [.p4552]
  | .p4552 => [.p4556]
  | .p4556 => [.p4560]
  | .p4560 => [.p4564]
  | .p4564 => [.p4568]
  | .p4568 => [.p4572]
  | .p4572 => [.p4576]
  | .p4576 => [.p4580]
  | .p4580 => [.p4584]
  | .p4584 => [.p4588]
  | .p4588 => [.p4592]
  | .p4592 => [.p4596]
  | .p4596 => [.p4600]
  | .p4600 => [.p4604]
  | .p4604 => [.p4608]
  | .p4608 => [.p4612]
  | .p4612 => [.p4616]
  | .p4616 => [.p4620]
  | .p4620 => [.p4624]
  | .p4624 => [.p4628]
  | .p4628 => [.p4632]
  | .p4632 => [.p4636]
  | .p4636 => [.p4640]
  | .p4640 => [.p4644]
  | .p4644 => [.p4648]
  | .p4648 => [.p4652]
  | .p4652 => [.p4656]
  | .p4656 => [.p4660]
  | .p4660 => [.p4664]
  | .p4664 => [.p4668]
  | .p4668 => [.p4672]
  | .p4672 => [.p4676]
  | .p4676 => [.p4680]
  | .p4680 => [.p4684]
  | .p4684 => [.p4688]
  | .p4688 => [.p4692]
  | .p4692 => [.p4696]
  | .p4696 => [.p4700]
  | .p4700 => [.p4704]
  | .p4704 => [.p4708]
  | .p4708 => [.p4712]
  | .p4712 => [.p4716]
  | .p4716 => [.p4720]
  | .p4720 => [.p4724]
  | .p4724 => [.p4728]
  | .p4728 => [.p4732]
  | .p4732 => [.p4736]
  | .p4736 => [.p4740]
  | .p4740 => [.p4744]
  | .p4744 => [.p4748]
  | .p4748 => [.p4752]
  | .p4752 => [.p4756]
  | .p4756 => [.p4760]
  | .p4760 => []

def Internal (s : ArmState) (base : BitVec 64) : Prop :=
  ∃ node : Node, read_pc s = base + BitVec.ofNat 64 node.pc

private theorem row_mem (node : Node) : (node.pc, node.word) ∈ program := by
  cases node <;> decide

private theorem aligned_add368 (x : BitVec 64) (h : Aligned x 4) : Aligned (x + 368#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

private theorem branch_total (p : Prop) [Decidable p] : ¬p ∨ p := by
  by_cases h : p
  · exact Or.inr h
  · exact Or.inl h

private theorem branch_total_reverse (p : Prop) [Decidable p] : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h

private theorem pc_write_closed (s : ArmState) (pc left right : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : pc = left ∨ pc = right) :
    (w .PC pc s).program = s.program ∧ r .ERR (w .PC pc s) = .None ∧
      CheckSPAlignment (w .PC pc s) ∧
      (r .PC (w .PC pc s) = left ∨ r .PC (w .PC pc s) = right) := by
  simp only [r, w, read_err, CheckSPAlignment, write_base_pc,
    read_base_pc, read_base_error, read_gpr, read_base_gpr] at *
  exact ⟨True.intro, he, ha, hp⟩

/-- A local ISA certificate compares only the one or two successors of its
instruction, never the full control-flow closure. -/
theorem node_step (s : ArmState) (base : BitVec 64) (node : Node)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 node.pc) (hn : node ≠ .p4760) :
    (stepi s).program = s.program ∧ read_err (stepi s) = .None ∧
      CheckSPAlignment (stepi s) ∧
      ∃ next ∈ node.targets, read_pc (stepi s) = base + BitVec.ofNat 64 next.pc := by
  have hf := hc (node.pc, node.word) (row_mem node)
  have herr : r .ERR s = .None := he
  have hsp : Aligned (r (.GPR 31#5) s) 4 := BoolCodec.stack_aligned s ha
  cases node
  case p4760 => exact False.elim (hn rfl)
  all_goals
    simp only [Node.pc, Node.word] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [Node.targets, Node.pc, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, ha, herr, hp, BitVec.add_assoc]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ hsp
    | exact BoolCodec.aligned_add16 _ hsp
    | exact aligned_add368 _ hsp
    | exact branch_total _
    | exact branch_total_reverse _
    | (split <;> apply pc_write_closed s _ _ _ he ha <;>
        first | exact Or.inl rfl | exact Or.inr rfl)

/-- Every actual non-RET instruction stays in the finite byte-only closure. -/
theorem step_closed (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Internal s base) (hr : read_pc s ≠ base + 4760#64) :
    CodeAt (stepi s) base ∧ read_err (stepi s) = .None ∧
      CheckSPAlignment (stepi s) ∧ Internal (stepi s) base := by
  obtain ⟨node, hp⟩ := hi
  have hn : node ≠ .p4760 := by
    intro h
    subst node
    exact hr hp
  obtain ⟨hprog, herr, halign, next, _, hnext⟩ := node_step s base node hc he ha hp hn
  exact ⟨by simpa only [CodeAt, hprog] using hc, herr, halign, next, hnext⟩

/-- Stop immediately before RET; every preceding transition is the real ISA step. -/
def beforeRet (base : BitVec 64) : Nat → ArmState → ArmState
  | 0, s => s
  | n + 1, s => if read_pc s = base + 4760#64 then s else beforeRet base n (stepi s)

theorem beforeRet_internal (base : BitVec 64) (n : Nat) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hi : Internal s base) : Internal (beforeRet base n s) base := by
  induction n generalizing s with
  | zero => exact hi
  | succ n ih =>
    simp only [beforeRet]
    split
    · exact hi
    · obtain ⟨hc', he', ha', hi'⟩ := step_closed s base hc he ha hi ‹_›
      exact ih _ hc' he' ha' hi'

theorem internal_ne_bounds (s : ArmState) (base : BitVec 64) (hi : Internal s base) :
    read_pc s ≠ base + BitVec.ofNat 64 boundsPanic := by
  obtain ⟨node, hp⟩ := hi
  have hb : node.pc ≤ 4760 := by cases node <;> decide
  rw [hp]
  simp only [boundsPanic]
  bv_omega

/-- No mathematical-capacity, memory-content or future-execution hypothesis is
needed to exclude the linked bounds-panic frontier from either byte decoder. -/
theorem boundsPanic_unreachable (s : ArmState) (base : BitVec 64) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1972#64 ∨ read_pc s = base + 688#64) :
    read_pc (beforeRet base n s) ≠ base + BitVec.ofNat 64 boundsPanic := by
  apply internal_ne_bounds
  apply beforeRet_internal base n s hc he ha
  rcases hp with hp | hp
  · exact ⟨.p1972, hp⟩
  · exact ⟨.p688, hp⟩

end SszArm.ByteView.ControlFlow

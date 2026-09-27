import SszArm.NatDivisionImpl
import SszArm.BoolMemory
import SszArm.BoolAlignment

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- One constructor per instruction in the linked native image. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52 | p56 | p60
  | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124
  | p128 | p132 | p136 | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188
  | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236 | p240 | p244 | p248 | p252
  | p256 | p260 | p264 | p268 | p272 | p276 | p280 | p284 | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316
  | p320 | p324 | p328 | p332 | p336 | p340 | p344 | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380
  | p384 | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p416 | p420 | p424 | p428 | p432 | p436 | p440 | p444
  | p448 | p452 | p456 | p460 | p464 | p468 | p472 | p476 | p480 | p484 | p488 | p492 | p496 | p500 | p504 | p508
  | p512 | p516 | p520 | p524 | p528 | p532 | p536 | p540 | p544 | p548 | p552 | p556 | p560 | p564 | p568 | p572
  | p576 | p580 | p584 | p588 | p592 | p596 | p600 | p604 | p608 | p612 | p616 | p620 | p624 | p628 | p632 | p636
  | p640 | p644 | p648 | p652 | p656 | p660 | p664 | p668 | p672 | p676 | p680 | p684 | p688 | p692 | p696 | p700
  | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736 | p740 | p744 | p748 | p752 | p756 | p760 | p764
  | p768 | p772 | p776 | p780 | p784 | p788 | p792 | p796 | p800 | p804 | p808 | p812 | p816 | p820 | p824 | p828
  | p832 | p836 | p840 | p844 | p848 | p852 | p856 | p860 | p864 | p868 | p872 | p876 | p880 | p884 | p888 | p892
  | p896 | p900 | p904 | p908 | p912 | p916 | p920 | p924 | p928 | p932 | p936 | p940 | p944 | p948 | p952 | p956
  | p960 | p964 | p968 | p972 | p976 | p980 | p984 | p988 | p992 | p996 | p1000 | p1004 | p1008 | p1012 | p1016 | p1020
  | p1024 | p1028 | p1032 | p1036 | p1040 | p1044 | p1048 | p1052 | p1056 | p1060 | p1064 | p1068 | p1072 | p1076 | p1080 | p1084
  | p1088 | p1092 | p1096 | p1100 | p1104 | p1108 | p1112 | p1116 | p1120 | p1124
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10103ff#32)
  | .p4 => (4, 0xf90003fe#32)
  | .p8 => (8, 0xa9015ff8#32)
  | .p12 => (12, 0xa90257f6#32)
  | .p16 => (16, 0xa9034ff4#32)
  | .p20 => (20, 0xaa0403f5#32)
  | .p24 => (24, 0xaa0303f4#32)
  | .p28 => (28, 0xaa0003f3#32)
  | .p32 => (32, 0xb4000861#32)
  | .p36 => (36, 0xd1000449#32)
  | .p40 => (40, 0xb100053f#32)
  | .p44 => (44, 0x540008e0#32)
  | .p48 => (48, 0xd10043ff#32)
  | .p52 => (52, 0xf90003eb#32)
  | .p56 => (56, 0xaa0903eb#32)
  | .p60 => (60, 0xd37df16b#32)
  | .p64 => (64, 0x8b0b002b#32)
  | .p68 => (68, 0xf940016a#32)
  | .p72 => (72, 0xf94003eb#32)
  | .p76 => (76, 0x910043ff#32)
  | .p80 => (80, 0xaa0903e8#32)
  | .p84 => (84, 0xd1000529#32)
  | .p88 => (88, 0xb4fffe8a#32)
  | .p92 => (92, 0x91000508#32)
  | .p96 => (96, 0xf1000d1f#32)
  | .p100 => (100, 0x54000743#32)
  | .p104 => (104, 0xd37df057#32)
  | .p108 => (108, 0x91000448#32)
  | .p112 => (112, 0xd1002029#32)
  | .p116 => (116, 0x52800118#32)
  | .p120 => (120, 0xaa0803f6#32)
  | .p124 => (124, 0xf1000508#32)
  | .p128 => (128, 0x54001c20#32)
  | .p132 => (132, 0xd10043ff#32)
  | .p136 => (136, 0xf90003eb#32)
  | .p140 => (140, 0xaa1703eb#32)
  | .p144 => (144, 0x8b0b012b#32)
  | .p148 => (148, 0xf940016a#32)
  | .p152 => (152, 0xf94003eb#32)
  | .p156 => (156, 0x910043ff#32)
  | .p160 => (160, 0xd10022f7#32)
  | .p164 => (164, 0xb4fffeaa#32)
  | .p168 => (168, 0xd37dfd09#32)
  | .p172 => (172, 0xb5001409#32)
  | .p176 => (176, 0xd37df109#32)
  | .p180 => (180, 0xd10043ff#32)
  | .p184 => (184, 0xf90003ea#32)
  | .p188 => (188, 0x9241012a#32)
  | .p192 => (192, 0xb500008a#32)
  | .p196 => (196, 0xf94003ea#32)
  | .p200 => (200, 0x910043ff#32)
  | .p204 => (204, 0x14000004#32)
  | .p208 => (208, 0xf94003ea#32)
  | .p212 => (212, 0x910043ff#32)
  | .p216 => (216, 0x14000095#32)
  | .p220 => (220, 0xf94002aa#32)
  | .p224 => (224, 0xf9400aab#32)
  | .p228 => (228, 0xab0a016c#32)
  | .p232 => (232, 0x54001222#32)
  | .p236 => (236, 0xb100219f#32)
  | .p240 => (240, 0x540011e8#32)
  | .p244 => (244, 0x91001d8d#32)
  | .p248 => (248, 0x927df1ad#32)
  | .p252 => (252, 0xcb0c01ac#32)
  | .p256 => (256, 0xab0b018b#32)
  | .p260 => (260, 0x54001142#32)
  | .p264 => (264, 0xab09016c#32)
  | .p268 => (268, 0x54001102#32)
  | .p272 => (272, 0xf94006a9#32)
  | .p276 => (276, 0xeb09019f#32)
  | .p280 => (280, 0x540010a8#32)
  | .p284 => (284, 0xaa1f03e9#32)
  | .p288 => (288, 0x8b0b0158#32)
  | .p292 => (292, 0xf9000aac#32)
  | .p296 => (296, 0x14000027#32)
  | .p300 => (300, 0xaa0203f6#32)
  | .p304 => (304, 0xaa1603e0#32)
  | .p308 => (308, 0xaa1403e2#32)
  | .p312 => (312, 0xaa1f03e3#32)
  | .p316 => (316, 0x9400b213#32)
  | .p320 => (320, 0xb4000a21#32)
  | .p324 => (324, 0x1400005a#32)
  | .p328 => (328, 0xb4000a42#32)
  | .p332 => (332, 0xf9400036#32)
  | .p336 => (336, 0xf100085f#32)
  | .p340 => (340, 0x540008c3#32)
  | .p344 => (344, 0xf9400421#32)
  | .p348 => (348, 0xaa1603e0#32)
  | .p352 => (352, 0xaa1403e2#32)
  | .p356 => (356, 0xaa1f03e3#32)
  | .p360 => (360, 0x9400b208#32)
  | .p364 => (364, 0xb40008c1#32)
  | .p368 => (368, 0x1400004f#32)
  | .p372 => (372, 0xd10043ff#32)
  | .p376 => (376, 0xf90003eb#32)
  | .p380 => (380, 0xaa0903eb#32)
  | .p384 => (384, 0xd37df16b#32)
  | .p388 => (388, 0x8b0b002b#32)
  | .p392 => (392, 0xf940016a#32)
  | .p396 => (396, 0xf94003eb#32)
  | .p400 => (400, 0x910043ff#32)
  | .p404 => (404, 0x9100052b#32)
  | .p408 => (408, 0xd10043ff#32)
  | .p412 => (412, 0xf90003eb#32)
  | .p416 => (416, 0xaa0903eb#32)
  | .p420 => (420, 0xd37df16b#32)
  | .p424 => (424, 0x8b0b030b#32)
  | .p428 => (428, 0xf900016a#32)
  | .p432 => (432, 0xf94003eb#32)
  | .p436 => (436, 0x910043ff#32)
  | .p440 => (440, 0xeb0b011f#32)
  | .p444 => (444, 0xaa0b03e9#32)
  | .p448 => (448, 0x54000240#32)
  | .p452 => (452, 0xeb02013f#32)
  | .p456 => (456, 0x54fffd63#32)
  | .p460 => (460, 0x9100052b#32)
  | .p464 => (464, 0xd10043ff#32)
  | .p468 => (468, 0xf90003ea#32)
  | .p472 => (472, 0xf90007eb#32)
  | .p476 => (476, 0xaa0903ea#32)
  | .p480 => (480, 0xd37df14a#32)
  | .p484 => (484, 0x8b0a030a#32)
  | .p488 => (488, 0xd280000b#32)
  | .p492 => (492, 0xf900014b#32)
  | .p496 => (496, 0xf94007eb#32)
  | .p500 => (500, 0xf94003ea#32)
  | .p504 => (504, 0x910043ff#32)
  | .p508 => (508, 0xeb0b011f#32)
  | .p512 => (512, 0xaa0b03e9#32)
  | .p516 => (516, 0x54fffe01#32)
  | .p520 => (520, 0xaa1f03e1#32)
  | .p524 => (524, 0xd10043ff#32)
  | .p528 => (528, 0xf90003e9#32)
  | .p532 => (532, 0xaa1703e9#32)
  | .p536 => (536, 0x8b090309#32)
  | .p540 => (540, 0xf9400135#32)
  | .p544 => (544, 0xf94003e9#32)
  | .p548 => (548, 0x910043ff#32)
  | .p552 => (552, 0xaa1403e2#32)
  | .p556 => (556, 0xaa1f03e3#32)
  | .p560 => (560, 0xaa1503e0#32)
  | .p564 => (564, 0x9400b1d5#32)
  | .p568 => (568, 0x9b147c08#32)
  | .p572 => (572, 0xd10043ff#32)
  | .p576 => (576, 0xf90003e9#32)
  | .p580 => (580, 0xaa1703e9#32)
  | .p584 => (584, 0x8b090309#32)
  | .p588 => (588, 0xf9000120#32)
  | .p592 => (592, 0xf94003e9#32)
  | .p596 => (596, 0x910043ff#32)
  | .p600 => (600, 0xd10022f7#32)
  | .p604 => (604, 0xeb0802a1#32)
  | .p608 => (608, 0xb10022ff#32)
  | .p612 => (612, 0x54fffd41#32)
  | .p616 => (616, 0x14000068#32)
  | .p620 => (620, 0xaa1f03e1#32)
  | .p624 => (624, 0xaa1603e0#32)
  | .p628 => (628, 0xaa1403e2#32)
  | .p632 => (632, 0xaa1f03e3#32)
  | .p636 => (636, 0x9400b1c3#32)
  | .p640 => (640, 0xb5000161#32)
  | .p644 => (644, 0xaa1f03e9#32)
  | .p648 => (648, 0xaa0003ea#32)
  | .p652 => (652, 0x1400001d#32)
  | .p656 => (656, 0xaa1f03e1#32)
  | .p660 => (660, 0xaa1f03f6#32)
  | .p664 => (664, 0xaa1603e0#32)
  | .p668 => (668, 0xaa1403e2#32)
  | .p672 => (672, 0xaa1f03e3#32)
  | .p676 => (676, 0x9400b1b9#32)
  | .p680 => (680, 0xb4fffee1#32)
  | .p684 => (684, 0xf94002a8#32)
  | .p688 => (688, 0xf9400aa9#32)
  | .p692 => (692, 0xab08012a#32)
  | .p696 => (696, 0x540003a2#32)
  | .p700 => (700, 0xb100215f#32)
  | .p704 => (704, 0x54000368#32)
  | .p708 => (708, 0x91001d4b#32)
  | .p712 => (712, 0x927df16b#32)
  | .p716 => (716, 0xcb0a016a#32)
  | .p720 => (720, 0xab090149#32)
  | .p724 => (724, 0x540002c2#32)
  | .p728 => (728, 0xb100453f#32)
  | .p732 => (732, 0x54000288#32)
  | .p736 => (736, 0xf94006ab#32)
  | .p740 => (740, 0x9100412a#32)
  | .p744 => (744, 0xeb0b015f#32)
  | .p748 => (748, 0x54000208#32)
  | .p752 => (752, 0xf9000aaa#32)
  | .p756 => (756, 0x8b090109#32)
  | .p760 => (760, 0x5280004a#32)
  | .p764 => (764, 0xa9000520#32)
  | .p768 => (768, 0x2a1f03e8#32)
  | .p772 => (772, 0xd10043ff#32)
  | .p776 => (776, 0xf90003e9#32)
  | .p780 => (780, 0x9b147c09#32)
  | .p784 => (784, 0xcb0902c1#32)
  | .p788 => (788, 0xf94003e9#32)
  | .p792 => (792, 0x910043ff#32)
  | .p796 => (796, 0xf9000269#32)
  | .p800 => (800, 0x52800209#32)
  | .p804 => (804, 0xf900066a#32)
  | .p808 => (808, 0x1400002a#32)
  | .p812 => (812, 0xaa1f03e1#32)
  | .p816 => (816, 0x5280002a#32)
  | .p820 => (820, 0x52900008#32)
  | .p824 => (824, 0x52800109#32)
  | .p828 => (828, 0xd10043ff#32)
  | .p832 => (832, 0xf90003e9#32)
  | .p836 => (836, 0xf90007ea#32)
  | .p840 => (840, 0x91000269#32)
  | .p844 => (844, 0x9100c129#32)
  | .p848 => (848, 0xd280000a#32)
  | .p852 => (852, 0xf900012a#32)
  | .p856 => (856, 0xd280000a#32)
  | .p860 => (860, 0xf900052a#32)
  | .p864 => (864, 0xf94007ea#32)
  | .p868 => (868, 0xf94003e9#32)
  | .p872 => (872, 0x910043ff#32)
  | .p876 => (876, 0xd10043ff#32)
  | .p880 => (880, 0xf90003e9#32)
  | .p884 => (884, 0xf90007ea#32)
  | .p888 => (888, 0x91000269#32)
  | .p892 => (892, 0x91008129#32)
  | .p896 => (896, 0xd280000a#32)
  | .p900 => (900, 0xf900012a#32)
  | .p904 => (904, 0xd280000a#32)
  | .p908 => (908, 0xf900052a#32)
  | .p912 => (912, 0xf94007ea#32)
  | .p916 => (916, 0xf94003e9#32)
  | .p920 => (920, 0x910043ff#32)
  | .p924 => (924, 0xd10043ff#32)
  | .p928 => (928, 0xf90003e9#32)
  | .p932 => (932, 0xf90007ea#32)
  | .p936 => (936, 0x91000269#32)
  | .p940 => (940, 0x91004129#32)
  | .p944 => (944, 0xd280000a#32)
  | .p948 => (948, 0xf900012a#32)
  | .p952 => (952, 0xd280000a#32)
  | .p956 => (956, 0xf900052a#32)
  | .p960 => (960, 0xf94007ea#32)
  | .p964 => (964, 0xf94003e9#32)
  | .p968 => (968, 0x910043ff#32)
  | .p972 => (972, 0xf900026a#32)
  | .p976 => (976, 0xd10043ff#32)
  | .p980 => (980, 0xf90003ea#32)
  | .p984 => (984, 0xaa0903ea#32)
  | .p988 => (988, 0x8b0a026a#32)
  | .p992 => (992, 0xf9000141#32)
  | .p996 => (996, 0xf94003ea#32)
  | .p1000 => (1000, 0x910043ff#32)
  | .p1004 => (1004, 0xa94257f6#32)
  | .p1008 => (1008, 0xb9004268#32)
  | .p1012 => (1012, 0xa9434ff4#32)
  | .p1016 => (1016, 0xa9415ff8#32)
  | .p1020 => (1020, 0xf84407fe#32)
  | .p1024 => (1024, 0xd65f03c0#32)
  | .p1028 => (1028, 0xaa1f03e1#32)
  | .p1032 => (1032, 0xd1000ac9#32)
  | .p1036 => (1036, 0xb100053f#32)
  | .p1040 => (1040, 0x54000220#32)
  | .p1044 => (1044, 0xd10043ff#32)
  | .p1048 => (1048, 0xf90003eb#32)
  | .p1052 => (1052, 0xaa0903eb#32)
  | .p1056 => (1056, 0xd37df16b#32)
  | .p1060 => (1060, 0x8b0b030b#32)
  | .p1064 => (1064, 0xf940016a#32)
  | .p1068 => (1068, 0xf94003eb#32)
  | .p1072 => (1072, 0x910043ff#32)
  | .p1076 => (1076, 0xaa0903e8#32)
  | .p1080 => (1080, 0xd1000529#32)
  | .p1084 => (1084, 0xb4fffe8a#32)
  | .p1088 => (1088, 0x9100050a#32)
  | .p1092 => (1092, 0xf100055f#32)
  | .p1096 => (1096, 0x540000a1#32)
  | .p1100 => (1100, 0xf940030a#32)
  | .p1104 => (1104, 0x14000002#32)
  | .p1108 => (1108, 0xaa1f03ea#32)
  | .p1112 => (1112, 0xaa1f03f8#32)
  | .p1116 => (1116, 0x2a1f03e8#32)
  | .p1120 => (1120, 0xf9000278#32)
  | .p1124 => (1124, 0x17ffffaf#32)

@[simp] theorem Op.row_mem (op : Op) : op.row ∈ program := by
  cases op <;> decide

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

/-- Architectural effects, including all lowered stack accesses, flag writes,
link-register updates, and returns. BL only performs its architectural branch;
the callee is composed separately. -/
def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => put 31 ((r (.GPR 31#5) s) - 64#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 30#5) s) s)
  | .p8, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 16#64) ((r (.GPR 23#5) s) ++ (r (.GPR 24#5) s)) s)
  | .p12, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 32#64) ((r (.GPR 21#5) s) ++ (r (.GPR 22#5) s)) s)
  | .p16, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 48#64) ((r (.GPR 19#5) s) ++ (r (.GPR 20#5) s)) s)
  | .p20, s => put 21 ((r (.GPR 4#5) s)) s
  | .p24, s => put 20 ((r (.GPR 3#5) s)) s
  | .p28, s => put 19 ((r (.GPR 0#5) s)) s
  | .p32, s => w .PC (if (r (.GPR 1#5) s) = 0#64 then base + 300#64 else base + 36#64) s
  | .p36, s => put 9 ((r (.GPR 2#5) s) - 1#64) s
  | .p40, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).2 (next s)
  | .p44, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 328#64 else base + 48#64) s
  | .p48, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p52, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p56, s => put 11 ((r (.GPR 9#5) s)) s
  | .p60, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p64, s => put 11 ((r (.GPR 1#5) s) + (r (.GPR 11#5) s)) s
  | .p68, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p72, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p76, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p80, s => put 8 ((r (.GPR 9#5) s)) s
  | .p84, s => put 9 ((r (.GPR 9#5) s) - 1#64) s
  | .p88, s => w .PC (if (r (.GPR 10#5) s) = 0#64 then base + 40#64 else base + 92#64) s
  | .p92, s => put 8 ((r (.GPR 8#5) s) + 1#64) s
  | .p96, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~3#64) 1#1).2 (next s)
  | .p100, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 332#64 else base + 104#64) s
  | .p104, s => put 23 ((r (.GPR 2#5) s) <<< 3) s
  | .p108, s => put 8 ((r (.GPR 2#5) s) + 1#64) s
  | .p112, s => put 9 ((r (.GPR 1#5) s) - 8#64) s
  | .p116, s => put 24 (8#64) s
  | .p120, s => put 22 ((r (.GPR 8#5) s)) s
  | .p124, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~1#64) 1#1).2 (put 8 ((r (.GPR 8#5) s) - 1#64) s)
  | .p128, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 1028#64 else base + 132#64) s
  | .p132, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p136, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p140, s => put 11 ((r (.GPR 23#5) s)) s
  | .p144, s => put 11 ((r (.GPR 9#5) s) + (r (.GPR 11#5) s)) s
  | .p148, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p152, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p156, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p160, s => put 23 ((r (.GPR 23#5) s) - 8#64) s
  | .p164, s => w .PC (if (r (.GPR 10#5) s) = 0#64 then base + 120#64 else base + 168#64) s
  | .p168, s => put 9 ((r (.GPR 8#5) s) >>> 61) s
  | .p172, s => w .PC (if (r (.GPR 9#5) s) ≠ 0#64 then base + 812#64 else base + 176#64) s
  | .p176, s => put 9 ((r (.GPR 8#5) s) <<< 3) s
  | .p180, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p184, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p188, s => put 10 ((r (.GPR 9#5) s) &&& 9223372036854775808#64) s
  | .p192, s => w .PC (if (r (.GPR 10#5) s) ≠ 0#64 then base + 208#64 else base + 196#64) s
  | .p196, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p200, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p204, s => w .PC (base + 220#64) s
  | .p208, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p212, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p216, s => w .PC (base + 812#64) s
  | .p220, s => put 10 (read_mem_bytes 8 (r (.GPR 21#5) s) s) s
  | .p224, s => put 11 (read_mem_bytes 8 ((r (.GPR 21#5) s) + 16#64) s) s
  | .p228, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) (r (.GPR 10#5) s) 0#1).2 (put 12 ((r (.GPR 11#5) s) + (r (.GPR 10#5) s)) s)
  | .p232, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 812#64 else base + 236#64) s
  | .p236, s => write_pstate (AddWithCarry (r (.GPR 12#5) s) 8#64 0#1).2 (next s)
  | .p240, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 812#64 else base + 244#64) s
  | .p244, s => put 13 ((r (.GPR 12#5) s) + 7#64) s
  | .p248, s => put 13 ((r (.GPR 13#5) s) &&& 18446744073709551608#64) s
  | .p252, s => put 12 ((r (.GPR 13#5) s) - (r (.GPR 12#5) s)) s
  | .p256, s => write_pstate (AddWithCarry (r (.GPR 12#5) s) (r (.GPR 11#5) s) 0#1).2 (put 11 ((r (.GPR 12#5) s) + (r (.GPR 11#5) s)) s)
  | .p260, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 812#64 else base + 264#64) s
  | .p264, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) (r (.GPR 9#5) s) 0#1).2 (put 12 ((r (.GPR 11#5) s) + (r (.GPR 9#5) s)) s)
  | .p268, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 812#64 else base + 272#64) s
  | .p272, s => put 9 (read_mem_bytes 8 ((r (.GPR 21#5) s) + 8#64) s) s
  | .p276, s => write_pstate (AddWithCarry (r (.GPR 12#5) s) (~~~(r (.GPR 9#5) s)) 1#1).2 (next s)
  | .p280, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 812#64 else base + 284#64) s
  | .p284, s => put 9 (0#64) s
  | .p288, s => put 24 ((r (.GPR 10#5) s) + (r (.GPR 11#5) s)) s
  | .p292, s => next (write_mem_bytes 8 ((r (.GPR 21#5) s) + 16#64) (r (.GPR 12#5) s) s)
  | .p296, s => w .PC (base + 452#64) s
  | .p300, s => put 22 ((r (.GPR 2#5) s)) s
  | .p304, s => put 0 ((r (.GPR 22#5) s)) s
  | .p308, s => put 2 ((r (.GPR 20#5) s)) s
  | .p312, s => put 3 (0#64) s
  | .p316, s => w .PC (base + 182664#64) (w (.GPR 30#5) (base + 320#64) s)
  | .p320, s => w .PC (if (r (.GPR 1#5) s) = 0#64 then base + 644#64 else base + 324#64) s
  | .p324, s => w .PC (base + 684#64) s
  | .p328, s => w .PC (if (r (.GPR 2#5) s) = 0#64 then base + 656#64 else base + 332#64) s
  | .p332, s => put 22 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p336, s => write_pstate (AddWithCarry (r (.GPR 2#5) s) (~~~2#64) 1#1).2 (next s)
  | .p340, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 620#64 else base + 344#64) s
  | .p344, s => put 1 (read_mem_bytes 8 ((r (.GPR 1#5) s) + 8#64) s) s
  | .p348, s => put 0 ((r (.GPR 22#5) s)) s
  | .p352, s => put 2 ((r (.GPR 20#5) s)) s
  | .p356, s => put 3 (0#64) s
  | .p360, s => w .PC (base + 182664#64) (w (.GPR 30#5) (base + 364#64) s)
  | .p364, s => w .PC (if (r (.GPR 1#5) s) = 0#64 then base + 644#64 else base + 368#64) s
  | .p368, s => w .PC (base + 684#64) s
  | .p372, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p376, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p380, s => put 11 ((r (.GPR 9#5) s)) s
  | .p384, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p388, s => put 11 ((r (.GPR 1#5) s) + (r (.GPR 11#5) s)) s
  | .p392, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p396, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p400, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p404, s => put 11 ((r (.GPR 9#5) s) + 1#64) s
  | .p408, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p412, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p416, s => put 11 ((r (.GPR 9#5) s)) s
  | .p420, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p424, s => put 11 ((r (.GPR 24#5) s) + (r (.GPR 11#5) s)) s
  | .p428, s => next (write_mem_bytes 8 (r (.GPR 11#5) s) (r (.GPR 10#5) s) s)
  | .p432, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p436, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p440, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~(r (.GPR 11#5) s)) 1#1).2 (next s)
  | .p444, s => put 9 ((r (.GPR 11#5) s)) s
  | .p448, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 520#64 else base + 452#64) s
  | .p452, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (~~~(r (.GPR 2#5) s)) 1#1).2 (next s)
  | .p456, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 372#64 else base + 460#64) s
  | .p460, s => put 11 ((r (.GPR 9#5) s) + 1#64) s
  | .p464, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p468, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p472, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p476, s => put 10 ((r (.GPR 9#5) s)) s
  | .p480, s => put 10 ((r (.GPR 10#5) s) <<< 3) s
  | .p484, s => put 10 ((r (.GPR 24#5) s) + (r (.GPR 10#5) s)) s
  | .p488, s => put 11 (0#64) s
  | .p492, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 11#5) s) s)
  | .p496, s => put 11 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p500, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p504, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p508, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~(r (.GPR 11#5) s)) 1#1).2 (next s)
  | .p512, s => put 9 ((r (.GPR 11#5) s)) s
  | .p516, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 452#64 else base + 520#64) s
  | .p520, s => put 1 (0#64) s
  | .p524, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p528, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p532, s => put 9 ((r (.GPR 23#5) s)) s
  | .p536, s => put 9 ((r (.GPR 24#5) s) + (r (.GPR 9#5) s)) s
  | .p540, s => put 21 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p544, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p548, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p552, s => put 2 ((r (.GPR 20#5) s)) s
  | .p556, s => put 3 (0#64) s
  | .p560, s => put 0 ((r (.GPR 21#5) s)) s
  | .p564, s => w .PC (base + 182664#64) (w (.GPR 30#5) (base + 568#64) s)
  | .p568, s => put 8 ((r (.GPR 0#5) s) * (r (.GPR 20#5) s)) s
  | .p572, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p576, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p580, s => put 9 ((r (.GPR 23#5) s)) s
  | .p584, s => put 9 ((r (.GPR 24#5) s) + (r (.GPR 9#5) s)) s
  | .p588, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 0#5) s) s)
  | .p592, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p596, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p600, s => put 23 ((r (.GPR 23#5) s) - 8#64) s
  | .p604, s => write_pstate (AddWithCarry (r (.GPR 21#5) s) (~~~(r (.GPR 8#5) s)) 1#1).2 (put 1 ((r (.GPR 21#5) s) - (r (.GPR 8#5) s)) s)
  | .p608, s => write_pstate (AddWithCarry (r (.GPR 23#5) s) 8#64 0#1).2 (next s)
  | .p612, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 524#64 else base + 616#64) s
  | .p616, s => w .PC (base + 1032#64) s
  | .p620, s => put 1 (0#64) s
  | .p624, s => put 0 ((r (.GPR 22#5) s)) s
  | .p628, s => put 2 ((r (.GPR 20#5) s)) s
  | .p632, s => put 3 (0#64) s
  | .p636, s => w .PC (base + 182664#64) (w (.GPR 30#5) (base + 640#64) s)
  | .p640, s => w .PC (if (r (.GPR 1#5) s) ≠ 0#64 then base + 684#64 else base + 644#64) s
  | .p644, s => put 9 (0#64) s
  | .p648, s => put 10 ((r (.GPR 0#5) s)) s
  | .p652, s => w .PC (base + 768#64) s
  | .p656, s => put 1 (0#64) s
  | .p660, s => put 22 (0#64) s
  | .p664, s => put 0 ((r (.GPR 22#5) s)) s
  | .p668, s => put 2 ((r (.GPR 20#5) s)) s
  | .p672, s => put 3 (0#64) s
  | .p676, s => w .PC (base + 182664#64) (w (.GPR 30#5) (base + 680#64) s)
  | .p680, s => w .PC (if (r (.GPR 1#5) s) = 0#64 then base + 644#64 else base + 684#64) s
  | .p684, s => put 8 (read_mem_bytes 8 (r (.GPR 21#5) s) s) s
  | .p688, s => put 9 (read_mem_bytes 8 ((r (.GPR 21#5) s) + 16#64) s) s
  | .p692, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (r (.GPR 8#5) s) 0#1).2 (put 10 ((r (.GPR 9#5) s) + (r (.GPR 8#5) s)) s)
  | .p696, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 812#64 else base + 700#64) s
  | .p700, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 8#64 0#1).2 (next s)
  | .p704, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 812#64 else base + 708#64) s
  | .p708, s => put 11 ((r (.GPR 10#5) s) + 7#64) s
  | .p712, s => put 11 ((r (.GPR 11#5) s) &&& 18446744073709551608#64) s
  | .p716, s => put 10 ((r (.GPR 11#5) s) - (r (.GPR 10#5) s)) s
  | .p720, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 9#5) s) 0#1).2 (put 9 ((r (.GPR 10#5) s) + (r (.GPR 9#5) s)) s)
  | .p724, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 812#64 else base + 728#64) s
  | .p728, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 17#64 0#1).2 (next s)
  | .p732, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 812#64 else base + 736#64) s
  | .p736, s => put 11 (read_mem_bytes 8 ((r (.GPR 21#5) s) + 8#64) s) s
  | .p740, s => put 10 ((r (.GPR 9#5) s) + 16#64) s
  | .p744, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (~~~(r (.GPR 11#5) s)) 1#1).2 (next s)
  | .p748, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 812#64 else base + 752#64) s
  | .p752, s => next (write_mem_bytes 8 ((r (.GPR 21#5) s) + 16#64) (r (.GPR 10#5) s) s)
  | .p756, s => put 9 ((r (.GPR 8#5) s) + (r (.GPR 9#5) s)) s
  | .p760, s => put 10 (2#64) s
  | .p764, s => next (write_mem_bytes 16 (r (.GPR 9#5) s) ((r (.GPR 1#5) s) ++ (r (.GPR 0#5) s)) s)
  | .p768, s => put 8 (((0#64).setWidth 32).setWidth 64) s
  | .p772, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p776, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p780, s => put 9 ((r (.GPR 0#5) s) * (r (.GPR 20#5) s)) s
  | .p784, s => put 1 ((r (.GPR 22#5) s) - (r (.GPR 9#5) s)) s
  | .p788, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p792, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p796, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 9#5) s) s)
  | .p800, s => put 9 (16#64) s
  | .p804, s => next (write_mem_bytes 8 ((r (.GPR 19#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p808, s => w .PC (base + 976#64) s
  | .p812, s => put 1 (0#64) s
  | .p816, s => put 10 (1#64) s
  | .p820, s => put 8 (32768#64) s
  | .p824, s => put 9 (8#64) s
  | .p828, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p832, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p836, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p840, s => put 9 ((r (.GPR 19#5) s) + 0#64) s
  | .p844, s => put 9 ((r (.GPR 9#5) s) + 48#64) s
  | .p848, s => put 10 (0#64) s
  | .p852, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p856, s => put 10 (0#64) s
  | .p860, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p864, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p868, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p872, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p876, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p880, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p884, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p888, s => put 9 ((r (.GPR 19#5) s) + 0#64) s
  | .p892, s => put 9 ((r (.GPR 9#5) s) + 32#64) s
  | .p896, s => put 10 (0#64) s
  | .p900, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p904, s => put 10 (0#64) s
  | .p908, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p912, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p916, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p920, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p924, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p928, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p932, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p936, s => put 9 ((r (.GPR 19#5) s) + 0#64) s
  | .p940, s => put 9 ((r (.GPR 9#5) s) + 16#64) s
  | .p944, s => put 10 (0#64) s
  | .p948, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p952, s => put 10 (0#64) s
  | .p956, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p960, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p964, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p968, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p972, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 10#5) s) s)
  | .p976, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p980, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p984, s => put 10 ((r (.GPR 9#5) s)) s
  | .p988, s => put 10 ((r (.GPR 19#5) s) + (r (.GPR 10#5) s)) s
  | .p992, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 1#5) s) s)
  | .p996, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p1000, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p1004, s => next (w (.GPR 21#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 32#64) + 8#64) s) (w (.GPR 22#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 32#64) s) s))
  | .p1008, s => next (write_mem_bytes 4 ((r (.GPR 19#5) s) + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)
  | .p1012, s => next (w (.GPR 19#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 48#64) + 8#64) s) (w (.GPR 20#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 48#64) s) s))
  | .p1016, s => next (w (.GPR 23#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 16#64) + 8#64) s) (w (.GPR 24#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 16#64) s) s))
  | .p1020, s => w (.GPR 31#5) ((r (.GPR 31#5) s) + 64#64) (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s)
  | .p1024, s => w .PC (r (.GPR 30#5) s) s
  | .p1028, s => put 1 (0#64) s
  | .p1032, s => put 9 ((r (.GPR 22#5) s) - 2#64) s
  | .p1036, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).2 (next s)
  | .p1040, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 1108#64 else base + 1044#64) s
  | .p1044, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p1048, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p1052, s => put 11 ((r (.GPR 9#5) s)) s
  | .p1056, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p1060, s => put 11 ((r (.GPR 24#5) s) + (r (.GPR 11#5) s)) s
  | .p1064, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p1068, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p1072, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p1076, s => put 8 ((r (.GPR 9#5) s)) s
  | .p1080, s => put 9 ((r (.GPR 9#5) s) - 1#64) s
  | .p1084, s => w .PC (if (r (.GPR 10#5) s) = 0#64 then base + 1036#64 else base + 1088#64) s
  | .p1088, s => put 10 ((r (.GPR 8#5) s) + 1#64) s
  | .p1092, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (~~~1#64) 1#1).2 (next s)
  | .p1096, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 1116#64 else base + 1100#64) s
  | .p1100, s => put 10 (read_mem_bytes 8 (r (.GPR 24#5) s) s) s
  | .p1104, s => w .PC (base + 1112#64) s
  | .p1108, s => put 10 (0#64) s
  | .p1112, s => put 24 (0#64) s
  | .p1116, s => put 8 (((0#64).setWidth 32).setWidth 64) s
  | .p1120, s => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 24#5) s) s)
  | .p1124, s => w .PC (base + 800#64) s

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

/-- No instruction in this routine modifies a SIMD register. -/
@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

def Op.stackDelta : Op → BitVec 64
  | .p0 => -64#64
  | .p48 | .p132 | .p180 | .p372 | .p408 | .p464 | .p524 | .p572 | .p772 | .p828 | .p876 | .p924 | .p976 | .p1044 => -16#64
  | .p76 | .p156 | .p200 | .p212 | .p400 | .p436 | .p504 | .p548 | .p596 | .p792 | .p872 | .p920 | .p968 | .p1000 | .p1072 => 16#64
  | .p1020 => 64#64
  | _ => 0#64

theorem Op.sp (op : Op) (base : BitVec 64) (s : ArmState) :
    r (.GPR 31#5) (op.effect base s) = r (.GPR 31#5) s + op.stackDelta := by
  cases op <;> simp [Op.effect, put, next, Op.stackDelta,
    state_simp_rules, BitVec.sub_eq_add_neg]

theorem Op.stackDelta_aligned (op : Op) : op.stackDelta.toNat % 16 = 0 := by
  cases op <;> decide

private theorem aligned_delta (x : BitVec 64) (h : Aligned x 4)
    (delta : BitVec 64) (hd : delta.toNat % 16 = 0) : Aligned (x + delta) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  have h := aligned_delta (r (.GPR 31#5) s) (BoolCodec.stack_aligned s ha)
    op.stackDelta op.stackDelta_aligned
  simpa only [CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory,
    Op.sp] using h

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

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

end SszArm.NatDivision

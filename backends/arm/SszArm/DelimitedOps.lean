import SszArm.DelimitedImpl
import SszArm.BoolMemory
import SszArm.BoolAlignment

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

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
  | p960 | p964 | p968 | p972 | p976 | p980 | p984 | p988 | p992 | p996 | p1000 | p1004 | p1008
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb4000623#32)
  | .p4 => (4, 0xa9ba7bfd#32)
  | .p8 => (8, 0xa9016ffc#32)
  | .p12 => (12, 0xa90267fa#32)
  | .p16 => (16, 0xa9035ff8#32)
  | .p20 => (20, 0xa90457f6#32)
  | .p24 => (24, 0xa9054ff4#32)
  | .p28 => (28, 0xd1000479#32)
  | .p32 => (32, 0xd10043ff#32)
  | .p36 => (36, 0xf90003e9#32)
  | .p40 => (40, 0xaa1903e9#32)
  | .p44 => (44, 0x8b090049#32)
  | .p48 => (48, 0x39400128#32)
  | .p52 => (52, 0xf94003e9#32)
  | .p56 => (56, 0x910043ff#32)
  | .p60 => (60, 0x340003e8#32)
  | .p64 => (64, 0x53081d08#32)
  | .p68 => (68, 0xd2800029#32)
  | .p72 => (72, 0xd37dff37#32)
  | .p76 => (76, 0xf2e40009#32)
  | .p80 => (80, 0xd10043ff#32)
  | .p84 => (84, 0xf90003e9#32)
  | .p88 => (88, 0xf90007ea#32)
  | .p92 => (92, 0x2a0803e9#32)
  | .p96 => (96, 0x5280040a#32)
  | .p100 => (100, 0x34000089#32)
  | .p104 => (104, 0x5100054a#32)
  | .p108 => (108, 0x53017d29#32)
  | .p112 => (112, 0x35ffffc9#32)
  | .p116 => (116, 0x2a0a03fa#32)
  | .p120 => (120, 0xf94007ea#32)
  | .p124 => (124, 0xf94003e9#32)
  | .p128 => (128, 0x910043ff#32)
  | .p132 => (132, 0xeb09007f#32)
  | .p136 => (136, 0x52000b48#32)
  | .p140 => (140, 0xaa190d18#32)
  | .p144 => (144, 0x540003e2#32)
  | .p148 => (148, 0xaa1f03f4#32)
  | .p152 => (152, 0xaa1803f3#32)
  | .p156 => (156, 0xb9400028#32)
  | .p160 => (160, 0x7100051f#32)
  | .p164 => (164, 0x54000640#32)
  | .p168 => (168, 0x1400005d#32)
  | .p172 => (172, 0x38401448#32)
  | .p176 => (176, 0xd1000463#32)
  | .p180 => (180, 0x35000da8#32)
  | .p184 => (184, 0xb5ffffa3#32)
  | .p188 => (188, 0x52800229#32)
  | .p192 => (192, 0x1400006b#32)
  | .p196 => (196, 0x6f00e400#32)
  | .p200 => (200, 0x52800028#32)
  | .p204 => (204, 0x52800209#32)
  | .p208 => (208, 0xd10043ff#32)
  | .p212 => (212, 0xf90003e9#32)
  | .p216 => (216, 0xf90007ea#32)
  | .p220 => (220, 0x91000009#32)
  | .p224 => (224, 0x91010129#32)
  | .p228 => (228, 0xd280000a#32)
  | .p232 => (232, 0xf900012a#32)
  | .p236 => (236, 0xf94007ea#32)
  | .p240 => (240, 0xf94003e9#32)
  | .p244 => (244, 0x910043ff#32)
  | .p248 => (248, 0xa9002008#32)
  | .p252 => (252, 0xb9004809#32)
  | .p256 => (256, 0xad008000#32)
  | .p260 => (260, 0x3d800c00#32)
  | .p264 => (264, 0xd65f03c0#32)
  | .p268 => (268, 0xf9400088#32)
  | .p272 => (272, 0xf9400889#32)
  | .p276 => (276, 0xab08012a#32)
  | .p280 => (280, 0x54000ec2#32)
  | .p284 => (284, 0xb100215f#32)
  | .p288 => (288, 0x54000e88#32)
  | .p292 => (292, 0x91001d4b#32)
  | .p296 => (296, 0x927df16b#32)
  | .p300 => (300, 0xcb0a016a#32)
  | .p304 => (304, 0xab090149#32)
  | .p308 => (308, 0x54000de2#32)
  | .p312 => (312, 0xb100453f#32)
  | .p316 => (316, 0x54000da8#32)
  | .p320 => (320, 0xf940048b#32)
  | .p324 => (324, 0x9100412a#32)
  | .p328 => (328, 0xeb0b015f#32)
  | .p332 => (332, 0x54000d28#32)
  | .p336 => (336, 0x8b090114#32)
  | .p340 => (340, 0x52800053#32)
  | .p344 => (344, 0xf900088a#32)
  | .p348 => (348, 0xa9005e98#32)
  | .p352 => (352, 0xb9400028#32)
  | .p356 => (356, 0x7100051f#32)
  | .p360 => (360, 0x540005a1#32)
  | .p364 => (364, 0xa940d436#32)
  | .p368 => (368, 0xaa0003fb#32)
  | .p372 => (372, 0xaa1403e0#32)
  | .p376 => (376, 0xaa1303e1#32)
  | .p380 => (380, 0xaa0203fc#32)
  | .p384 => (384, 0xaa0303fd#32)
  | .p388 => (388, 0xaa1603e2#32)
  | .p392 => (392, 0xaa1503e3#32)
  | .p396 => (396, 0x97ffbb50#32)
  | .p400 => (400, 0xaa1d03e3#32)
  | .p404 => (404, 0xaa1c03e2#32)
  | .p408 => (408, 0x13001c08#32)
  | .p412 => (412, 0xaa1b03e0#32)
  | .p416 => (416, 0x7100051f#32)
  | .p420 => (420, 0x540003cb#32)
  | .p424 => (424, 0x52800028#32)
  | .p428 => (428, 0xd10043ff#32)
  | .p432 => (432, 0xf90003e9#32)
  | .p436 => (436, 0xf90007ea#32)
  | .p440 => (440, 0x91000009#32)
  | .p444 => (444, 0x9100e129#32)
  | .p448 => (448, 0xd280000a#32)
  | .p452 => (452, 0xf900012a#32)
  | .p456 => (456, 0xd280000a#32)
  | .p460 => (460, 0xf900052a#32)
  | .p464 => (464, 0xf94007ea#32)
  | .p468 => (468, 0xf94003e9#32)
  | .p472 => (472, 0x910043ff#32)
  | .p476 => (476, 0x52800049#32)
  | .p480 => (480, 0xd10043ff#32)
  | .p484 => (484, 0xf90003e9#32)
  | .p488 => (488, 0xf90007ea#32)
  | .p492 => (492, 0x91000009#32)
  | .p496 => (496, 0x91002129#32)
  | .p500 => (500, 0xf9000128#32)
  | .p504 => (504, 0xd280000a#32)
  | .p508 => (508, 0xf900052a#32)
  | .p512 => (512, 0xf94007ea#32)
  | .p516 => (516, 0xf94003e9#32)
  | .p520 => (520, 0x910043ff#32)
  | .p524 => (524, 0x52800608#32)
  | .p528 => (528, 0x5280050a#32)
  | .p532 => (532, 0xa901d416#32)
  | .p536 => (536, 0x1400005f#32)
  | .p540 => (540, 0x71001f5f#32)
  | .p544 => (544, 0x54000061#32)
  | .p548 => (548, 0x52800008#32)
  | .p552 => (552, 0x14000002#32)
  | .p556 => (556, 0x52800028#32)
  | .p560 => (560, 0x9a830329#32)
  | .p564 => (564, 0xab190108#32)
  | .p568 => (568, 0x54000062#32)
  | .p572 => (572, 0x5280000a#32)
  | .p576 => (576, 0x14000002#32)
  | .p580 => (580, 0x5280002a#32)
  | .p584 => (584, 0xca090108#32)
  | .p588 => (588, 0xaa0a0108#32)
  | .p592 => (592, 0xb50002e8#32)
  | .p596 => (596, 0x5280006a#32)
  | .p600 => (600, 0xa9022402#32)
  | .p604 => (604, 0x3900400a#32)
  | .p608 => (608, 0xa9035c18#32)
  | .p612 => (612, 0x1400005c#32)
  | .p616 => (616, 0x52800249#32)
  | .p620 => (620, 0x6f00e400#32)
  | .p624 => (624, 0x52800028#32)
  | .p628 => (628, 0xd10043ff#32)
  | .p632 => (632, 0xf90003e9#32)
  | .p636 => (636, 0xf90007ea#32)
  | .p640 => (640, 0x91000009#32)
  | .p644 => (644, 0x91010129#32)
  | .p648 => (648, 0xd280000a#32)
  | .p652 => (652, 0xf900012a#32)
  | .p656 => (656, 0xf94007ea#32)
  | .p660 => (660, 0xf94003e9#32)
  | .p664 => (664, 0x910043ff#32)
  | .p668 => (668, 0xf9000408#32)
  | .p672 => (672, 0xad008000#32)
  | .p676 => (676, 0x3d800c00#32)
  | .p680 => (680, 0x1400004a#32)
  | .p684 => (684, 0x6f00e400#32)
  | .p688 => (688, 0x52800028#32)
  | .p692 => (692, 0xd10043ff#32)
  | .p696 => (696, 0xf90003e9#32)
  | .p700 => (700, 0xf90007ea#32)
  | .p704 => (704, 0x91000009#32)
  | .p708 => (708, 0x91010129#32)
  | .p712 => (712, 0xd280000a#32)
  | .p716 => (716, 0xf900012a#32)
  | .p720 => (720, 0xf94007ea#32)
  | .p724 => (724, 0xf94003e9#32)
  | .p728 => (728, 0x910043ff#32)
  | .p732 => (732, 0xf9000408#32)
  | .p736 => (736, 0x52900049#32)
  | .p740 => (740, 0xad008000#32)
  | .p744 => (744, 0x3d800c00#32)
  | .p748 => (748, 0x14000039#32)
  | .p752 => (752, 0xaa1f03f3#32)
  | .p756 => (756, 0x52900009#32)
  | .p760 => (760, 0x52800208#32)
  | .p764 => (764, 0x52800034#32)
  | .p768 => (768, 0x5280010a#32)
  | .p772 => (772, 0xd10043ff#32)
  | .p776 => (776, 0xf90003e9#32)
  | .p780 => (780, 0xf90007ea#32)
  | .p784 => (784, 0x91000009#32)
  | .p788 => (788, 0x9100e129#32)
  | .p792 => (792, 0xd280000a#32)
  | .p796 => (796, 0xf900012a#32)
  | .p800 => (800, 0xd280000a#32)
  | .p804 => (804, 0xf900052a#32)
  | .p808 => (808, 0xf94007ea#32)
  | .p812 => (812, 0xf94003e9#32)
  | .p816 => (816, 0x910043ff#32)
  | .p820 => (820, 0xd10043ff#32)
  | .p824 => (824, 0xf90003e9#32)
  | .p828 => (828, 0xf90007ea#32)
  | .p832 => (832, 0x91000009#32)
  | .p836 => (836, 0x9100a129#32)
  | .p840 => (840, 0xd280000a#32)
  | .p844 => (844, 0xf900012a#32)
  | .p848 => (848, 0xd280000a#32)
  | .p852 => (852, 0xf900052a#32)
  | .p856 => (856, 0xf94007ea#32)
  | .p860 => (860, 0xf94003e9#32)
  | .p864 => (864, 0x910043ff#32)
  | .p868 => (868, 0xd10043ff#32)
  | .p872 => (872, 0xf90003e9#32)
  | .p876 => (876, 0xf90007ea#32)
  | .p880 => (880, 0x91000009#32)
  | .p884 => (884, 0x91006129#32)
  | .p888 => (888, 0xd280000a#32)
  | .p892 => (892, 0xf900012a#32)
  | .p896 => (896, 0xd280000a#32)
  | .p900 => (900, 0xf900052a#32)
  | .p904 => (904, 0xf94007ea#32)
  | .p908 => (908, 0xf94003e9#32)
  | .p912 => (912, 0x910043ff#32)
  | .p916 => (916, 0xd10043ff#32)
  | .p920 => (920, 0xf90003e9#32)
  | .p924 => (924, 0xaa0a03e9#32)
  | .p928 => (928, 0x8b090009#32)
  | .p932 => (932, 0xf9000134#32)
  | .p936 => (936, 0xf94003e9#32)
  | .p940 => (940, 0x910043ff#32)
  | .p944 => (944, 0xd10043ff#32)
  | .p948 => (948, 0xf90003e9#32)
  | .p952 => (952, 0xaa0803e9#32)
  | .p956 => (956, 0x8b090009#32)
  | .p960 => (960, 0xf9000133#32)
  | .p964 => (964, 0xf94003e9#32)
  | .p968 => (968, 0x910043ff#32)
  | .p972 => (972, 0x52800028#32)
  | .p976 => (976, 0xb9004809#32)
  | .p980 => (980, 0xa9454ff4#32)
  | .p984 => (984, 0xa94457f6#32)
  | .p988 => (988, 0xa9435ff8#32)
  | .p992 => (992, 0xa94267fa#32)
  | .p996 => (996, 0xa9416ffc#32)
  | .p1000 => (1000, 0xa8c67bfd#32)
  | .p1004 => (1004, 0xf9000008#32)
  | .p1008 => (1008, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

/-- Architectural effects, including SIMD writes and every lowered stack access. -/
def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if (r (.GPR 3#5) s) = 0#64 then base + 196#64 else base + 4#64) s
  | .p4, s => w (.GPR 31#5) ((r (.GPR 31#5) s) + -96#64) (next (write_mem_bytes 16 ((r (.GPR 31#5) s) + -96#64) ((r (.GPR 30#5) s) ++ (r (.GPR 29#5) s)) s))
  | .p8, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 16#64) ((r (.GPR 27#5) s) ++ (r (.GPR 28#5) s)) s)
  | .p12, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 32#64) ((r (.GPR 25#5) s) ++ (r (.GPR 26#5) s)) s)
  | .p16, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 48#64) ((r (.GPR 23#5) s) ++ (r (.GPR 24#5) s)) s)
  | .p20, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 64#64) ((r (.GPR 21#5) s) ++ (r (.GPR 22#5) s)) s)
  | .p24, s => next (write_mem_bytes 16 ((r (.GPR 31#5) s) + 80#64) ((r (.GPR 19#5) s) ++ (r (.GPR 20#5) s)) s)
  | .p28, s => put 25 ((r (.GPR 3#5) s) - 1#64) s
  | .p32, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p36, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p40, s => put 9 ((r (.GPR 25#5) s)) s
  | .p44, s => put 9 ((r (.GPR 2#5) s) + (r (.GPR 9#5) s)) s
  | .p48, s => put 8 ((read_mem_bytes 1 (r (.GPR 9#5) s) s).setWidth 64) s
  | .p52, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p56, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p60, s => w .PC (if ((r (.GPR 8#5) s).setWidth 32) = 0#32 then base + 184#64 else base + 64#64) s
  | .p64, s => put 8 ((((r (.GPR 8#5) s).setWidth 32) <<< 24).setWidth 64) s
  | .p68, s => put 9 (1#64) s
  | .p72, s => put 23 ((r (.GPR 25#5) s) >>> 61) s
  | .p76, s => put 9 (((r (.GPR 9#5) s) &&& 281474976710655#64) ||| 2305843009213693952#64) s
  | .p80, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p84, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p88, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p92, s => put 9 ((((r (.GPR 8#5) s).setWidth 32).setWidth 64)) s
  | .p96, s => put 10 32#64 s
  | .p100, s => w .PC (if ((r (.GPR 9#5) s).setWidth 32) = 0#32 then base + 116#64 else base + 104#64) s
  | .p104, s => put 10 ((((r (.GPR 10#5) s).setWidth 32) - 1#32).setWidth 64) s
  | .p108, s => put 9 ((((r (.GPR 9#5) s).setWidth 32) >>> 1).setWidth 64) s
  | .p112, s => w .PC (if ((r (.GPR 9#5) s).setWidth 32) ≠ 0#32 then base + 104#64 else base + 116#64) s
  | .p116, s => put 26 ((((r (.GPR 10#5) s).setWidth 32).setWidth 64)) s
  | .p120, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p124, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p128, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p132, s => write_pstate (AddWithCarry (r (.GPR 3#5) s) (~~~(r (.GPR 9#5) s)) 1#1).2 (next s)
  | .p136, s => put 8 ((((r (.GPR 26#5) s).setWidth 32) ^^^ 7#32).setWidth 64) s
  | .p140, s => put 24 ((r (.GPR 8#5) s) ||| ((r (.GPR 25#5) s) <<< 3)) s
  | .p144, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 268#64 else base + 148#64) s
  | .p148, s => put 20 (0#64) s
  | .p152, s => put 19 ((r (.GPR 24#5) s)) s
  | .p156, s => put 8 ((read_mem_bytes 4 (r (.GPR 1#5) s) s).setWidth 64) s
  | .p160, s => write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~1#32) 1#1).2 (next s)
  | .p164, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 364#64 else base + 168#64) s
  | .p168, s => w .PC (base + 540#64) s
  | .p172, s => w (.GPR 2#5) ((r (.GPR 2#5) s) + 1#64) (put 8 ((read_mem_bytes 1 (r (.GPR 2#5) s) s).setWidth 64) s)
  | .p176, s => put 3 ((r (.GPR 3#5) s) - 1#64) s
  | .p180, s => w .PC (if ((r (.GPR 8#5) s).setWidth 32) ≠ 0#32 then base + 616#64 else base + 184#64) s
  | .p184, s => w .PC (if (r (.GPR 3#5) s) ≠ 0#64 then base + 172#64 else base + 188#64) s
  | .p188, s => put 9 17#64 s
  | .p192, s => w .PC (base + 620#64) s
  | .p196, s => next (w (.SFP 0#5) 0#128 s)
  | .p200, s => put 8 1#64 s
  | .p204, s => put 9 16#64 s
  | .p208, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p212, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p216, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p220, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p224, s => put 9 ((r (.GPR 9#5) s) + 64#64) s
  | .p228, s => put 10 (0#64) s
  | .p232, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p236, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p240, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p244, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p248, s => next (write_mem_bytes 16 (r (.GPR 0#5) s) ((r (.GPR 8#5) s) ++ (r (.GPR 8#5) s)) s)
  | .p252, s => next (write_mem_bytes 4 ((r (.GPR 0#5) s) + 72#64) ((r (.GPR 9#5) s).setWidth 32) s)
  | .p256, s => next (write_mem_bytes 32 ((r (.GPR 0#5) s) + 16#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s)
  | .p260, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 48#64) (r (.SFP 0#5) s) s)
  | .p264, s => w .PC (r (.GPR 30#5) s) s
  | .p268, s => put 8 (read_mem_bytes 8 (r (.GPR 4#5) s) s) s
  | .p272, s => put 9 (read_mem_bytes 8 ((r (.GPR 4#5) s) + 16#64) s) s
  | .p276, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (r (.GPR 8#5) s) 0#1).2 (put 10 ((r (.GPR 9#5) s) + (r (.GPR 8#5) s)) s)
  | .p280, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 752#64 else base + 284#64) s
  | .p284, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 8#64 0#1).2 (next s)
  | .p288, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s ≠ 1#1 then base + 752#64 else base + 292#64) s
  | .p292, s => put 11 ((r (.GPR 10#5) s) + 7#64) s
  | .p296, s => put 11 ((r (.GPR 11#5) s) &&& 18446744073709551608#64) s
  | .p300, s => put 10 ((r (.GPR 11#5) s) - (r (.GPR 10#5) s)) s
  | .p304, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 9#5) s) 0#1).2 (put 9 ((r (.GPR 10#5) s) + (r (.GPR 9#5) s)) s)
  | .p308, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 752#64 else base + 312#64) s
  | .p312, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 17#64 0#1).2 (next s)
  | .p316, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s ≠ 1#1 then base + 752#64 else base + 320#64) s
  | .p320, s => put 11 (read_mem_bytes 8 ((r (.GPR 4#5) s) + 8#64) s) s
  | .p324, s => put 10 ((r (.GPR 9#5) s) + 16#64) s
  | .p328, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (~~~(r (.GPR 11#5) s)) 1#1).2 (next s)
  | .p332, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s ≠ 1#1 then base + 752#64 else base + 336#64) s
  | .p336, s => put 20 ((r (.GPR 8#5) s) + (r (.GPR 9#5) s)) s
  | .p340, s => put 19 2#64 s
  | .p344, s => next (write_mem_bytes 8 ((r (.GPR 4#5) s) + 16#64) (r (.GPR 10#5) s) s)
  | .p348, s => next (write_mem_bytes 16 (r (.GPR 20#5) s) ((r (.GPR 23#5) s) ++ (r (.GPR 24#5) s)) s)
  | .p352, s => put 8 ((read_mem_bytes 4 (r (.GPR 1#5) s) s).setWidth 64) s
  | .p356, s => write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~1#32) 1#1).2 (next s)
  | .p360, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 540#64 else base + 364#64) s
  | .p364, s => next (w (.GPR 21#5) (read_mem_bytes 8 (((r (.GPR 1#5) s) + 8#64) + 8#64) s) (w (.GPR 22#5) (read_mem_bytes 8 ((r (.GPR 1#5) s) + 8#64) s) s))
  | .p368, s => put 27 ((r (.GPR 0#5) s)) s
  | .p372, s => put 0 ((r (.GPR 20#5) s)) s
  | .p376, s => put 1 ((r (.GPR 19#5) s)) s
  | .p380, s => put 28 ((r (.GPR 2#5) s)) s
  | .p384, s => put 29 ((r (.GPR 3#5) s)) s
  | .p388, s => put 2 ((r (.GPR 22#5) s)) s
  | .p392, s => put 3 ((r (.GPR 21#5) s)) s
  | .p396, s => w .PC (base + compareOffset) (w (.GPR 30#5) (base + 400#64) s)
  | .p400, s => put 3 ((r (.GPR 29#5) s)) s
  | .p404, s => put 2 ((r (.GPR 28#5) s)) s
  | .p408, s => put 8 ((((r (.GPR 0#5) s).setWidth 8).signExtend 32).setWidth 64) s
  | .p412, s => put 0 ((r (.GPR 27#5) s)) s
  | .p416, s => write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~1#32) 1#1).2 (next s)
  | .p420, s => w .PC (if r (.FLAG .N) s ≠ r (.FLAG .V) s then base + 540#64 else base + 424#64) s
  | .p424, s => put 8 1#64 s
  | .p428, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p432, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p436, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p440, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p444, s => put 9 ((r (.GPR 9#5) s) + 56#64) s
  | .p448, s => put 10 (0#64) s
  | .p452, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p456, s => put 10 (0#64) s
  | .p460, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p464, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p468, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p472, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p476, s => put 9 2#64 s
  | .p480, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p484, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p488, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p492, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p496, s => put 9 ((r (.GPR 9#5) s) + 8#64) s
  | .p500, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 8#5) s) s)
  | .p504, s => put 10 (0#64) s
  | .p508, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p512, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p516, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p520, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p524, s => put 8 48#64 s
  | .p528, s => put 10 40#64 s
  | .p532, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 24#64) ((r (.GPR 21#5) s) ++ (r (.GPR 22#5) s)) s)
  | .p536, s => w .PC (base + 916#64) s
  | .p540, s => write_pstate (AddWithCarry ((r (.GPR 26#5) s).setWidth 32) (~~~7#32) 1#1).2 (next s)
  | .p544, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 556#64 else base + 548#64) s
  | .p548, s => put 8 0#64 s
  | .p552, s => w .PC (base + 560#64) s
  | .p556, s => put 8 1#64 s
  | .p560, s => put 9 (if r (.FLAG .Z) s = 1#1 then (r (.GPR 25#5) s) else (r (.GPR 3#5) s)) s
  | .p564, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (r (.GPR 25#5) s) 0#1).2 (put 8 ((r (.GPR 8#5) s) + (r (.GPR 25#5) s)) s)
  | .p568, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 580#64 else base + 572#64) s
  | .p572, s => put 10 0#64 s
  | .p576, s => w .PC (base + 584#64) s
  | .p580, s => put 10 1#64 s
  | .p584, s => put 8 ((r (.GPR 8#5) s) ^^^ (r (.GPR 9#5) s)) s
  | .p588, s => put 8 ((r (.GPR 8#5) s) ||| (r (.GPR 10#5) s)) s
  | .p592, s => w .PC (if (r (.GPR 8#5) s) ≠ 0#64 then base + 684#64 else base + 596#64) s
  | .p596, s => put 10 3#64 s
  | .p600, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 32#64) ((r (.GPR 9#5) s) ++ (r (.GPR 2#5) s)) s)
  | .p604, s => next (write_mem_bytes 1 ((r (.GPR 0#5) s) + 16#64) ((r (.GPR 10#5) s).setWidth 8) s)
  | .p608, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 48#64) ((r (.GPR 23#5) s) ++ (r (.GPR 24#5) s)) s)
  | .p612, s => w .PC (base + 980#64) s
  | .p616, s => put 9 18#64 s
  | .p620, s => next (w (.SFP 0#5) 0#128 s)
  | .p624, s => put 8 1#64 s
  | .p628, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p632, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p636, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p640, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p644, s => put 9 ((r (.GPR 9#5) s) + 64#64) s
  | .p648, s => put 10 (0#64) s
  | .p652, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p656, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p660, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p664, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p668, s => next (write_mem_bytes 8 ((r (.GPR 0#5) s) + 8#64) (r (.GPR 8#5) s) s)
  | .p672, s => next (write_mem_bytes 32 ((r (.GPR 0#5) s) + 16#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s)
  | .p676, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 48#64) (r (.SFP 0#5) s) s)
  | .p680, s => w .PC (base + 976#64) s
  | .p684, s => next (w (.SFP 0#5) 0#128 s)
  | .p688, s => put 8 1#64 s
  | .p692, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p696, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p700, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p704, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p708, s => put 9 ((r (.GPR 9#5) s) + 64#64) s
  | .p712, s => put 10 (0#64) s
  | .p716, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p720, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p724, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p728, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p732, s => next (write_mem_bytes 8 ((r (.GPR 0#5) s) + 8#64) (r (.GPR 8#5) s) s)
  | .p736, s => put 9 32770#64 s
  | .p740, s => next (write_mem_bytes 32 ((r (.GPR 0#5) s) + 16#64) ((r (.SFP 0#5) s) ++ (r (.SFP 0#5) s)) s)
  | .p744, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 48#64) (r (.SFP 0#5) s) s)
  | .p748, s => w .PC (base + 976#64) s
  | .p752, s => put 19 (0#64) s
  | .p756, s => put 9 32768#64 s
  | .p760, s => put 8 16#64 s
  | .p764, s => put 20 1#64 s
  | .p768, s => put 10 8#64 s
  | .p772, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p776, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p780, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p784, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p788, s => put 9 ((r (.GPR 9#5) s) + 56#64) s
  | .p792, s => put 10 (0#64) s
  | .p796, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p800, s => put 10 (0#64) s
  | .p804, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p808, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p812, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p816, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p820, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p824, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p828, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p832, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p836, s => put 9 ((r (.GPR 9#5) s) + 40#64) s
  | .p840, s => put 10 (0#64) s
  | .p844, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p848, s => put 10 (0#64) s
  | .p852, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p856, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p860, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p864, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p868, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p872, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p876, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p880, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p884, s => put 9 ((r (.GPR 9#5) s) + 24#64) s
  | .p888, s => put 10 (0#64) s
  | .p892, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p896, s => put 10 (0#64) s
  | .p900, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p904, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p908, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p912, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p916, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p920, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p924, s => put 9 ((r (.GPR 10#5) s)) s
  | .p928, s => put 9 ((r (.GPR 0#5) s) + (r (.GPR 9#5) s)) s
  | .p932, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 20#5) s) s)
  | .p936, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p940, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p944, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p948, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p952, s => put 9 ((r (.GPR 8#5) s)) s
  | .p956, s => put 9 ((r (.GPR 0#5) s) + (r (.GPR 9#5) s)) s
  | .p960, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 19#5) s) s)
  | .p964, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p968, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p972, s => put 8 1#64 s
  | .p976, s => next (write_mem_bytes 4 ((r (.GPR 0#5) s) + 72#64) ((r (.GPR 9#5) s).setWidth 32) s)
  | .p980, s => next (w (.GPR 19#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 80#64) + 8#64) s) (w (.GPR 20#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 80#64) s) s))
  | .p984, s => next (w (.GPR 21#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 64#64) + 8#64) s) (w (.GPR 22#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 64#64) s) s))
  | .p988, s => next (w (.GPR 23#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 48#64) + 8#64) s) (w (.GPR 24#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 48#64) s) s))
  | .p992, s => next (w (.GPR 25#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 32#64) + 8#64) s) (w (.GPR 26#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 32#64) s) s))
  | .p996, s => next (w (.GPR 27#5) (read_mem_bytes 8 (((r (.GPR 31#5) s) + 16#64) + 8#64) s) (w (.GPR 28#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 16#64) s) s))
  | .p1000, s => w (.GPR 31#5) ((r (.GPR 31#5) s) + 96#64) (next (w (.GPR 30#5) (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) (w (.GPR 29#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s)))
  | .p1004, s => next (write_mem_bytes 8 (r (.GPR 0#5) s) (r (.GPR 8#5) s) s)
  | .p1008, s => w .PC (r (.GPR 30#5) s) s

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

def Op.stackDelta : Op → BitVec 64
  | .p4 => -96#64
  | .p1000 => 96#64
  | .p32 | .p80 | .p208 | .p428 | .p480 | .p628 | .p692 |
    .p772 | .p820 | .p868 | .p916 | .p944 => -16#64
  | .p56 | .p128 | .p244 | .p472 | .p520 | .p664 | .p728 |
    .p816 | .p864 | .p912 | .p940 | .p968 => 16#64
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

end SszArm.Delimited

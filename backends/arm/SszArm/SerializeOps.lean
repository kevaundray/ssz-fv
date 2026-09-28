import SszArm.SerializeImpl
import SszArm.EmitUintWidthOps

namespace SszArm.Serialize

/-- Every original instruction of the private serialize wrapper, including both calls. -/
inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36
  | p40 | p44 | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76
  | p80 | p84 | p88 | p92 | p96 | p100 | p104 | p108 | p112 | p116
  | p120 | p124 | p128 | p132 | p136 | p140 | p144 | p148 | p152 | p156
  | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188 | p192 | p196
  | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236
  | p240 | p244 | p248 | p252 | p256 | p260 | p264 | p268 | p272 | p276
  | p280 | p284 | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316
  | p320 | p324 | p328 | p332 | p336 | p340 | p344 | p348 | p352 | p356
  | p360 | p364 | p368 | p372 | p376 | p380 | p384 | p388 | p392 | p396
  | p400 | p404 | p408 | p412 | p416 | p420 | p424 | p428 | p432 | p436
  | p440 | p444 | p448 | p452 | p456 | p460 | p464 | p468 | p472 | p476
  | p480 | p484 | p488 | p492 | p496 | p500 | p504 | p508 | p512 | p516
  | p520 | p524 | p528 | p532 | p536 | p540 | p544 | p548 | p552 | p556
  | p560 | p564 | p568 | p572 | p576 | p580 | p584 | p588 | p592 | p596
  | p600 | p604 | p608 | p612 | p616 | p620 | p624 | p628 | p632 | p636
  | p640 | p644 | p648 | p652 | p656 | p660 | p664 | p668 | p672 | p676
  | p680 | p684 | p688
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10243ff#32)
  | .p4 => (4, 0xa9065ffe#32)
  | .p8 => (8, 0xa90757f6#32)
  | .p12 => (12, 0xa9084ff4#32)
  | .p16 => (16, 0xaa0403f7#32)
  | .p20 => (20, 0xaa0303f4#32)
  | .p24 => (24, 0xaa0003f3#32)
  | .p28 => (28, 0x910063e0#32)
  | .p32 => (32, 0xaa0503e3#32)
  | .p36 => (36, 0x52800024#32)
  | .p40 => (40, 0xaa0203f5#32)
  | .p44 => (44, 0xaa0103f6#32)
  | .p48 => (48, 0x97ffdabd#32)
  | .p52 => (52, 0xa941b3eb#32)
  | .p56 => (56, 0xb9405be9#32)
  | .p60 => (60, 0xa94297e8#32)
  | .p64 => (64, 0xf9401fea#32)
  | .p68 => (68, 0xa900b3eb#32)
  | .p72 => (72, 0x34000209#32)
  | .p76 => (76, 0xa94433eb#32)
  | .p80 => (80, 0xf9402bed#32)
  | .p84 => (84, 0xa9011668#32)
  | .p88 => (88, 0xb9405fe8#32)
  | .p92 => (92, 0xf9001e6d#32)
  | .p96 => (96, 0xa902b26b#32)
  | .p100 => (100, 0xa940b3eb#32)
  | .p104 => (104, 0xf900126a#32)
  | .p108 => (108, 0x29082269#32)
  | .p112 => (112, 0xa900326b#32)
  | .p116 => (116, 0xa9484ff4#32)
  | .p120 => (120, 0xa94757f6#32)
  | .p124 => (124, 0xa9465ffe#32)
  | .p128 => (128, 0x910243ff#32)
  | .p132 => (132, 0xd65f03c0#32)
  | .p136 => (136, 0xa940afe9#32)
  | .p140 => (140, 0xa90297e8#32)
  | .p144 => (144, 0xf9001fea#32)
  | .p148 => (148, 0xa901afe9#32)
  | .p152 => (152, 0xb4000888#32)
  | .p156 => (156, 0xd10004aa#32)
  | .p160 => (160, 0xb100055f#32)
  | .p164 => (164, 0x540007e0#32)
  | .p168 => (168, 0xd10043ff#32)
  | .p172 => (172, 0xf90003e9#32)
  | .p176 => (176, 0xaa0a03e9#32)
  | .p180 => (180, 0xd37df129#32)
  | .p184 => (184, 0x8b090109#32)
  | .p188 => (188, 0xf940012b#32)
  | .p192 => (192, 0xf94003e9#32)
  | .p196 => (196, 0x910043ff#32)
  | .p200 => (200, 0xaa0a03e9#32)
  | .p204 => (204, 0xd100054a#32)
  | .p208 => (208, 0xb4fffe8b#32)
  | .p212 => (212, 0x91000529#32)
  | .p216 => (216, 0xf100053f#32)
  | .p220 => (220, 0x54000640#32)
  | .p224 => (224, 0x52800028#32)
  | .p228 => (228, 0xd10043ff#32)
  | .p232 => (232, 0xf90003e9#32)
  | .p236 => (236, 0xf90007ea#32)
  | .p240 => (240, 0x91000269#32)
  | .p244 => (244, 0x9100c129#32)
  | .p248 => (248, 0xd280000a#32)
  | .p252 => (252, 0xf900012a#32)
  | .p256 => (256, 0xd280000a#32)
  | .p260 => (260, 0xf900052a#32)
  | .p264 => (264, 0xf94007ea#32)
  | .p268 => (268, 0xf94003e9#32)
  | .p272 => (272, 0x910043ff#32)
  | .p276 => (276, 0xd10043ff#32)
  | .p280 => (280, 0xf90003e9#32)
  | .p284 => (284, 0xf90007ea#32)
  | .p288 => (288, 0x91000269#32)
  | .p292 => (292, 0x91008129#32)
  | .p296 => (296, 0xd280000a#32)
  | .p300 => (300, 0xf900012a#32)
  | .p304 => (304, 0xd280000a#32)
  | .p308 => (308, 0xf900052a#32)
  | .p312 => (312, 0xf94007ea#32)
  | .p316 => (316, 0xf94003e9#32)
  | .p320 => (320, 0x910043ff#32)
  | .p324 => (324, 0xd10043ff#32)
  | .p328 => (328, 0xf90003e9#32)
  | .p332 => (332, 0xf90007ea#32)
  | .p336 => (336, 0x91000269#32)
  | .p340 => (340, 0x91004129#32)
  | .p344 => (344, 0xd280000a#32)
  | .p348 => (348, 0xf900012a#32)
  | .p352 => (352, 0xd280000a#32)
  | .p356 => (356, 0xf900052a#32)
  | .p360 => (360, 0xf94007ea#32)
  | .p364 => (364, 0xf94003e9#32)
  | .p368 => (368, 0x910043ff#32)
  | .p372 => (372, 0xd10043ff#32)
  | .p376 => (376, 0xf90003e9#32)
  | .p380 => (380, 0xf90007ea#32)
  | .p384 => (384, 0x91000269#32)
  | .p388 => (388, 0xf9000128#32)
  | .p392 => (392, 0xd280000a#32)
  | .p396 => (396, 0xf900052a#32)
  | .p400 => (400, 0xf94007ea#32)
  | .p404 => (404, 0xf94003e9#32)
  | .p408 => (408, 0x910043ff#32)
  | .p412 => (412, 0x14000034#32)
  | .p416 => (416, 0xb4000745#32)
  | .p420 => (420, 0xf9400105#32)
  | .p424 => (424, 0xeb0502ff#32)
  | .p428 => (428, 0x540006e2#32)
  | .p432 => (432, 0x52800028#32)
  | .p436 => (436, 0xd10043ff#32)
  | .p440 => (440, 0xf90003e9#32)
  | .p444 => (444, 0xf90007ea#32)
  | .p448 => (448, 0x91000269#32)
  | .p452 => (452, 0x91004129#32)
  | .p456 => (456, 0xd280000a#32)
  | .p460 => (460, 0xf900012a#32)
  | .p464 => (464, 0xd280000a#32)
  | .p468 => (468, 0xf900052a#32)
  | .p472 => (472, 0xf94007ea#32)
  | .p476 => (476, 0xf94003e9#32)
  | .p480 => (480, 0x910043ff#32)
  | .p484 => (484, 0xd10043ff#32)
  | .p488 => (488, 0xf90003e9#32)
  | .p492 => (492, 0xf90007ea#32)
  | .p496 => (496, 0x91000269#32)
  | .p500 => (500, 0xf9000128#32)
  | .p504 => (504, 0xd280000a#32)
  | .p508 => (508, 0xf900052a#32)
  | .p512 => (512, 0xf94007ea#32)
  | .p516 => (516, 0xf94003e9#32)
  | .p520 => (520, 0x910043ff#32)
  | .p524 => (524, 0xd10043ff#32)
  | .p528 => (528, 0xf90003e9#32)
  | .p532 => (532, 0xf90007ea#32)
  | .p536 => (536, 0x91000269#32)
  | .p540 => (540, 0x91008129#32)
  | .p544 => (544, 0xd280000a#32)
  | .p548 => (548, 0xf900012a#32)
  | .p552 => (552, 0xd280000a#32)
  | .p556 => (556, 0xf900052a#32)
  | .p560 => (560, 0xf94007ea#32)
  | .p564 => (564, 0xf94003e9#32)
  | .p568 => (568, 0x910043ff#32)
  | .p572 => (572, 0xd10043ff#32)
  | .p576 => (576, 0xf90003e9#32)
  | .p580 => (580, 0xf90007ea#32)
  | .p584 => (584, 0x91000269#32)
  | .p588 => (588, 0x9100c129#32)
  | .p592 => (592, 0xd280000a#32)
  | .p596 => (596, 0xf900012a#32)
  | .p600 => (600, 0xd280000a#32)
  | .p604 => (604, 0xf900052a#32)
  | .p608 => (608, 0xf94007ea#32)
  | .p612 => (612, 0xf94003e9#32)
  | .p616 => (616, 0x910043ff#32)
  | .p620 => (620, 0x52900028#32)
  | .p624 => (624, 0xb9004268#32)
  | .p628 => (628, 0xa9484ff4#32)
  | .p632 => (632, 0xa94757f6#32)
  | .p636 => (636, 0xa9465ffe#32)
  | .p640 => (640, 0x910243ff#32)
  | .p644 => (644, 0xd65f03c0#32)
  | .p648 => (648, 0x910063e3#32)
  | .p652 => (652, 0xaa1303e0#32)
  | .p656 => (656, 0xaa1603e1#32)
  | .p660 => (660, 0xaa1503e2#32)
  | .p664 => (664, 0xaa1403e4#32)
  | .p668 => (668, 0x97ffde62#32)
  | .p672 => (672, 0xa9484ff4#32)
  | .p676 => (676, 0xa94757f6#32)
  | .p680 => (680, 0xa9465ffe#32)
  | .p684 => (684, 0x910243ff#32)
  | .p688 => (688, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

/-- Single original-instruction effects. Loads observe the state at that instruction,
including reloads after the wrapper's actual stores. -/
def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 144#64) s
  | .p4, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 96#64)
      (r (.GPR 23#5) s ++ r (.GPR 30#5) s) s)
  | .p8, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 112#64)
      (r (.GPR 21#5) s ++ r (.GPR 22#5) s) s)
  | .p12, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 128#64)
      (r (.GPR 19#5) s ++ r (.GPR 20#5) s) s)
  | .p16, s => put 23 (r (.GPR 4#5) s) s
  | .p20, s => put 20 (r (.GPR 3#5) s) s
  | .p24, s => put 19 (r (.GPR 0#5) s) s
  | .p28, s => put 0 (r (.GPR 31#5) s + 24#64) s
  | .p32, s => put 3 (r (.GPR 5#5) s) s
  | .p36, s => put 4 (1#64) s
  | .p40, s => put 21 (r (.GPR 2#5) s) s
  | .p44, s => put 22 (r (.GPR 1#5) s) s
  | .p48, s => w .PC (base + measureOffset) (w (.GPR 30#5) (base + 52#64) s)
  | .p52, s => w (.GPR 12#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 32#64) s)
      (put 11 (read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s) s)
  | .p56, s => put 9 ((read_mem_bytes 4 (r (.GPR 31#5) s + 88#64) s).setWidth 64) s
  | .p60, s => w (.GPR 5#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 48#64) s)
      (put 8 (read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s) s)
  | .p64, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 56#64) s) s
  | .p68, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 8#64)
      (r (.GPR 12#5) s ++ r (.GPR 11#5) s) s)
  | .p72, s => w .PC (if (r (.GPR 9#5) s).setWidth 32 = 0#32 then base + 136#64 else base + 76#64) s
  | .p76, s => w (.GPR 12#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 72#64) s)
      (put 11 (read_mem_bytes 8 (r (.GPR 31#5) s + 64#64) s) s)
  | .p80, s => put 13 (read_mem_bytes 8 (r (.GPR 31#5) s + 80#64) s) s
  | .p84, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 16#64)
      (r (.GPR 5#5) s ++ r (.GPR 8#5) s) s)
  | .p88, s => put 8 ((read_mem_bytes 4 (r (.GPR 31#5) s + 92#64) s).setWidth 64) s
  | .p92, s => next (write_mem_bytes 8 (r (.GPR 19#5) s + 56#64) (r (.GPR 13#5) s) s)
  | .p96, s => next (write_mem_bytes 16 (r (.GPR 19#5) s + 40#64)
      (r (.GPR 12#5) s ++ r (.GPR 11#5) s) s)
  | .p100, s => w (.GPR 12#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s)
      (put 11 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)
  | .p104, s => next (write_mem_bytes 8 (r (.GPR 19#5) s + 32#64) (r (.GPR 10#5) s) s)
  | .p108, s => next (write_mem_bytes 8 (r (.GPR 19#5) s + 64#64)
      ((r (.GPR 8#5) s).setWidth 32 ++ (r (.GPR 9#5) s).setWidth 32) s)
  | .p112, s => next (write_mem_bytes 16 (r (.GPR 19#5) s)
      (r (.GPR 12#5) s ++ r (.GPR 11#5) s) s)
  | .p116, s => w (.GPR 19#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 136#64) s)
      (put 20 (read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s) s)
  | .p120, s => w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s)
      (put 22 (read_mem_bytes 8 (r (.GPR 31#5) s + 112#64) s) s)
  | .p124, s => w (.GPR 23#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s)
      (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s) s)
  | .p128, s => put 31 (r (.GPR 31#5) s + 144#64) s
  | .p132, s => w .PC (r (.GPR 30#5) s) s
  | .p136, s => w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s)
      (put 9 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s)
  | .p140, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 40#64)
      (r (.GPR 5#5) s ++ r (.GPR 8#5) s) s)
  | .p144, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 56#64) (r (.GPR 10#5) s) s)
  | .p148, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 24#64)
      (r (.GPR 11#5) s ++ r (.GPR 9#5) s) s)
  | .p152, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 424#64 else base + 156#64) s
  | .p156, s => put 10 (r (.GPR 5#5) s - 1#64) s
  | .p160, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 1#64 0#1).2 (next s)
  | .p164, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 416#64 else base + 168#64) s
  | .p168, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p172, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p176, s => put 9 (r (.GPR 10#5) s) s
  | .p180, s => put 9 (r (.GPR 9#5) s <<< 3) s
  | .p184, s => put 9 (r (.GPR 8#5) s + r (.GPR 9#5) s) s
  | .p188, s => put 11 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p192, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p196, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p200, s => put 9 (r (.GPR 10#5) s) s
  | .p204, s => put 10 (r (.GPR 10#5) s - 1#64) s
  | .p208, s => w .PC (if r (.GPR 11#5) s = 0#64 then base + 160#64 else base + 212#64) s
  | .p212, s => put 9 (r (.GPR 9#5) s + 1#64) s
  | .p216, s => Emit.Dispatch.compare64 (r (.GPR 9#5) s) (1#64) s
  | .p220, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 420#64 else base + 224#64) s
  | .p224, s => put 8 (1#64) s
  | .p228, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p232, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p236, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p240, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p244, s => put 9 (r (.GPR 9#5) s + 48#64) s
  | .p248, s => put 10 (0#64) s
  | .p252, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p256, s => put 10 (0#64) s
  | .p260, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p264, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p268, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p272, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p276, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p280, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p284, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p288, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p292, s => put 9 (r (.GPR 9#5) s + 32#64) s
  | .p296, s => put 10 (0#64) s
  | .p300, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p304, s => put 10 (0#64) s
  | .p308, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p312, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p316, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p320, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p324, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p328, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p332, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p336, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p340, s => put 9 (r (.GPR 9#5) s + 16#64) s
  | .p344, s => put 10 (0#64) s
  | .p348, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p352, s => put 10 (0#64) s
  | .p356, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p360, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p364, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p368, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p372, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p376, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p380, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p384, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p388, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 8#5) s) s)
  | .p392, s => put 10 (0#64) s
  | .p396, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p400, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p404, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p408, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p412, s => w .PC (base + 620#64) s
  | .p416, s => w .PC (if r (.GPR 5#5) s = 0#64 then base + 648#64 else base + 420#64) s
  | .p420, s => put 5 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s
  | .p424, s => Emit.Dispatch.compare64 (r (.GPR 23#5) s) (r (.GPR 5#5) s) s
  | .p428, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 648#64 else base + 432#64) s
  | .p432, s => put 8 (1#64) s
  | .p436, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p440, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p444, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p448, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p452, s => put 9 (r (.GPR 9#5) s + 16#64) s
  | .p456, s => put 10 (0#64) s
  | .p460, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p464, s => put 10 (0#64) s
  | .p468, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p472, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p476, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p480, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p484, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p488, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p492, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p496, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p500, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 8#5) s) s)
  | .p504, s => put 10 (0#64) s
  | .p508, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p512, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p516, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p520, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p524, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p528, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p532, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p536, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p540, s => put 9 (r (.GPR 9#5) s + 32#64) s
  | .p544, s => put 10 (0#64) s
  | .p548, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p552, s => put 10 (0#64) s
  | .p556, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p560, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p564, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p568, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p572, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p576, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p580, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p584, s => put 9 (r (.GPR 19#5) s + 0#64) s
  | .p588, s => put 9 (r (.GPR 9#5) s + 48#64) s
  | .p592, s => put 10 (0#64) s
  | .p596, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p600, s => put 10 (0#64) s
  | .p604, s => next (write_mem_bytes 8 (r (.GPR 9#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p608, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p612, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p616, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p620, s => put 8 (32769#64) s
  | .p624, s => next (write_mem_bytes 4 (r (.GPR 19#5) s + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)
  | .p628, s => w (.GPR 19#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 136#64) s)
      (put 20 (read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s) s)
  | .p632, s => w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s)
      (put 22 (read_mem_bytes 8 (r (.GPR 31#5) s + 112#64) s) s)
  | .p636, s => w (.GPR 23#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s)
      (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s) s)
  | .p640, s => put 31 (r (.GPR 31#5) s + 144#64) s
  | .p644, s => w .PC (r (.GPR 30#5) s) s
  | .p648, s => put 3 (r (.GPR 31#5) s + 24#64) s
  | .p652, s => put 0 (r (.GPR 19#5) s) s
  | .p656, s => put 1 (r (.GPR 22#5) s) s
  | .p660, s => put 2 (r (.GPR 21#5) s) s
  | .p664, s => put 4 (r (.GPR 20#5) s) s
  | .p668, s => w .PC (base + emitOffset) (w (.GPR 30#5) (base + 672#64) s)
  | .p672, s => w (.GPR 19#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 136#64) s)
      (put 20 (read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s) s)
  | .p676, s => w (.GPR 21#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s)
      (put 22 (read_mem_bytes 8 (r (.GPR 31#5) s + 112#64) s) s)
  | .p680, s => w (.GPR 23#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) s)
      (put 30 (read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s) s)
  | .p684, s => put 31 (r (.GPR 31#5) s + 144#64) s
  | .p688, s => w .PC (r (.GPR 30#5) s) s

end SszArm.Serialize

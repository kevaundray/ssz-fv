import SszArm.NatCompareImpl

namespace SszArm.NatCompare

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136 | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188 | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236 | p240 | p244 | p248 | p252 | p256 | p260 | p264 | p268 | p272 | p276 | p280 | p284 | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316 | p320 | p324 | p328 | p332 | p336 | p340 | p344 | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380 | p384 | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p416 | p420 | p424 | p428 | p432 | p436 | p440 | p444 | p448 | p452 | p456 | p460 | p464 | p468 | p472 | p476 | p480 | p484 | p488 | p492 | p496 | p500 | p504 | p508 | p512 | p516 | p520 | p524 | p528 | p532 | p536 | p540 | p544 | p548 | p552 | p556 | p560 | p564 | p568 | p572 | p576 | p580 | p584 | p588 | p592 | p596 | p600 | p604 | p608 | p612 | p616 | p620 | p624 | p628 | p632 | p636 | p640 | p644 | p648 | p652 | p656 | p660 | p664 | p668 | p672 | p676 | p680 | p684 | p688 | p692 | p696 | p700 | p704 | p708
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb4000560#32)
  | .p4 => (4, 0xd1002008#32)
  | .p8 => (8, 0xaa0103e9#32)
  | .p12 => (12, 0xb40001a9#32)
  | .p16 => (16, 0xd10043ff#32)
  | .p20 => (20, 0xf90003ea#32)
  | .p24 => (24, 0xaa0903ea#32)
  | .p28 => (28, 0xd37df14a#32)
  | .p32 => (32, 0x8b0a010a#32)
  | .p36 => (36, 0xf940014b#32)
  | .p40 => (40, 0xf94003ea#32)
  | .p44 => (44, 0x910043ff#32)
  | .p48 => (48, 0xd100052a#32)
  | .p52 => (52, 0xaa0a03e9#32)
  | .p56 => (56, 0xb4fffeab#32)
  | .p60 => (60, 0x91000549#32)
  | .p64 => (64, 0xb4000422#32)
  | .p68 => (68, 0xd1002048#32)
  | .p72 => (72, 0xaa0303ea#32)
  | .p76 => (76, 0xb40005ea#32)
  | .p80 => (80, 0xd10043ff#32)
  | .p84 => (84, 0xf90003e9#32)
  | .p88 => (88, 0xaa0a03e9#32)
  | .p92 => (92, 0xd37df129#32)
  | .p96 => (96, 0x8b090109#32)
  | .p100 => (100, 0xf940012c#32)
  | .p104 => (104, 0xf94003e9#32)
  | .p108 => (108, 0x910043ff#32)
  | .p112 => (112, 0xd100054b#32)
  | .p116 => (116, 0xaa0b03ea#32)
  | .p120 => (120, 0xb4fffeac#32)
  | .p124 => (124, 0x91000568#32)
  | .p128 => (128, 0xeb08013f#32)
  | .p132 => (132, 0x54000068#32)
  | .p136 => (136, 0x52800008#32)
  | .p140 => (140, 0x14000002#32)
  | .p144 => (144, 0x52800028#32)
  | .p148 => (148, 0x54000062#32)
  | .p152 => (152, 0x2a3f03e8#32)
  | .p156 => (156, 0x14000002#32)
  | .p160 => (160, 0x2a0803e8#32)
  | .p164 => (164, 0x540002e1#32)
  | .p168 => (168, 0x14000022#32)
  | .p172 => (172, 0xf100003f#32)
  | .p176 => (176, 0x54000061#32)
  | .p180 => (180, 0x52800009#32)
  | .p184 => (184, 0x14000002#32)
  | .p188 => (188, 0x52800029#32)
  | .p192 => (192, 0xb5fffc22#32)
  | .p196 => (196, 0xf100007f#32)
  | .p200 => (200, 0x54000061#32)
  | .p204 => (204, 0x52800008#32)
  | .p208 => (208, 0x14000002#32)
  | .p212 => (212, 0x52800028#32)
  | .p216 => (216, 0xeb08013f#32)
  | .p220 => (220, 0x54000068#32)
  | .p224 => (224, 0x52800008#32)
  | .p228 => (228, 0x14000002#32)
  | .p232 => (232, 0x52800028#32)
  | .p236 => (236, 0x54000062#32)
  | .p240 => (240, 0x2a3f03e8#32)
  | .p244 => (244, 0x14000002#32)
  | .p248 => (248, 0x2a0803e8#32)
  | .p252 => (252, 0x540001a0#32)
  | .p256 => (256, 0x2a0803e0#32)
  | .p260 => (260, 0xd65f03c0#32)
  | .p264 => (264, 0xeb1f013f#32)
  | .p268 => (268, 0x54000068#32)
  | .p272 => (272, 0x52800008#32)
  | .p276 => (276, 0x14000002#32)
  | .p280 => (280, 0x52800028#32)
  | .p284 => (284, 0x54000062#32)
  | .p288 => (288, 0x2a3f03e8#32)
  | .p292 => (292, 0x14000002#32)
  | .p296 => (296, 0x2a0803e8#32)
  | .p300 => (300, 0x54fffea1#32)
  | .p304 => (304, 0xb40008e0#32)
  | .p308 => (308, 0xd1000529#32)
  | .p312 => (312, 0xb50001a2#32)
  | .p316 => (316, 0x14000030#32)
  | .p320 => (320, 0xd10043ff#32)
  | .p324 => (324, 0xf90003eb#32)
  | .p328 => (328, 0xaa0903eb#32)
  | .p332 => (332, 0xd37df16b#32)
  | .p336 => (336, 0x8b0b004b#32)
  | .p340 => (340, 0xf940016a#32)
  | .p344 => (344, 0xf94003eb#32)
  | .p348 => (348, 0x910043ff#32)
  | .p352 => (352, 0xeb0a011f#32)
  | .p356 => (356, 0xd1000529#32)
  | .p360 => (360, 0x540005e1#32)
  | .p364 => (364, 0xb100053f#32)
  | .p368 => (368, 0x54000a60#32)
  | .p372 => (372, 0xeb01013f#32)
  | .p376 => (376, 0x54000182#32)
  | .p380 => (380, 0xd10043ff#32)
  | .p384 => (384, 0xf90003ea#32)
  | .p388 => (388, 0xaa0903ea#32)
  | .p392 => (392, 0xd37df14a#32)
  | .p396 => (396, 0x8b0a000a#32)
  | .p400 => (400, 0xf9400148#32)
  | .p404 => (404, 0xf94003ea#32)
  | .p408 => (408, 0x910043ff#32)
  | .p412 => (412, 0xeb03013f#32)
  | .p416 => (416, 0x54fffd03#32)
  | .p420 => (420, 0x14000004#32)
  | .p424 => (424, 0xaa1f03e8#32)
  | .p428 => (428, 0xeb03013f#32)
  | .p432 => (432, 0x54fffc83#32)
  | .p436 => (436, 0xaa1f03ea#32)
  | .p440 => (440, 0xeb1f011f#32)
  | .p444 => (444, 0xd1000529#32)
  | .p448 => (448, 0x54fffd60#32)
  | .p452 => (452, 0x14000018#32)
  | .p456 => (456, 0xd10043ff#32)
  | .p460 => (460, 0xf90003ea#32)
  | .p464 => (464, 0xaa0903ea#32)
  | .p468 => (468, 0xd37df14a#32)
  | .p472 => (472, 0x8b0a000a#32)
  | .p476 => (476, 0xf9400148#32)
  | .p480 => (480, 0xf94003ea#32)
  | .p484 => (484, 0x910043ff#32)
  | .p488 => (488, 0xf100013f#32)
  | .p492 => (492, 0xd1000529#32)
  | .p496 => (496, 0x9a9f006a#32)
  | .p500 => (500, 0xeb0a011f#32)
  | .p504 => (504, 0x54000161#32)
  | .p508 => (508, 0xb100053f#32)
  | .p512 => (512, 0x540005e0#32)
  | .p516 => (516, 0xeb01013f#32)
  | .p520 => (520, 0x54fffe03#32)
  | .p524 => (524, 0xaa1f03e8#32)
  | .p528 => (528, 0xf100013f#32)
  | .p532 => (532, 0xd1000529#32)
  | .p536 => (536, 0x9a9f006a#32)
  | .p540 => (540, 0xeb0a03ff#32)
  | .p544 => (544, 0x54fffee0#32)
  | .p548 => (548, 0xeb0a011f#32)
  | .p552 => (552, 0x54000068#32)
  | .p556 => (556, 0x52800008#32)
  | .p560 => (560, 0x14000002#32)
  | .p564 => (564, 0x52800028#32)
  | .p568 => (568, 0x54000062#32)
  | .p572 => (572, 0x2a3f03e0#32)
  | .p576 => (576, 0x14000002#32)
  | .p580 => (580, 0x2a0803e0#32)
  | .p584 => (584, 0xd65f03c0#32)
  | .p588 => (588, 0xb4000362#32)
  | .p592 => (592, 0xd1000529#32)
  | .p596 => (596, 0x14000004#32)
  | .p600 => (600, 0xeb0a011f#32)
  | .p604 => (604, 0xd1000529#32)
  | .p608 => (608, 0x54fffe21#32)
  | .p612 => (612, 0xb100053f#32)
  | .p616 => (616, 0x540002a0#32)
  | .p620 => (620, 0xf100013f#32)
  | .p624 => (624, 0xaa1f03ea#32)
  | .p628 => (628, 0x9a9f0028#32)
  | .p632 => (632, 0xeb03013f#32)
  | .p636 => (636, 0x54fffee2#32)
  | .p640 => (640, 0xd10043ff#32)
  | .p644 => (644, 0xf90003eb#32)
  | .p648 => (648, 0xaa0903eb#32)
  | .p652 => (652, 0xd37df16b#32)
  | .p656 => (656, 0x8b0b004b#32)
  | .p660 => (660, 0xf940016a#32)
  | .p664 => (664, 0xf94003eb#32)
  | .p668 => (668, 0x910043ff#32)
  | .p672 => (672, 0x17ffffee#32)
  | .p676 => (676, 0xf1000529#32)
  | .p680 => (680, 0x9a9f0028#32)
  | .p684 => (684, 0x9a9f006a#32)
  | .p688 => (688, 0xeb0a011f#32)
  | .p692 => (692, 0x54fffb81#32)
  | .p696 => (696, 0xb5ffff69#32)
  | .p700 => (700, 0x2a1f03e8#32)
  | .p704 => (704, 0x2a0803e0#32)
  | .p708 => (708, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if r (.GPR 0#5) s = 0#64 then base + 172#64 else base + 4#64) s
  | .p4, s => put 8 ((r (.GPR 0#5) s) - (8#64)) s
  | .p8, s => put 9 (r (.GPR 1#5) s) s
  | .p12, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 64#64 else base + 16#64) s
  | .p16, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p20, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p24, s => put 10 (r (.GPR 9#5) s) s
  | .p28, s => put 10 ((r (.GPR 10#5) s) <<< 3) s
  | .p32, s => put 10 ((r (.GPR 8#5) s) + (r (.GPR 10#5) s)) s
  | .p36, s => put 11 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p40, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p44, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p48, s => put 10 ((r (.GPR 9#5) s) - (1#64)) s
  | .p52, s => put 9 (r (.GPR 10#5) s) s
  | .p56, s => w .PC (if r (.GPR 11#5) s = 0#64 then base + 12#64 else base + 60#64) s
  | .p60, s => put 9 ((r (.GPR 10#5) s) + (1#64)) s
  | .p64, s => w .PC (if r (.GPR 2#5) s = 0#64 then base + 196#64 else base + 68#64) s
  | .p68, s => put 8 ((r (.GPR 2#5) s) - (8#64)) s
  | .p72, s => put 10 (r (.GPR 3#5) s) s
  | .p76, s => w .PC (if r (.GPR 10#5) s = 0#64 then base + 264#64 else base + 80#64) s
  | .p80, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p84, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p88, s => put 9 (r (.GPR 10#5) s) s
  | .p92, s => put 9 ((r (.GPR 9#5) s) <<< 3) s
  | .p96, s => put 9 ((r (.GPR 8#5) s) + (r (.GPR 9#5) s)) s
  | .p100, s => put 12 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p104, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p108, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p112, s => put 11 ((r (.GPR 10#5) s) - (1#64)) s
  | .p116, s => put 10 (r (.GPR 11#5) s) s
  | .p120, s => w .PC (if r (.GPR 12#5) s = 0#64 then base + 76#64 else base + 124#64) s
  | .p124, s => put 8 ((r (.GPR 11#5) s) + (1#64)) s
  | .p128, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 8#5) s) s
  | .p132, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 144#64 else base + 136#64) s
  | .p136, s => put 8 (0#64) s
  | .p140, s => w .PC (base + 148#64) s
  | .p144, s => put 8 (1#64) s
  | .p148, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 160#64 else base + 152#64) s
  | .p152, s => put 8 (4294967295#64) s
  | .p156, s => w .PC (base + 164#64) s
  | .p160, s => put 8 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p164, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 256#64 else base + 168#64) s
  | .p168, s => w .PC (base + 304#64) s
  | .p172, s => Udivti3.compare (r (.GPR 1#5) s) (0#64) s
  | .p176, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 188#64 else base + 180#64) s
  | .p180, s => put 9 (0#64) s
  | .p184, s => w .PC (base + 192#64) s
  | .p188, s => put 9 (1#64) s
  | .p192, s => w .PC (if r (.GPR 2#5) s ≠ 0#64 then base + 68#64 else base + 196#64) s
  | .p196, s => Udivti3.compare (r (.GPR 3#5) s) (0#64) s
  | .p200, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 212#64 else base + 204#64) s
  | .p204, s => put 8 (0#64) s
  | .p208, s => w .PC (base + 216#64) s
  | .p212, s => put 8 (1#64) s
  | .p216, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 8#5) s) s
  | .p220, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 232#64 else base + 224#64) s
  | .p224, s => put 8 (0#64) s
  | .p228, s => w .PC (base + 236#64) s
  | .p232, s => put 8 (1#64) s
  | .p236, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 248#64 else base + 240#64) s
  | .p240, s => put 8 (4294967295#64) s
  | .p244, s => w .PC (base + 252#64) s
  | .p248, s => put 8 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p252, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 304#64 else base + 256#64) s
  | .p256, s => put 0 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p260, s => w .PC (r (.GPR 30#5) s) s
  | .p264, s => Udivti3.compare (r (.GPR 9#5) s) (0#64) s
  | .p268, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 280#64 else base + 272#64) s
  | .p272, s => put 8 (0#64) s
  | .p276, s => w .PC (base + 284#64) s
  | .p280, s => put 8 (1#64) s
  | .p284, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 296#64 else base + 288#64) s
  | .p288, s => put 8 (4294967295#64) s
  | .p292, s => w .PC (base + 300#64) s
  | .p296, s => put 8 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p300, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 256#64 else base + 304#64) s
  | .p304, s => w .PC (if r (.GPR 0#5) s = 0#64 then base + 588#64 else base + 308#64) s
  | .p308, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p312, s => w .PC (if r (.GPR 2#5) s ≠ 0#64 then base + 364#64 else base + 316#64) s
  | .p316, s => w .PC (base + 508#64) s
  | .p320, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p324, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p328, s => put 11 (r (.GPR 9#5) s) s
  | .p332, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p336, s => put 11 ((r (.GPR 2#5) s) + (r (.GPR 11#5) s)) s
  | .p340, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p344, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p348, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p352, s => Udivti3.compare (r (.GPR 8#5) s) (r (.GPR 10#5) s) s
  | .p356, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p360, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 548#64 else base + 364#64) s
  | .p364, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (1#64) 0#1).2 (next s)
  | .p368, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 700#64 else base + 372#64) s
  | .p372, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 1#5) s) s
  | .p376, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 424#64 else base + 380#64) s
  | .p380, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p384, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p388, s => put 10 (r (.GPR 9#5) s) s
  | .p392, s => put 10 ((r (.GPR 10#5) s) <<< 3) s
  | .p396, s => put 10 ((r (.GPR 0#5) s) + (r (.GPR 10#5) s)) s
  | .p400, s => put 8 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p404, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p408, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p412, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 3#5) s) s
  | .p416, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 320#64 else base + 420#64) s
  | .p420, s => w .PC (base + 436#64) s
  | .p424, s => put 8 (0#64) s
  | .p428, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 3#5) s) s
  | .p432, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 320#64 else base + 436#64) s
  | .p436, s => put 10 (0#64) s
  | .p440, s => Udivti3.compare (r (.GPR 8#5) s) (0#64) s
  | .p444, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p448, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 364#64 else base + 452#64) s
  | .p452, s => w .PC (base + 548#64) s
  | .p456, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p460, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p464, s => put 10 (r (.GPR 9#5) s) s
  | .p468, s => put 10 ((r (.GPR 10#5) s) <<< 3) s
  | .p472, s => put 10 ((r (.GPR 0#5) s) + (r (.GPR 10#5) s)) s
  | .p476, s => put 8 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p480, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p484, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p488, s => Udivti3.compare (r (.GPR 9#5) s) (0#64) s
  | .p492, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p496, s => put 10 (if r (.FLAG .Z) s = 1#1 then r (.GPR 3#5) s else 0#64) s
  | .p500, s => Udivti3.compare (r (.GPR 8#5) s) (r (.GPR 10#5) s) s
  | .p504, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 548#64 else base + 508#64) s
  | .p508, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (1#64) 0#1).2 (next s)
  | .p512, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 700#64 else base + 516#64) s
  | .p516, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 1#5) s) s
  | .p520, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 456#64 else base + 524#64) s
  | .p524, s => put 8 (0#64) s
  | .p528, s => Udivti3.compare (r (.GPR 9#5) s) (0#64) s
  | .p532, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p536, s => put 10 (if r (.FLAG .Z) s = 1#1 then r (.GPR 3#5) s else 0#64) s
  | .p540, s => Udivti3.compare (0#64) (r (.GPR 10#5) s) s
  | .p544, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 508#64 else base + 548#64) s
  | .p548, s => Udivti3.compare (r (.GPR 8#5) s) (r (.GPR 10#5) s) s
  | .p552, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 564#64 else base + 556#64) s
  | .p556, s => put 8 (0#64) s
  | .p560, s => w .PC (base + 568#64) s
  | .p564, s => put 8 (1#64) s
  | .p568, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 580#64 else base + 572#64) s
  | .p572, s => put 0 (4294967295#64) s
  | .p576, s => w .PC (base + 584#64) s
  | .p580, s => put 0 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p584, s => w .PC (r (.GPR 30#5) s) s
  | .p588, s => w .PC (if r (.GPR 2#5) s = 0#64 then base + 696#64 else base + 592#64) s
  | .p592, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p596, s => w .PC (base + 612#64) s
  | .p600, s => Udivti3.compare (r (.GPR 8#5) s) (r (.GPR 10#5) s) s
  | .p604, s => put 9 ((r (.GPR 9#5) s) - (1#64)) s
  | .p608, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 548#64 else base + 612#64) s
  | .p612, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) (1#64) 0#1).2 (next s)
  | .p616, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 700#64 else base + 620#64) s
  | .p620, s => Udivti3.compare (r (.GPR 9#5) s) (0#64) s
  | .p624, s => put 10 (0#64) s
  | .p628, s => put 8 (if r (.FLAG .Z) s = 1#1 then r (.GPR 1#5) s else 0#64) s
  | .p632, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 3#5) s) s
  | .p636, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 600#64 else base + 640#64) s
  | .p640, s => put 31 ((r (.GPR 31#5) s) - (16#64)) s
  | .p644, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p648, s => put 11 (r (.GPR 9#5) s) s
  | .p652, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p656, s => put 11 ((r (.GPR 2#5) s) + (r (.GPR 11#5) s)) s
  | .p660, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p664, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p668, s => put 31 ((r (.GPR 31#5) s) + (16#64)) s
  | .p672, s => w .PC (base + 600#64) s
  | .p676, s => w (.GPR 9#5) (r (.GPR 9#5) s - 1#64)
      (write_pstate (AddWithCarry (r (.GPR 9#5) s) (~~~(1#64)) 1#1).2 (next s))
  | .p680, s => put 8 (if r (.FLAG .Z) s = 1#1 then r (.GPR 1#5) s else 0#64) s
  | .p684, s => put 10 (if r (.FLAG .Z) s = 1#1 then r (.GPR 3#5) s else 0#64) s
  | .p688, s => Udivti3.compare (r (.GPR 8#5) s) (r (.GPR 10#5) s) s
  | .p692, s => w .PC (if r (.FLAG .Z) s ≠ 1#1 then base + 548#64 else base + 696#64) s
  | .p696, s => w .PC (if r (.GPR 9#5) s ≠ 0#64 then base + 676#64 else base + 700#64) s
  | .p700, s => put 8 (0#64) s
  | .p704, s => put 0 (((r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p708, s => w .PC (r (.GPR 30#5) s) s

/-- Each contract is checked against this function's fetched raw word. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf := hc op.row hm
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, ha, hp, BitVec.add_assoc, apply_ite, uint_lsl3_mask,
       uint_and_ones, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

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

end SszArm.NatCompare

import SszArm.NatFromU128Impl
import SszArm.NatCompareExec

namespace SszArm.NatFromU128

open UintCodec

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92
  | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136 | p140
  | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188
  | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236
  | p240 | p244 | p248 | p252 | p256 | p260 | p264 | p268 | p272 | p276 | p280 | p284
  | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316 | p320 | p324 | p328 | p332
  | p336 | p340 | p344 | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380
  | p384 | p388 | p392 | p396 | p400 | p404 | p408 | p412 | p416
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb50002c3#32)
  | .p4 => (4, 0xd10043ff#32)
  | .p8 => (8, 0xf90003e9#32)
  | .p12 => (12, 0xf90007ea#32)
  | .p16 => (16, 0x91000009#32)
  | .p20 => (20, 0xd280000a#32)
  | .p24 => (24, 0xf900012a#32)
  | .p28 => (28, 0xf9000522#32)
  | .p32 => (32, 0xf94007ea#32)
  | .p36 => (36, 0xf94003e9#32)
  | .p40 => (40, 0x910043ff#32)
  | .p44 => (44, 0xd10043ff#32)
  | .p48 => (48, 0xf90003e9#32)
  | .p52 => (52, 0xf90007ea#32)
  | .p56 => (56, 0x91000009#32)
  | .p60 => (60, 0x91010129#32)
  | .p64 => (64, 0x5280000a#32)
  | .p68 => (68, 0xb900012a#32)
  | .p72 => (72, 0xf94007ea#32)
  | .p76 => (76, 0xf94003e9#32)
  | .p80 => (80, 0x910043ff#32)
  | .p84 => (84, 0xd65f03c0#32)
  | .p88 => (88, 0xf9400089#32)
  | .p92 => (92, 0xf9400888#32)
  | .p96 => (96, 0xab09010a#32)
  | .p100 => (100, 0x540003c2#32)
  | .p104 => (104, 0xb100215f#32)
  | .p108 => (108, 0x54000388#32)
  | .p112 => (112, 0x91001d4b#32)
  | .p116 => (116, 0x927df16b#32)
  | .p120 => (120, 0xcb0a016a#32)
  | .p124 => (124, 0xab08014a#32)
  | .p128 => (128, 0x540002e2#32)
  | .p132 => (132, 0xb100455f#32)
  | .p136 => (136, 0x540002a8#32)
  | .p140 => (140, 0xf9400488#32)
  | .p144 => (144, 0x9100414b#32)
  | .p148 => (148, 0xeb08017f#32)
  | .p152 => (152, 0x54000228#32)
  | .p156 => (156, 0x8b0a0129#32)
  | .p160 => (160, 0xf900088b#32)
  | .p164 => (164, 0xa9000d22#32)
  | .p168 => (168, 0x52800042#32)
  | .p172 => (172, 0xa9000809#32)
  | .p176 => (176, 0xd10043ff#32)
  | .p180 => (180, 0xf90003e9#32)
  | .p184 => (184, 0xf90007ea#32)
  | .p188 => (188, 0x91000009#32)
  | .p192 => (192, 0x91010129#32)
  | .p196 => (196, 0x5280000a#32)
  | .p200 => (200, 0xb900012a#32)
  | .p204 => (204, 0xf94007ea#32)
  | .p208 => (208, 0xf94003e9#32)
  | .p212 => (212, 0x910043ff#32)
  | .p216 => (216, 0xd65f03c0#32)
  | .p220 => (220, 0x52900008#32)
  | .p224 => (224, 0x52800029#32)
  | .p228 => (228, 0xd10043ff#32)
  | .p232 => (232, 0xf90003e9#32)
  | .p236 => (236, 0xf90007ea#32)
  | .p240 => (240, 0x91000009#32)
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
  | .p288 => (288, 0x91000009#32)
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
  | .p336 => (336, 0x91000009#32)
  | .p340 => (340, 0x91004129#32)
  | .p344 => (344, 0xd280000a#32)
  | .p348 => (348, 0xf900012a#32)
  | .p352 => (352, 0xd280000a#32)
  | .p356 => (356, 0xf900052a#32)
  | .p360 => (360, 0xf94007ea#32)
  | .p364 => (364, 0xf94003e9#32)
  | .p368 => (368, 0x910043ff#32)
  | .p372 => (372, 0xd10043ff#32)
  | .p376 => (376, 0xf90003ea#32)
  | .p380 => (380, 0xf90007eb#32)
  | .p384 => (384, 0x9100000a#32)
  | .p388 => (388, 0xf9000149#32)
  | .p392 => (392, 0xd280000b#32)
  | .p396 => (396, 0xf900054b#32)
  | .p400 => (400, 0xf94007eb#32)
  | .p404 => (404, 0xf94003ea#32)
  | .p408 => (408, 0x910043ff#32)
  | .p412 => (412, 0xb9004008#32)
  | .p416 => (416, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if (r (.GPR 3#5) s) ≠ 0#64 then base + 88#64 else base + 4#64) s
  | .p4, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p8, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p12, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p16, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p20, s => put 10 0#64 s
  | .p24, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p28, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 2#5) s) s)
  | .p32, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p36, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p40, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p44, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p48, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p52, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p56, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p60, s => put 9 ((r (.GPR 9#5) s) + 64#64) s
  | .p64, s => put 10 0#64 s
  | .p68, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p72, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p76, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p80, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p84, s => w .PC (r (.GPR 30#5) s) s
  | .p88, s => put 9 (read_mem_bytes 8 (r (.GPR 4#5) s) s) s
  | .p92, s => put 8 (read_mem_bytes 8 ((r (.GPR 4#5) s) + 16#64) s) s
  | .p96, s => write_pstate (AddWithCarry (r (.GPR 8#5) s) (r (.GPR 9#5) s) 0#1).2 (put 10 ((r (.GPR 8#5) s) + (r (.GPR 9#5) s)) s)
  | .p100, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 220#64 else base + 104#64) s
  | .p104, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 8#64 0#1).2 (next s)
  | .p108, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 220#64 else base + 112#64) s
  | .p112, s => put 11 ((r (.GPR 10#5) s) + 7#64) s
  | .p116, s => put 11 ((r (.GPR 11#5) s) &&& 18446744073709551608#64) s
  | .p120, s => put 10 ((r (.GPR 11#5) s) - (r (.GPR 10#5) s)) s
  | .p124, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 8#5) s) 0#1).2 (put 10 ((r (.GPR 10#5) s) + (r (.GPR 8#5) s)) s)
  | .p128, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 220#64 else base + 132#64) s
  | .p132, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 17#64 0#1).2 (next s)
  | .p136, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 220#64 else base + 140#64) s
  | .p140, s => put 8 (read_mem_bytes 8 ((r (.GPR 4#5) s) + 8#64) s) s
  | .p144, s => put 11 ((r (.GPR 10#5) s) + 16#64) s
  | .p148, s => Udivti3.compare (r (.GPR 11#5) s) (r (.GPR 8#5) s) s
  | .p152, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 220#64 else base + 156#64) s
  | .p156, s => put 9 ((r (.GPR 9#5) s) + (r (.GPR 10#5) s)) s
  | .p160, s => next (write_mem_bytes 8 ((r (.GPR 4#5) s) + 16#64) (r (.GPR 11#5) s) s)
  | .p164, s => next (write_mem_bytes 16 (r (.GPR 9#5) s) ((r (.GPR 3#5) s) ++ (r (.GPR 2#5) s)) s)
  | .p168, s => put 2 2#64 s
  | .p172, s => next (write_mem_bytes 16 (r (.GPR 0#5) s) ((r (.GPR 2#5) s) ++ (r (.GPR 9#5) s)) s)
  | .p176, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p180, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p184, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p188, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p192, s => put 9 ((r (.GPR 9#5) s) + 64#64) s
  | .p196, s => put 10 0#64 s
  | .p200, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p204, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p208, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p212, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p216, s => w .PC (r (.GPR 30#5) s) s
  | .p220, s => put 8 32768#64 s
  | .p224, s => put 9 1#64 s
  | .p228, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p232, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p236, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p240, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p244, s => put 9 ((r (.GPR 9#5) s) + 48#64) s
  | .p248, s => put 10 0#64 s
  | .p252, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p256, s => put 10 0#64 s
  | .p260, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p264, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p268, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p272, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p276, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p280, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p284, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p288, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p292, s => put 9 ((r (.GPR 9#5) s) + 32#64) s
  | .p296, s => put 10 0#64 s
  | .p300, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p304, s => put 10 0#64 s
  | .p308, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p312, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p316, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p320, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p324, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p328, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p332, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p336, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p340, s => put 9 ((r (.GPR 9#5) s) + 16#64) s
  | .p344, s => put 10 0#64 s
  | .p348, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p352, s => put 10 0#64 s
  | .p356, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p360, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p364, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p368, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p372, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p376, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p380, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p384, s => put 10 ((r (.GPR 0#5) s) + 0#64) s
  | .p388, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 9#5) s) s)
  | .p392, s => put 11 0#64 s
  | .p396, s => next (write_mem_bytes 8 ((r (.GPR 10#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p400, s => put 11 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p404, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p408, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p412, s => next (write_mem_bytes 4 ((r (.GPR 0#5) s) + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)
  | .p416, s => w .PC (r (.GPR 30#5) s) s

end SszArm.NatFromU128

import SszArm.DelimitedBranchExec
import SszArm.DelimitedIntegerExec
import SszArm.DelimitedLoadExec
import SszArm.DelimitedStoreExec
import SszArm.DelimitedSimdExec

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Dispatches to the already checked, small opcode-family contracts. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  cases op
  case p0 =>
    have hf : s.program.find? (read_pc s) = some 0xb4000623#32 := by
      rw [hp]; exact hc (0, 0xb4000623#32) (by decide)
    simpa only [Op.effect] using word_p0 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p4 =>
    have hf : s.program.find? (read_pc s) = some 0xa9ba7bfd#32 := by
      rw [hp]; exact hc (4, 0xa9ba7bfd#32) (by decide)
    simpa only [Op.effect] using word_p4 s base he ha hf
  case p8 =>
    have hf : s.program.find? (read_pc s) = some 0xa9016ffc#32 := by
      rw [hp]; exact hc (8, 0xa9016ffc#32) (by decide)
    simpa only [Op.effect] using word_p8 s base he ha hf
  case p12 =>
    have hf : s.program.find? (read_pc s) = some 0xa90267fa#32 := by
      rw [hp]; exact hc (12, 0xa90267fa#32) (by decide)
    simpa only [Op.effect] using word_p12 s base he ha hf
  case p16 =>
    have hf : s.program.find? (read_pc s) = some 0xa9035ff8#32 := by
      rw [hp]; exact hc (16, 0xa9035ff8#32) (by decide)
    simpa only [Op.effect] using word_p16 s base he ha hf
  case p20 =>
    have hf : s.program.find? (read_pc s) = some 0xa90457f6#32 := by
      rw [hp]; exact hc (20, 0xa90457f6#32) (by decide)
    simpa only [Op.effect] using word_p20 s base he ha hf
  case p24 =>
    have hf : s.program.find? (read_pc s) = some 0xa9054ff4#32 := by
      rw [hp]; exact hc (24, 0xa9054ff4#32) (by decide)
    simpa only [Op.effect] using word_p24 s base he ha hf
  case p28 =>
    have hf : s.program.find? (read_pc s) = some 0xd1000479#32 := by
      rw [hp]; exact hc (28, 0xd1000479#32) (by decide)
    simpa only [Op.effect] using word_p28 s base he ha hf
  case p32 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (32, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p36 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (36, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p40 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1903e9#32 := by
      rw [hp]; exact hc (40, 0xaa1903e9#32) (by decide)
    simpa only [Op.effect] using word_p40 s base he ha hf
  case p44 =>
    have hf : s.program.find? (read_pc s) = some 0x8b090049#32 := by
      rw [hp]; exact hc (44, 0x8b090049#32) (by decide)
    simpa only [Op.effect] using word_p44 s base he ha hf
  case p48 =>
    have hf : s.program.find? (read_pc s) = some 0x39400128#32 := by
      rw [hp]; exact hc (48, 0x39400128#32) (by decide)
    simpa only [Op.effect] using word_p48 s base he ha hf
  case p52 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (52, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p56 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (56, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p60 =>
    have hf : s.program.find? (read_pc s) = some 0x340003e8#32 := by
      rw [hp]; exact hc (60, 0x340003e8#32) (by decide)
    simpa only [Op.effect] using word_p60 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p64 =>
    have hf : s.program.find? (read_pc s) = some 0x53081d08#32 := by
      rw [hp]; exact hc (64, 0x53081d08#32) (by decide)
    simpa only [Op.effect] using word_p64 s base he ha hf
  case p68 =>
    have hf : s.program.find? (read_pc s) = some 0xd2800029#32 := by
      rw [hp]; exact hc (68, 0xd2800029#32) (by decide)
    simpa only [Op.effect] using word_p68 s base he ha hf
  case p72 =>
    have hf : s.program.find? (read_pc s) = some 0xd37dff37#32 := by
      rw [hp]; exact hc (72, 0xd37dff37#32) (by decide)
    simpa only [Op.effect] using word_p72 s base he ha hf
  case p76 =>
    have hf : s.program.find? (read_pc s) = some 0xf2e40009#32 := by
      rw [hp]; exact hc (76, 0xf2e40009#32) (by decide)
    simpa only [Op.effect] using word_p76 s base he ha hf
  case p80 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (80, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p84 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (84, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p88 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (88, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p92 =>
    have hf : s.program.find? (read_pc s) = some 0x2a0803e9#32 := by
      rw [hp]; exact hc (92, 0x2a0803e9#32) (by decide)
    simpa only [Op.effect] using word_p92 s base he ha hf
  case p96 =>
    have hf : s.program.find? (read_pc s) = some 0x5280040a#32 := by
      rw [hp]; exact hc (96, 0x5280040a#32) (by decide)
    simpa only [Op.effect] using word_p96 s base he ha hf
  case p100 =>
    have hf : s.program.find? (read_pc s) = some 0x34000089#32 := by
      rw [hp]; exact hc (100, 0x34000089#32) (by decide)
    simpa only [Op.effect] using word_p100 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p104 =>
    have hf : s.program.find? (read_pc s) = some 0x5100054a#32 := by
      rw [hp]; exact hc (104, 0x5100054a#32) (by decide)
    simpa only [Op.effect] using word_p104 s base he ha hf
  case p108 =>
    have hf : s.program.find? (read_pc s) = some 0x53017d29#32 := by
      rw [hp]; exact hc (108, 0x53017d29#32) (by decide)
    simpa only [Op.effect] using word_p108 s base he ha hf
  case p112 =>
    have hf : s.program.find? (read_pc s) = some 0x35ffffc9#32 := by
      rw [hp]; exact hc (112, 0x35ffffc9#32) (by decide)
    simpa only [Op.effect] using word_p112 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p116 =>
    have hf : s.program.find? (read_pc s) = some 0x2a0a03fa#32 := by
      rw [hp]; exact hc (116, 0x2a0a03fa#32) (by decide)
    simpa only [Op.effect] using word_p116 s base he ha hf
  case p120 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (120, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p124 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (124, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p128 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (128, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p132 =>
    have hf : s.program.find? (read_pc s) = some 0xeb09007f#32 := by
      rw [hp]; exact hc (132, 0xeb09007f#32) (by decide)
    simpa only [Op.effect] using word_p132 s base he ha hf
  case p136 =>
    have hf : s.program.find? (read_pc s) = some 0x52000b48#32 := by
      rw [hp]; exact hc (136, 0x52000b48#32) (by decide)
    simpa only [Op.effect] using word_p136 s base he ha hf
  case p140 =>
    have hf : s.program.find? (read_pc s) = some 0xaa190d18#32 := by
      rw [hp]; exact hc (140, 0xaa190d18#32) (by decide)
    simpa only [Op.effect] using word_p140 s base he ha hf
  case p144 =>
    have hf : s.program.find? (read_pc s) = some 0x540003e2#32 := by
      rw [hp]; exact hc (144, 0x540003e2#32) (by decide)
    simpa only [Op.effect] using word_p144 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p148 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1f03f4#32 := by
      rw [hp]; exact hc (148, 0xaa1f03f4#32) (by decide)
    simpa only [Op.effect] using word_p148 s base he ha hf
  case p152 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1803f3#32 := by
      rw [hp]; exact hc (152, 0xaa1803f3#32) (by decide)
    simpa only [Op.effect] using word_p152 s base he ha hf
  case p156 =>
    have hf : s.program.find? (read_pc s) = some 0xb9400028#32 := by
      rw [hp]; exact hc (156, 0xb9400028#32) (by decide)
    simpa only [Op.effect] using word_p156 s base he ha hf
  case p160 =>
    have hf : s.program.find? (read_pc s) = some 0x7100051f#32 := by
      rw [hp]; exact hc (160, 0x7100051f#32) (by decide)
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p164 =>
    have hf : s.program.find? (read_pc s) = some 0x54000640#32 := by
      rw [hp]; exact hc (164, 0x54000640#32) (by decide)
    simpa only [Op.effect] using word_p164 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p168 =>
    have hf : s.program.find? (read_pc s) = some 0x1400005d#32 := by
      rw [hp]; exact hc (168, 0x1400005d#32) (by decide)
    simpa only [Op.effect] using word_p168 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p172 =>
    have hf : s.program.find? (read_pc s) = some 0x38401448#32 := by
      rw [hp]; exact hc (172, 0x38401448#32) (by decide)
    simpa only [Op.effect] using word_p172 s base he ha hf
  case p176 =>
    have hf : s.program.find? (read_pc s) = some 0xd1000463#32 := by
      rw [hp]; exact hc (176, 0xd1000463#32) (by decide)
    simpa only [Op.effect] using word_p176 s base he ha hf
  case p180 =>
    have hf : s.program.find? (read_pc s) = some 0x35000da8#32 := by
      rw [hp]; exact hc (180, 0x35000da8#32) (by decide)
    simpa only [Op.effect] using word_p180 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p184 =>
    have hf : s.program.find? (read_pc s) = some 0xb5ffffa3#32 := by
      rw [hp]; exact hc (184, 0xb5ffffa3#32) (by decide)
    simpa only [Op.effect] using word_p184 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p188 =>
    have hf : s.program.find? (read_pc s) = some 0x52800229#32 := by
      rw [hp]; exact hc (188, 0x52800229#32) (by decide)
    simpa only [Op.effect] using word_p188 s base he ha hf
  case p192 =>
    have hf : s.program.find? (read_pc s) = some 0x1400006b#32 := by
      rw [hp]; exact hc (192, 0x1400006b#32) (by decide)
    simpa only [Op.effect] using word_p192 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p196 =>
    have hf : s.program.find? (read_pc s) = some 0x6f00e400#32 := by
      rw [hp]; exact hc (196, 0x6f00e400#32) (by decide)
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p200 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (200, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p204 =>
    have hf : s.program.find? (read_pc s) = some 0x52800209#32 := by
      rw [hp]; exact hc (204, 0x52800209#32) (by decide)
    simpa only [Op.effect] using word_p204 s base he ha hf
  case p208 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (208, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p212 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (212, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p216 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (216, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p220 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (220, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p224 =>
    have hf : s.program.find? (read_pc s) = some 0x91010129#32 := by
      rw [hp]; exact hc (224, 0x91010129#32) (by decide)
    simpa only [Op.effect] using word_p224 s base he ha hf
  case p228 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (228, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p232 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (232, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p236 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (236, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p240 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (240, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p244 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (244, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p248 =>
    have hf : s.program.find? (read_pc s) = some 0xa9002008#32 := by
      rw [hp]; exact hc (248, 0xa9002008#32) (by decide)
    simpa only [Op.effect] using word_p248 s base he ha hf
  case p252 =>
    have hf : s.program.find? (read_pc s) = some 0xb9004809#32 := by
      rw [hp]; exact hc (252, 0xb9004809#32) (by decide)
    simpa only [Op.effect] using word_p252 s base he ha hf
  case p256 =>
    have hf : s.program.find? (read_pc s) = some 0xad008000#32 := by
      rw [hp]; exact hc (256, 0xad008000#32) (by decide)
    simpa only [Op.effect] using word_p256 s base he ha hf
  case p260 =>
    have hf : s.program.find? (read_pc s) = some 0x3d800c00#32 := by
      rw [hp]; exact hc (260, 0x3d800c00#32) (by decide)
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p264 =>
    have hf : s.program.find? (read_pc s) = some 0xd65f03c0#32 := by
      rw [hp]; exact hc (264, 0xd65f03c0#32) (by decide)
    simpa only [Op.effect] using word_p264 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p268 =>
    have hf : s.program.find? (read_pc s) = some 0xf9400088#32 := by
      rw [hp]; exact hc (268, 0xf9400088#32) (by decide)
    simpa only [Op.effect] using word_p268 s base he ha hf
  case p272 =>
    have hf : s.program.find? (read_pc s) = some 0xf9400889#32 := by
      rw [hp]; exact hc (272, 0xf9400889#32) (by decide)
    simpa only [Op.effect] using word_p272 s base he ha hf
  case p276 =>
    have hf : s.program.find? (read_pc s) = some 0xab08012a#32 := by
      rw [hp]; exact hc (276, 0xab08012a#32) (by decide)
    simpa only [Op.effect] using word_p276 s base he ha hf
  case p280 =>
    have hf : s.program.find? (read_pc s) = some 0x54000ec2#32 := by
      rw [hp]; exact hc (280, 0x54000ec2#32) (by decide)
    simpa only [Op.effect] using word_p280 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p284 =>
    have hf : s.program.find? (read_pc s) = some 0xb100215f#32 := by
      rw [hp]; exact hc (284, 0xb100215f#32) (by decide)
    simpa only [Op.effect] using word_p284 s base he ha hf
  case p288 =>
    have hf : s.program.find? (read_pc s) = some 0x54000e88#32 := by
      rw [hp]; exact hc (288, 0x54000e88#32) (by decide)
    simpa only [Op.effect] using word_p288 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p292 =>
    have hf : s.program.find? (read_pc s) = some 0x91001d4b#32 := by
      rw [hp]; exact hc (292, 0x91001d4b#32) (by decide)
    simpa only [Op.effect] using word_p292 s base he ha hf
  case p296 =>
    have hf : s.program.find? (read_pc s) = some 0x927df16b#32 := by
      rw [hp]; exact hc (296, 0x927df16b#32) (by decide)
    simpa only [Op.effect] using word_p296 s base he ha hf
  case p300 =>
    have hf : s.program.find? (read_pc s) = some 0xcb0a016a#32 := by
      rw [hp]; exact hc (300, 0xcb0a016a#32) (by decide)
    simpa only [Op.effect] using word_p300 s base he ha hf
  case p304 =>
    have hf : s.program.find? (read_pc s) = some 0xab090149#32 := by
      rw [hp]; exact hc (304, 0xab090149#32) (by decide)
    simpa only [Op.effect] using word_p304 s base he ha hf
  case p308 =>
    have hf : s.program.find? (read_pc s) = some 0x54000de2#32 := by
      rw [hp]; exact hc (308, 0x54000de2#32) (by decide)
    simpa only [Op.effect] using word_p308 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p312 =>
    have hf : s.program.find? (read_pc s) = some 0xb100453f#32 := by
      rw [hp]; exact hc (312, 0xb100453f#32) (by decide)
    simpa only [Op.effect] using word_p312 s base he ha hf
  case p316 =>
    have hf : s.program.find? (read_pc s) = some 0x54000da8#32 := by
      rw [hp]; exact hc (316, 0x54000da8#32) (by decide)
    simpa only [Op.effect] using word_p316 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p320 =>
    have hf : s.program.find? (read_pc s) = some 0xf940048b#32 := by
      rw [hp]; exact hc (320, 0xf940048b#32) (by decide)
    simpa only [Op.effect] using word_p320 s base he ha hf
  case p324 =>
    have hf : s.program.find? (read_pc s) = some 0x9100412a#32 := by
      rw [hp]; exact hc (324, 0x9100412a#32) (by decide)
    simpa only [Op.effect] using word_p324 s base he ha hf
  case p328 =>
    have hf : s.program.find? (read_pc s) = some 0xeb0b015f#32 := by
      rw [hp]; exact hc (328, 0xeb0b015f#32) (by decide)
    simpa only [Op.effect] using word_p328 s base he ha hf
  case p332 =>
    have hf : s.program.find? (read_pc s) = some 0x54000d28#32 := by
      rw [hp]; exact hc (332, 0x54000d28#32) (by decide)
    simpa only [Op.effect] using word_p332 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p336 =>
    have hf : s.program.find? (read_pc s) = some 0x8b090114#32 := by
      rw [hp]; exact hc (336, 0x8b090114#32) (by decide)
    simpa only [Op.effect] using word_p336 s base he ha hf
  case p340 =>
    have hf : s.program.find? (read_pc s) = some 0x52800053#32 := by
      rw [hp]; exact hc (340, 0x52800053#32) (by decide)
    simpa only [Op.effect] using word_p340 s base he ha hf
  case p344 =>
    have hf : s.program.find? (read_pc s) = some 0xf900088a#32 := by
      rw [hp]; exact hc (344, 0xf900088a#32) (by decide)
    simpa only [Op.effect] using word_p344 s base he ha hf
  case p348 =>
    have hf : s.program.find? (read_pc s) = some 0xa9005e98#32 := by
      rw [hp]; exact hc (348, 0xa9005e98#32) (by decide)
    simpa only [Op.effect] using word_p348 s base he ha hf
  case p352 =>
    have hf : s.program.find? (read_pc s) = some 0xb9400028#32 := by
      rw [hp]; exact hc (352, 0xb9400028#32) (by decide)
    simpa only [Op.effect] using word_p156 s base he ha hf
  case p356 =>
    have hf : s.program.find? (read_pc s) = some 0x7100051f#32 := by
      rw [hp]; exact hc (356, 0x7100051f#32) (by decide)
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p360 =>
    have hf : s.program.find? (read_pc s) = some 0x540005a1#32 := by
      rw [hp]; exact hc (360, 0x540005a1#32) (by decide)
    simpa only [Op.effect] using word_p360 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p364 =>
    have hf : s.program.find? (read_pc s) = some 0xa940d436#32 := by
      rw [hp]; exact hc (364, 0xa940d436#32) (by decide)
    simpa only [Op.effect] using word_p364 s base he ha hf
  case p368 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0003fb#32 := by
      rw [hp]; exact hc (368, 0xaa0003fb#32) (by decide)
    simpa only [Op.effect] using word_p368 s base he ha hf
  case p372 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1403e0#32 := by
      rw [hp]; exact hc (372, 0xaa1403e0#32) (by decide)
    simpa only [Op.effect] using word_p372 s base he ha hf
  case p376 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1303e1#32 := by
      rw [hp]; exact hc (376, 0xaa1303e1#32) (by decide)
    simpa only [Op.effect] using word_p376 s base he ha hf
  case p380 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0203fc#32 := by
      rw [hp]; exact hc (380, 0xaa0203fc#32) (by decide)
    simpa only [Op.effect] using word_p380 s base he ha hf
  case p384 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0303fd#32 := by
      rw [hp]; exact hc (384, 0xaa0303fd#32) (by decide)
    simpa only [Op.effect] using word_p384 s base he ha hf
  case p388 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1603e2#32 := by
      rw [hp]; exact hc (388, 0xaa1603e2#32) (by decide)
    simpa only [Op.effect] using word_p388 s base he ha hf
  case p392 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1503e3#32 := by
      rw [hp]; exact hc (392, 0xaa1503e3#32) (by decide)
    simpa only [Op.effect] using word_p392 s base he ha hf
  case p396 =>
    have hf : s.program.find? (read_pc s) = some 0x97ffbb50#32 := by
      rw [hp]; exact hc (396, 0x97ffbb50#32) (by decide)
    simpa only [Op.effect] using word_p396 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p400 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1d03e3#32 := by
      rw [hp]; exact hc (400, 0xaa1d03e3#32) (by decide)
    simpa only [Op.effect] using word_p400 s base he ha hf
  case p404 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1c03e2#32 := by
      rw [hp]; exact hc (404, 0xaa1c03e2#32) (by decide)
    simpa only [Op.effect] using word_p404 s base he ha hf
  case p408 =>
    have hf : s.program.find? (read_pc s) = some 0x13001c08#32 := by
      rw [hp]; exact hc (408, 0x13001c08#32) (by decide)
    simpa only [Op.effect] using word_p408 s base he ha hf
  case p412 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1b03e0#32 := by
      rw [hp]; exact hc (412, 0xaa1b03e0#32) (by decide)
    simpa only [Op.effect] using word_p412 s base he ha hf
  case p416 =>
    have hf : s.program.find? (read_pc s) = some 0x7100051f#32 := by
      rw [hp]; exact hc (416, 0x7100051f#32) (by decide)
    simpa only [Op.effect] using word_p160 s base he ha hf
  case p420 =>
    have hf : s.program.find? (read_pc s) = some 0x540003cb#32 := by
      rw [hp]; exact hc (420, 0x540003cb#32) (by decide)
    simpa only [Op.effect] using word_p420 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p424 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (424, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p428 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (428, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p432 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (432, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p436 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (436, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p440 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (440, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p444 =>
    have hf : s.program.find? (read_pc s) = some 0x9100e129#32 := by
      rw [hp]; exact hc (444, 0x9100e129#32) (by decide)
    simpa only [Op.effect] using word_p444 s base he ha hf
  case p448 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (448, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p452 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (452, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p456 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (456, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p460 =>
    have hf : s.program.find? (read_pc s) = some 0xf900052a#32 := by
      rw [hp]; exact hc (460, 0xf900052a#32) (by decide)
    simpa only [Op.effect] using word_p460 s base he ha hf
  case p464 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (464, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p468 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (468, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p472 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (472, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p476 =>
    have hf : s.program.find? (read_pc s) = some 0x52800049#32 := by
      rw [hp]; exact hc (476, 0x52800049#32) (by decide)
    simpa only [Op.effect] using word_p476 s base he ha hf
  case p480 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (480, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p484 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (484, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p488 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (488, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p492 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (492, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p496 =>
    have hf : s.program.find? (read_pc s) = some 0x91002129#32 := by
      rw [hp]; exact hc (496, 0x91002129#32) (by decide)
    simpa only [Op.effect] using word_p496 s base he ha hf
  case p500 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000128#32 := by
      rw [hp]; exact hc (500, 0xf9000128#32) (by decide)
    simpa only [Op.effect] using word_p500 s base he ha hf
  case p504 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (504, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p508 =>
    have hf : s.program.find? (read_pc s) = some 0xf900052a#32 := by
      rw [hp]; exact hc (508, 0xf900052a#32) (by decide)
    simpa only [Op.effect] using word_p460 s base he ha hf
  case p512 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (512, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p516 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (516, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p520 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (520, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p524 =>
    have hf : s.program.find? (read_pc s) = some 0x52800608#32 := by
      rw [hp]; exact hc (524, 0x52800608#32) (by decide)
    simpa only [Op.effect] using word_p524 s base he ha hf
  case p528 =>
    have hf : s.program.find? (read_pc s) = some 0x5280050a#32 := by
      rw [hp]; exact hc (528, 0x5280050a#32) (by decide)
    simpa only [Op.effect] using word_p528 s base he ha hf
  case p532 =>
    have hf : s.program.find? (read_pc s) = some 0xa901d416#32 := by
      rw [hp]; exact hc (532, 0xa901d416#32) (by decide)
    simpa only [Op.effect] using word_p532 s base he ha hf
  case p536 =>
    have hf : s.program.find? (read_pc s) = some 0x1400005f#32 := by
      rw [hp]; exact hc (536, 0x1400005f#32) (by decide)
    simpa only [Op.effect] using word_p536 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p540 =>
    have hf : s.program.find? (read_pc s) = some 0x71001f5f#32 := by
      rw [hp]; exact hc (540, 0x71001f5f#32) (by decide)
    simpa only [Op.effect] using word_p540 s base he ha hf
  case p544 =>
    have hf : s.program.find? (read_pc s) = some 0x54000061#32 := by
      rw [hp]; exact hc (544, 0x54000061#32) (by decide)
    simpa only [Op.effect] using word_p544 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p548 =>
    have hf : s.program.find? (read_pc s) = some 0x52800008#32 := by
      rw [hp]; exact hc (548, 0x52800008#32) (by decide)
    simpa only [Op.effect] using word_p548 s base he ha hf
  case p552 =>
    have hf : s.program.find? (read_pc s) = some 0x14000002#32 := by
      rw [hp]; exact hc (552, 0x14000002#32) (by decide)
    simpa only [Op.effect] using word_p552 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p556 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (556, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p560 =>
    have hf : s.program.find? (read_pc s) = some 0x9a830329#32 := by
      rw [hp]; exact hc (560, 0x9a830329#32) (by decide)
    simpa only [Op.effect] using word_p560 s base he ha hf
  case p564 =>
    have hf : s.program.find? (read_pc s) = some 0xab190108#32 := by
      rw [hp]; exact hc (564, 0xab190108#32) (by decide)
    simpa only [Op.effect] using word_p564 s base he ha hf
  case p568 =>
    have hf : s.program.find? (read_pc s) = some 0x54000062#32 := by
      rw [hp]; exact hc (568, 0x54000062#32) (by decide)
    simpa only [Op.effect] using word_p568 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p572 =>
    have hf : s.program.find? (read_pc s) = some 0x5280000a#32 := by
      rw [hp]; exact hc (572, 0x5280000a#32) (by decide)
    simpa only [Op.effect] using word_p572 s base he ha hf
  case p576 =>
    have hf : s.program.find? (read_pc s) = some 0x14000002#32 := by
      rw [hp]; exact hc (576, 0x14000002#32) (by decide)
    simpa only [Op.effect] using word_p576 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p580 =>
    have hf : s.program.find? (read_pc s) = some 0x5280002a#32 := by
      rw [hp]; exact hc (580, 0x5280002a#32) (by decide)
    simpa only [Op.effect] using word_p580 s base he ha hf
  case p584 =>
    have hf : s.program.find? (read_pc s) = some 0xca090108#32 := by
      rw [hp]; exact hc (584, 0xca090108#32) (by decide)
    simpa only [Op.effect] using word_p584 s base he ha hf
  case p588 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0a0108#32 := by
      rw [hp]; exact hc (588, 0xaa0a0108#32) (by decide)
    simpa only [Op.effect] using word_p588 s base he ha hf
  case p592 =>
    have hf : s.program.find? (read_pc s) = some 0xb50002e8#32 := by
      rw [hp]; exact hc (592, 0xb50002e8#32) (by decide)
    simpa only [Op.effect] using word_p592 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p596 =>
    have hf : s.program.find? (read_pc s) = some 0x5280006a#32 := by
      rw [hp]; exact hc (596, 0x5280006a#32) (by decide)
    simpa only [Op.effect] using word_p596 s base he ha hf
  case p600 =>
    have hf : s.program.find? (read_pc s) = some 0xa9022402#32 := by
      rw [hp]; exact hc (600, 0xa9022402#32) (by decide)
    simpa only [Op.effect] using word_p600 s base he ha hf
  case p604 =>
    have hf : s.program.find? (read_pc s) = some 0x3900400a#32 := by
      rw [hp]; exact hc (604, 0x3900400a#32) (by decide)
    simpa only [Op.effect] using word_p604 s base he ha hf
  case p608 =>
    have hf : s.program.find? (read_pc s) = some 0xa9035c18#32 := by
      rw [hp]; exact hc (608, 0xa9035c18#32) (by decide)
    simpa only [Op.effect] using word_p608 s base he ha hf
  case p612 =>
    have hf : s.program.find? (read_pc s) = some 0x1400005c#32 := by
      rw [hp]; exact hc (612, 0x1400005c#32) (by decide)
    simpa only [Op.effect] using word_p612 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p616 =>
    have hf : s.program.find? (read_pc s) = some 0x52800249#32 := by
      rw [hp]; exact hc (616, 0x52800249#32) (by decide)
    simpa only [Op.effect] using word_p616 s base he ha hf
  case p620 =>
    have hf : s.program.find? (read_pc s) = some 0x6f00e400#32 := by
      rw [hp]; exact hc (620, 0x6f00e400#32) (by decide)
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p624 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (624, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p628 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (628, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p632 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (632, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p636 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (636, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p640 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (640, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p644 =>
    have hf : s.program.find? (read_pc s) = some 0x91010129#32 := by
      rw [hp]; exact hc (644, 0x91010129#32) (by decide)
    simpa only [Op.effect] using word_p224 s base he ha hf
  case p648 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (648, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p652 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (652, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p656 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (656, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p660 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (660, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p664 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (664, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p668 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000408#32 := by
      rw [hp]; exact hc (668, 0xf9000408#32) (by decide)
    simpa only [Op.effect] using word_p668 s base he ha hf
  case p672 =>
    have hf : s.program.find? (read_pc s) = some 0xad008000#32 := by
      rw [hp]; exact hc (672, 0xad008000#32) (by decide)
    simpa only [Op.effect] using word_p256 s base he ha hf
  case p676 =>
    have hf : s.program.find? (read_pc s) = some 0x3d800c00#32 := by
      rw [hp]; exact hc (676, 0x3d800c00#32) (by decide)
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p680 =>
    have hf : s.program.find? (read_pc s) = some 0x1400004a#32 := by
      rw [hp]; exact hc (680, 0x1400004a#32) (by decide)
    simpa only [Op.effect] using word_p680 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p684 =>
    have hf : s.program.find? (read_pc s) = some 0x6f00e400#32 := by
      rw [hp]; exact hc (684, 0x6f00e400#32) (by decide)
    simpa only [Op.effect] using word_p196 s base he ha hf
  case p688 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (688, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p692 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (692, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p696 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (696, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p700 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (700, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p704 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (704, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p708 =>
    have hf : s.program.find? (read_pc s) = some 0x91010129#32 := by
      rw [hp]; exact hc (708, 0x91010129#32) (by decide)
    simpa only [Op.effect] using word_p224 s base he ha hf
  case p712 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (712, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p716 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (716, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p720 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (720, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p724 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (724, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p728 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (728, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p732 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000408#32 := by
      rw [hp]; exact hc (732, 0xf9000408#32) (by decide)
    simpa only [Op.effect] using word_p668 s base he ha hf
  case p736 =>
    have hf : s.program.find? (read_pc s) = some 0x52900049#32 := by
      rw [hp]; exact hc (736, 0x52900049#32) (by decide)
    simpa only [Op.effect] using word_p736 s base he ha hf
  case p740 =>
    have hf : s.program.find? (read_pc s) = some 0xad008000#32 := by
      rw [hp]; exact hc (740, 0xad008000#32) (by decide)
    simpa only [Op.effect] using word_p256 s base he ha hf
  case p744 =>
    have hf : s.program.find? (read_pc s) = some 0x3d800c00#32 := by
      rw [hp]; exact hc (744, 0x3d800c00#32) (by decide)
    simpa only [Op.effect] using word_p260 s base he ha hf
  case p748 =>
    have hf : s.program.find? (read_pc s) = some 0x14000039#32 := by
      rw [hp]; exact hc (748, 0x14000039#32) (by decide)
    simpa only [Op.effect] using word_p748 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)
  case p752 =>
    have hf : s.program.find? (read_pc s) = some 0xaa1f03f3#32 := by
      rw [hp]; exact hc (752, 0xaa1f03f3#32) (by decide)
    simpa only [Op.effect] using word_p752 s base he ha hf
  case p756 =>
    have hf : s.program.find? (read_pc s) = some 0x52900009#32 := by
      rw [hp]; exact hc (756, 0x52900009#32) (by decide)
    simpa only [Op.effect] using word_p756 s base he ha hf
  case p760 =>
    have hf : s.program.find? (read_pc s) = some 0x52800208#32 := by
      rw [hp]; exact hc (760, 0x52800208#32) (by decide)
    simpa only [Op.effect] using word_p760 s base he ha hf
  case p764 =>
    have hf : s.program.find? (read_pc s) = some 0x52800034#32 := by
      rw [hp]; exact hc (764, 0x52800034#32) (by decide)
    simpa only [Op.effect] using word_p764 s base he ha hf
  case p768 =>
    have hf : s.program.find? (read_pc s) = some 0x5280010a#32 := by
      rw [hp]; exact hc (768, 0x5280010a#32) (by decide)
    simpa only [Op.effect] using word_p768 s base he ha hf
  case p772 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (772, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p776 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (776, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p780 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (780, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p784 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (784, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p788 =>
    have hf : s.program.find? (read_pc s) = some 0x9100e129#32 := by
      rw [hp]; exact hc (788, 0x9100e129#32) (by decide)
    simpa only [Op.effect] using word_p444 s base he ha hf
  case p792 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (792, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p796 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (796, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p800 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (800, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p804 =>
    have hf : s.program.find? (read_pc s) = some 0xf900052a#32 := by
      rw [hp]; exact hc (804, 0xf900052a#32) (by decide)
    simpa only [Op.effect] using word_p460 s base he ha hf
  case p808 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (808, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p812 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (812, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p816 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (816, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p820 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (820, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p824 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (824, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p828 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (828, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p832 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (832, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p836 =>
    have hf : s.program.find? (read_pc s) = some 0x9100a129#32 := by
      rw [hp]; exact hc (836, 0x9100a129#32) (by decide)
    simpa only [Op.effect] using word_p836 s base he ha hf
  case p840 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (840, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p844 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (844, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p848 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (848, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p852 =>
    have hf : s.program.find? (read_pc s) = some 0xf900052a#32 := by
      rw [hp]; exact hc (852, 0xf900052a#32) (by decide)
    simpa only [Op.effect] using word_p460 s base he ha hf
  case p856 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (856, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p860 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (860, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p864 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (864, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p868 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (868, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p872 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (872, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p876 =>
    have hf : s.program.find? (read_pc s) = some 0xf90007ea#32 := by
      rw [hp]; exact hc (876, 0xf90007ea#32) (by decide)
    simpa only [Op.effect] using word_p88 s base he ha hf
  case p880 =>
    have hf : s.program.find? (read_pc s) = some 0x91000009#32 := by
      rw [hp]; exact hc (880, 0x91000009#32) (by decide)
    simpa only [Op.effect] using word_p220 s base he ha hf
  case p884 =>
    have hf : s.program.find? (read_pc s) = some 0x91006129#32 := by
      rw [hp]; exact hc (884, 0x91006129#32) (by decide)
    simpa only [Op.effect] using word_p884 s base he ha hf
  case p888 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (888, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p892 =>
    have hf : s.program.find? (read_pc s) = some 0xf900012a#32 := by
      rw [hp]; exact hc (892, 0xf900012a#32) (by decide)
    simpa only [Op.effect] using word_p232 s base he ha hf
  case p896 =>
    have hf : s.program.find? (read_pc s) = some 0xd280000a#32 := by
      rw [hp]; exact hc (896, 0xd280000a#32) (by decide)
    simpa only [Op.effect] using word_p228 s base he ha hf
  case p900 =>
    have hf : s.program.find? (read_pc s) = some 0xf900052a#32 := by
      rw [hp]; exact hc (900, 0xf900052a#32) (by decide)
    simpa only [Op.effect] using word_p460 s base he ha hf
  case p904 =>
    have hf : s.program.find? (read_pc s) = some 0xf94007ea#32 := by
      rw [hp]; exact hc (904, 0xf94007ea#32) (by decide)
    simpa only [Op.effect] using word_p120 s base he ha hf
  case p908 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (908, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p912 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (912, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p916 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (916, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p920 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (920, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p924 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0a03e9#32 := by
      rw [hp]; exact hc (924, 0xaa0a03e9#32) (by decide)
    simpa only [Op.effect] using word_p924 s base he ha hf
  case p928 =>
    have hf : s.program.find? (read_pc s) = some 0x8b090009#32 := by
      rw [hp]; exact hc (928, 0x8b090009#32) (by decide)
    simpa only [Op.effect] using word_p928 s base he ha hf
  case p932 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000134#32 := by
      rw [hp]; exact hc (932, 0xf9000134#32) (by decide)
    simpa only [Op.effect] using word_p932 s base he ha hf
  case p936 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (936, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p940 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (940, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p944 =>
    have hf : s.program.find? (read_pc s) = some 0xd10043ff#32 := by
      rw [hp]; exact hc (944, 0xd10043ff#32) (by decide)
    simpa only [Op.effect] using word_p32 s base he ha hf
  case p948 =>
    have hf : s.program.find? (read_pc s) = some 0xf90003e9#32 := by
      rw [hp]; exact hc (948, 0xf90003e9#32) (by decide)
    simpa only [Op.effect] using word_p36 s base he ha hf
  case p952 =>
    have hf : s.program.find? (read_pc s) = some 0xaa0803e9#32 := by
      rw [hp]; exact hc (952, 0xaa0803e9#32) (by decide)
    simpa only [Op.effect] using word_p952 s base he ha hf
  case p956 =>
    have hf : s.program.find? (read_pc s) = some 0x8b090009#32 := by
      rw [hp]; exact hc (956, 0x8b090009#32) (by decide)
    simpa only [Op.effect] using word_p928 s base he ha hf
  case p960 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000133#32 := by
      rw [hp]; exact hc (960, 0xf9000133#32) (by decide)
    simpa only [Op.effect] using word_p960 s base he ha hf
  case p964 =>
    have hf : s.program.find? (read_pc s) = some 0xf94003e9#32 := by
      rw [hp]; exact hc (964, 0xf94003e9#32) (by decide)
    simpa only [Op.effect] using word_p52 s base he ha hf
  case p968 =>
    have hf : s.program.find? (read_pc s) = some 0x910043ff#32 := by
      rw [hp]; exact hc (968, 0x910043ff#32) (by decide)
    simpa only [Op.effect] using word_p56 s base he ha hf
  case p972 =>
    have hf : s.program.find? (read_pc s) = some 0x52800028#32 := by
      rw [hp]; exact hc (972, 0x52800028#32) (by decide)
    simpa only [Op.effect] using word_p200 s base he ha hf
  case p976 =>
    have hf : s.program.find? (read_pc s) = some 0xb9004809#32 := by
      rw [hp]; exact hc (976, 0xb9004809#32) (by decide)
    simpa only [Op.effect] using word_p252 s base he ha hf
  case p980 =>
    have hf : s.program.find? (read_pc s) = some 0xa9454ff4#32 := by
      rw [hp]; exact hc (980, 0xa9454ff4#32) (by decide)
    simpa only [Op.effect] using word_p980 s base he ha hf
  case p984 =>
    have hf : s.program.find? (read_pc s) = some 0xa94457f6#32 := by
      rw [hp]; exact hc (984, 0xa94457f6#32) (by decide)
    simpa only [Op.effect] using word_p984 s base he ha hf
  case p988 =>
    have hf : s.program.find? (read_pc s) = some 0xa9435ff8#32 := by
      rw [hp]; exact hc (988, 0xa9435ff8#32) (by decide)
    simpa only [Op.effect] using word_p988 s base he ha hf
  case p992 =>
    have hf : s.program.find? (read_pc s) = some 0xa94267fa#32 := by
      rw [hp]; exact hc (992, 0xa94267fa#32) (by decide)
    simpa only [Op.effect] using word_p992 s base he ha hf
  case p996 =>
    have hf : s.program.find? (read_pc s) = some 0xa9416ffc#32 := by
      rw [hp]; exact hc (996, 0xa9416ffc#32) (by decide)
    simpa only [Op.effect] using word_p996 s base he ha hf
  case p1000 =>
    have hf : s.program.find? (read_pc s) = some 0xa8c67bfd#32 := by
      rw [hp]; exact hc (1000, 0xa8c67bfd#32) (by decide)
    simpa only [Op.effect] using word_p1000 s base he ha hf
  case p1004 =>
    have hf : s.program.find? (read_pc s) = some 0xf9000008#32 := by
      rw [hp]; exact hc (1004, 0xf9000008#32) (by decide)
    simpa only [Op.effect] using word_p1004 s base he ha hf
  case p1008 =>
    have hf : s.program.find? (read_pc s) = some 0xd65f03c0#32 := by
      rw [hp]; exact hc (1008, 0xd65f03c0#32) (by decide)
    simpa only [Op.effect] using word_p1008 s base he ha hf (by simpa only [Op.row, BitVec.ofNat_eq_ofNat] using hp)

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

macro "delimited_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [block, Follows, Op.row, Op.effect, put, next,
     state_simp_rules, BitVec.add_assoc])

end SszArm.Delimited
